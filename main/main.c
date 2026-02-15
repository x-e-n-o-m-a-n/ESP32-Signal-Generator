#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <ctype.h>
#include <math.h>

#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "driver/gpio.h"
#include "driver/ledc.h"
#include "esp_log.h"
#include "esp_err.h"
#include "esp_timer.h"
#include "driver/rmt_tx.h"
#include "driver/rmt_encoder.h"
#include "nvs.h"
#include "nvs_flash.h"
#include "esp_netif.h"
#include "esp_event.h"
#include "esp_wifi.h"
#include "esp_http_server.h"

#define SLOW_PWM 5
#define FAST_PWM 6

static const char *TAG = "web_input";

static volatile uint32_t g_pulse_us = 100000; // длительность импульса по умолчанию (мкс)
static volatile uint32_t g_pause_us = 900000; // длительность паузы по умолчанию (мкс)
static volatile int g_pulses_per_rev = 1; // импульсов на оборот по умолчанию
static volatile double g_rpm = 60.0; // обороты в минуту по умолчанию
static volatile int g_pulse_percent = 10; // процент ширины импульса (1..99)
static volatile bool g_output_enabled = false;
static volatile bool g_use_rmt = false;
static TaskHandle_t g_rmt_task = NULL;
static rmt_channel_handle_t g_rmt_channel = NULL;
static rmt_encoder_handle_t g_rmt_copy_encoder = NULL;
static SemaphoreHandle_t g_param_lock = NULL;

typedef struct {
    int pulses_per_rev;
    uint32_t pulse_us;
    uint32_t pause_us;
    int pulse_pct;
    double rpm;
    bool enabled;
} rmt_params_t;

typedef struct {
    rmt_symbol_word_t *items;
    uint32_t cap;
    uint32_t idx;
    bool half_filled;
} rmt_symbol_builder_t;

static rmt_params_t g_params;
// (удален неиспользуемый g_cfg_sem)

// Глобальные переменные для быстрого ШИМ (LEDC)
static volatile double g_fast_freq_hz = 1000.0; // Гц
static volatile int g_fast_pulse_pct = 10; // 1..99
static volatile bool g_fast_enabled = false;
static const ledc_timer_t g_ledc_timer = LEDC_TIMER_0;
static const ledc_channel_t g_ledc_channel = LEDC_CHANNEL_0;
static const ledc_mode_t g_ledc_mode = LEDC_LOW_SPEED_MODE;

static void init_fast_pwm(void);
static void update_fast_pwm_from_globals(void);

// Настройки RMT
#define RMT_CLK_DIV 80 // тик 1 мкс (80 МГц / 80 = 1 МГц)
// Максимальная длительность сегмента RMT (в тиках) - 15 бит: 32767
#define RMT_MAX_DURATION 32767
// Ограничение безопасности для динамически выделяемых элементов
#define RMT_MAX_ITEMS_CAP 2048
// Сколько транзакций ставить в очередь для непрерывной передачи
#define RMT_TX_QUEUE_DEPTH 4
// Сколько кадров оборота держать в очереди (рекомендуется 1-2)
#define RMT_TX_KEEP_QUEUED 2
// Задержка после перенастройки частоты, чтобы избежать артефактов на выходе
#define RMT_REBUILD_DELAY_MS 5000

// Использование RMT для генерации импульсов (покрывает весь частотный диапазон)

static void init_pwm_from_globals(void);
static void update_pwm_from_globals(void);
static esp_err_t save_settings(void);
static esp_err_t load_settings(void);
static void rmt_tx_task(void *arg);
static void network_task(void *arg);
static httpd_handle_t start_webserver(void);
static void wifi_init_softap(void);
static bool compute_pulse_timing(int pulses_per_rev, double rpm, int pulse_pct, uint32_t *out_pulse_us, uint32_t *out_pause_us, uint32_t *out_total_us, double *out_freq_hz);
static bool rmt_builder_append_segment(rmt_symbol_builder_t *b, uint32_t level, uint32_t duration);
static uint32_t rmt_builder_finalize(rmt_symbol_builder_t *b);

// Настройки SoftAP
#define AP_SSID "SSID"
#define AP_PASS "PASSWORD"
#define AP_MAX_CONN 4

// Использование аппаратного ШИМ LEDC для стабильной частоты и скважности

static bool compute_pulse_timing(int pulses_per_rev, double rpm, int pulse_pct, uint32_t *out_pulse_us, uint32_t *out_pause_us, uint32_t *out_total_us, double *out_freq_hz)
{
    if (pulses_per_rev < 1) pulses_per_rev = 1;
    if (pulses_per_rev > 10) pulses_per_rev = 10;
    if (pulse_pct < 1) pulse_pct = 1;
    if (pulse_pct > 99) pulse_pct = 99;
    if (rpm <= 0.0) return false;
    if (rpm > 1000.0) rpm = 1000.0;

    double freq_hz = (rpm / 60.0) * (double)pulses_per_rev;
    if (freq_hz <= 0.0) return false;

    double period_us = 1000000.0 / freq_hz;
    uint32_t total_us = (uint32_t)llround(period_us);
    if (total_us < 2) total_us = 2;

    uint32_t pulse_us = (uint32_t)llround(period_us * ((double)pulse_pct / 100.0));
    if (pulse_us < 1) pulse_us = 1;
    if (pulse_us >= total_us) pulse_us = total_us - 1;
    uint32_t pause_us = total_us - pulse_us;

    if (out_pulse_us) *out_pulse_us = pulse_us;
    if (out_pause_us) *out_pause_us = pause_us;
    if (out_total_us) *out_total_us = total_us;
    if (out_freq_hz) *out_freq_hz = freq_hz;
    return true;
}

static bool rmt_builder_append_segment(rmt_symbol_builder_t *b, uint32_t level, uint32_t duration)
{
    while (duration > 0) {
        if (b->idx >= b->cap) {
            return false;
        }
        uint32_t seg = (duration > RMT_MAX_DURATION) ? RMT_MAX_DURATION : duration;
        duration -= seg;

        if (!b->half_filled) {
            b->items[b->idx].level0 = level ? 1 : 0;
            b->items[b->idx].duration0 = seg;
            b->items[b->idx].level1 = 0;
            b->items[b->idx].duration1 = 0;
            b->half_filled = true;
        } else {
            b->items[b->idx].level1 = level ? 1 : 0;
            b->items[b->idx].duration1 = seg;
            b->idx++;
            b->half_filled = false;
        }
    }
    return true;
}

static uint32_t rmt_builder_finalize(rmt_symbol_builder_t *b)
{
    // Если последний символ использует только duration0, оставляем duration1=0 только в конце.
    // Это предотвращает появление преждевременных маркеров остановки внутри потока символов.
    if (b->half_filled) {
        b->idx++;
        b->half_filled = false;
    }
    return b->idx;
}

static void init_pwm_from_globals(void)
{
    // Создание канала передачи (TX) с использованием нового API RMT TX
    if (!g_rmt_channel) {
        rmt_tx_channel_config_t tx_cfg = {
            .gpio_num = SLOW_PWM,
            .clk_src = RMT_CLK_SRC_DEFAULT,
            .resolution_hz = 1000000, // 1 МГц -> тик 1 мкс
            .mem_block_symbols = SOC_RMT_MEM_WORDS_PER_CHANNEL,
            .trans_queue_depth = RMT_TX_QUEUE_DEPTH,
            .intr_priority = 1,
            .flags = { .invert_out = 0, .with_dma = 1, .io_loop_back = 0, .io_od_mode = 0, .allow_pd = 0, .init_level = 0 }
        };

        esp_err_t rc = rmt_new_tx_channel(&tx_cfg, &g_rmt_channel);
        if (rc != ESP_OK) {
            ESP_LOGW(TAG, "RMT: new tx channel with DMA failed (%d), retrying without DMA", rc);
            // Повторная попытка без DMA
            tx_cfg.flags.with_dma = 0;
            tx_cfg.trans_queue_depth = 4;
            rc = rmt_new_tx_channel(&tx_cfg, &g_rmt_channel);
            if (rc != ESP_OK) {
                ESP_LOGE(TAG, "RMT: new tx channel failed (%d)", rc);
                return;
            }
        }
        // создание copy encoder для отправки сырых массивов rmt_symbol_word_t
        rmt_copy_encoder_config_t enc_cfg = {};
        if (rmt_new_copy_encoder(&enc_cfg, &g_rmt_copy_encoder) != ESP_OK) {
            ESP_LOGE(TAG, "RMT: new copy encoder failed");
            // очистка канала
            rmt_del_channel(g_rmt_channel);
            g_rmt_channel = NULL;
            return;
        }
        // включение канала
        rmt_enable(g_rmt_channel);

        // регистрация callback-функции завершения передачи для пополнения очереди
        rmt_tx_event_callbacks_t tx_cbs = {
            .on_trans_done = NULL, // будет установлено позже, когда задача будет создана
        };
        // регистрация заглушки; реальный callback зарегистрируем после создания задачи
        rmt_tx_register_event_callbacks(g_rmt_channel, &tx_cbs, NULL);
    }

    // запуск задачи RMT TX, если она еще не запущена
    if (!g_rmt_task) {
        xTaskCreatePinnedToCore(rmt_tx_task, "rmt_tx", 4096, NULL, 5, &g_rmt_task, 1);
    }
    g_use_rmt = true;
}

static void update_pwm_from_globals(void)
{
    // Атомарное обновление снимка параметров и уведомление задачи RMT
    if (!g_param_lock) {
        // запасной вариант: гарантируем инициализацию
        init_pwm_from_globals();
        if (g_rmt_task) xTaskNotify(g_rmt_task, 0x80000000, eSetBits);
        return;
    }

    if (xSemaphoreTake(g_param_lock, pdMS_TO_TICKS(100)) == pdTRUE) {
        g_params.pulses_per_rev = g_pulses_per_rev;
        g_params.pulse_us = g_pulse_us;
        g_params.pause_us = g_pause_us;
        g_params.pulse_pct = g_pulse_percent;
        g_params.rpm = g_rpm;
        g_params.enabled = g_output_enabled;
        xSemaphoreGive(g_param_lock);
    }

    // убеждаемся, что RMT инициализирован, и уведомляем
    if (!g_rmt_task) init_pwm_from_globals();
    if (g_rmt_task) {
        // Уведомляем задачу RMT об изменении конфигурации, используя специальный бит (старший бит)
        xTaskNotify(g_rmt_task, 0x80000000, eSetBits);
    }

    // Обновляем быстрый (LEDC) ШИМ из глобальных переменных
    update_fast_pwm_from_globals();
}

// Инициализация таймера/канала LEDC для быстрого ШИМ
static void init_fast_pwm(void)
{
    // настройка таймера с разрешением и частотой по умолчанию
    ledc_timer_config_t tcfg = {
        .speed_mode = g_ledc_mode,
        .timer_num = g_ledc_timer,
        .duty_resolution = LEDC_TIMER_9_BIT,
        .freq_hz = (int)g_fast_freq_hz,
        .clk_cfg = LEDC_AUTO_CLK,
    };
    ledc_timer_config(&tcfg);

    ledc_channel_config_t chcfg = {
        .gpio_num = FAST_PWM,
        .speed_mode = g_ledc_mode,
        .channel = g_ledc_channel,
        .intr_type = LEDC_INTR_DISABLE,
        .timer_sel = g_ledc_timer,
        .duty = 0,
        .hpoint = 0,
    };
    ledc_channel_config(&chcfg);
}

// Обновление параметров LEDC (частота, скважность) из глобальных переменных (потокобезопасный снимок)
static void update_fast_pwm_from_globals(void)
{
    double freq = g_fast_freq_hz;
    int pct = g_fast_pulse_pct;
    bool enabled = g_fast_enabled;

    // создание снимка под блокировкой, если доступна
    if (g_param_lock && xSemaphoreTake(g_param_lock, pdMS_TO_TICKS(50)) == pdTRUE) {
        freq = g_fast_freq_hz;
        pct = g_fast_pulse_pct;
        enabled = g_fast_enabled;
        xSemaphoreGive(g_param_lock);
    }

    // ограничение значений
    if (freq < 100.0) freq = 100.0;
    if (freq > 100000.0) freq = 100000.0;
    if (pct < 1) pct = 1;
    if (pct > 99) pct = 99;

    // перенастройка таймера на запрошенную частоту (сохраняя 10-битное разрешение)
    ledc_timer_config_t tcfg = {
        .speed_mode = g_ledc_mode,
        .timer_num = g_ledc_timer,
        .duty_resolution = LEDC_TIMER_9_BIT,
        .freq_hz = (int)freq,
        .clk_cfg = LEDC_AUTO_CLK,
    };
    ledc_timer_config(&tcfg);

    uint32_t max_duty = (1 << LEDC_TIMER_9_BIT) - 1;
    uint32_t duty = (uint32_t)(((uint32_t)max_duty * (uint32_t)pct) / 100U);

    if (!enabled) {
        duty = 0;
    }

    ledc_set_duty(g_ledc_mode, g_ledc_channel, duty);
    ledc_update_duty(g_ledc_mode, g_ledc_channel);
}

// Вспомогательная функция URL-декодирования (in-place). Возвращает указатель на dest (тот же, что и input).
static void url_decode(char *src)
{
    char *dst = src;
    while (*src) {
        if (*src == '+') {
            *dst++ = ' ';
            src++;
        } else if (*src == '%' && isxdigit((unsigned char)src[1]) && isxdigit((unsigned char)src[2])) {
            char hex[3] = { src[1], src[2], '\0' };
            *dst++ = (char) strtol(hex, NULL, 16);
            src += 3;
        } else {
            *dst++ = *src++;
        }
    }
    *dst = '\0';
}

// Разбор тела формы с "pulses=<int>&rpm=<double>" и обновление глобальных переменных
static void handle_frequency_body(char *body)
{
    if (!body) return;
    // Сначала URL-декодируем все тело
    url_decode(body);

    int pulses_per_rev = 1; // по умолчанию
    double rpm = 0.0;
    int pulse_pct = 10; // процент по умолчанию
    bool enabled = true;
    // настройки быстрого ШИМ по умолчанию
    double fast_freq = g_fast_freq_hz;
    int fast_pct = g_fast_pulse_pct;
    bool fast_enabled = g_fast_enabled;

    // Разделение пар ключ=значение, разделенных '&'
    char *pair = strtok(body, "&");
    while (pair) {
        char *eq = strchr(pair, '=');
        if (eq) {
            *eq = '\0';
            char *key = pair;
            char *val = eq + 1;
            if (strcmp(key, "pulses") == 0) {
                pulses_per_rev = atoi(val);
            } else if (strcmp(key, "rpm") == 0) {
                rpm = atof(val);
            } else if (strcmp(key, "pulse_pct") == 0) {
                pulse_pct = atoi(val);
            } else if (strcmp(key, "fast_freq") == 0) {
                fast_freq = atof(val);
            } else if (strcmp(key, "fast_pct") == 0) {
                fast_pct = atoi(val);
            } else if (strcmp(key, "fast_enabled") == 0) {
                fast_enabled = (atoi(val) != 0);
            } else if (strcmp(key, "enabled") == 0) {
                enabled = (atoi(val) != 0);
            }
        }
        pair = strtok(NULL, "&");
    }

    // Применение ограничений
    if (pulses_per_rev <= 0) pulses_per_rev = 1;
    if (pulses_per_rev > 10) pulses_per_rev = 10; // макс. импульсов
    if (rpm <= 0.0) {
        ESP_LOGW(TAG, "Invalid RPM: %.3f", rpm);
        return;
    }
    if (rpm > 1000.0) rpm = 1000.0; // макс. об/мин

    uint32_t pulse = 0;
    uint32_t pause = 0;
    uint32_t total = 0;
    double freq = 0.0;
    if (!compute_pulse_timing(pulses_per_rev, rpm, pulse_pct, &pulse, &pause, &total, &freq)) {
        ESP_LOGW(TAG, "Computed invalid timing from rpm=%.3f pulses=%d pct=%d", rpm, pulses_per_rev, pulse_pct);
        return;
    }

    g_pulse_us = pulse;
    g_pause_us = pause;
    g_pulses_per_rev = pulses_per_rev;
    g_rpm = rpm;
    g_pulse_percent = pulse_pct;
    g_output_enabled = enabled;

    // применение параметров быстрого ШИМ
    g_fast_freq_hz = fast_freq;
    g_fast_pulse_pct = fast_pct;
    g_fast_enabled = fast_enabled;

    // Обновление аппаратного ШИМ на новую частоту/скважность
    update_pwm_from_globals();

    // Сохранение новых настроек
    if (save_settings() != ESP_OK) {
        ESP_LOGW(TAG, "Failed to save settings to NVS");
    }

    ESP_LOGI(TAG, "Set rpm=%.3f, pulses_per_rev=%d -> freq=%.3f Hz, period=%u us, pulse=%u us, pause=%u us",
             rpm, pulses_per_rev, freq, total, pulse, pause);
}

// Статический HTML для экономии RAM (без больших malloc) и Flash (без кода форматирования snprintf)
static const char INDEX_HTML[] = 
    "<!doctype html><html lang=\"ru\"><head><meta charset=\"utf-8\">"
    "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1,viewport-fit=cover\">"
    "<title>ESP32 PWM</title>"
    "<style>html,body{height:100%;margin:0;font-family:system-ui,-apple-system,Segoe UI,Roboto,'Helvetica Neue',Arial;background:#0f1724;color:#e6eef8;-webkit-font-smoothing:antialiased}"
    ".wrap{display:flex;flex-direction:column;min-height:100vh;padding:18px;box-sizing:border-box;gap:12px}"
    ".card{background:linear-gradient(180deg,#111827, #0b1220);border-radius:14px;padding:14px;box-shadow:0 6px 20px rgba(2,6,23,0.6);border:1px solid rgba(255,255,255,0.03)}"
    ".section-head{display:flex;align-items:center;gap:10px;margin-bottom:10px;padding-bottom:5px;border-bottom:1px solid rgba(255,255,255,0.05)}"
    ".section-title{font-size:18px;font-weight:700;color:#fff}"
    ".control{display:flex;flex-direction:column;gap:8px;padding:6px;margin-bottom:8px}label{font-size:13px;color:#9fb0d1}"
    ".big-row{display:flex;gap:10px;align-items:center}input[type=range]{flex:1;height:36px}input[type=number]{width:90px;padding:8px;border-radius:8px;border:1px solid rgba(255,255,255,0.06);background:transparent;color:inherit;font-size:16px;text-align:center}"
    "button.primary{width:100%;padding:14px;border-radius:12px;border:none;background:#06b6d4;color:#042027;font-weight:700;font-size:16px;cursor:pointer;margin-top:8px}"
    "button.ghost{background:transparent;border:1px solid rgba(255,255,255,0.06);color:#cfe8f3;padding:10px;border-radius:10px;width:100%;cursor:pointer;margin-top:10px}"
    ".presets{display:flex;gap:8px;flex-wrap:wrap}button.preset{flex:1;padding:10px;border-radius:10px;background:rgba(255,255,255,0.03);border:none;color:#d8eef8;cursor:pointer}"
    ".status{display:flex;justify-content:space-between;gap:8px;padding:8px;background:rgba(255,255,255,0.02);border-radius:8px;font-size:14px;margin-bottom:8px}"
    ".fast-info{background:rgba(6,182,212,0.1);color:#22d3ee;padding:10px;border-radius:8px;text-align:center;font-weight:bold;margin-bottom:8px}"
    "footer{font-size:12px;color:#8fb0cf;text-align:center;margin-top:20px}" 
    "@media(min-width:520px){.wrap{padding:28px}.card{max-width:520px;margin:0 auto}}"
    "</style></head><body><div class=wrap><div class=card>"
    "<div class=section-head><input type=checkbox id=enabled_cb style=\"width:24px;height:24px\"><div class=section-title>Медленный ШИМ</div></div>"
    "<div id=controls style=\"display:none\">"
    "<div class=control><label for=pulses_range>Импульсов на оборот</label>"
    "<div class=big-row><input id=pulses_range type=range min=1 max=10 step=1 value=\"1\"><input id=pulses_num type=number min=1 max=10 value=\"1\"></div>"
    "<div class=presets><button type=button class=preset onclick=pickP(1)>1</button><button type=button class=preset onclick=pickP(2)>2</button><button type=button class=preset onclick=pickP(4)>4</button><button type=button class=preset onclick=pickP(6)>6</button><button type=button class=preset onclick=pickP(8)>8</button><button type=button class=preset onclick=pickP(10)>10</button></div></div>"
    "<div class=control><label for=rpm_range>Скорость, об/мин</label>"
    "<div class=big-row><input id=rpm_range type=range min=1 max=1000 step=1 value=\"60\"><input id=rpm_num type=number min=1 max=1000 value=\"60\"></div>"
    "<div class=presets><button type=button class=preset onclick=pickR(60)>60</button><button type=button class=preset onclick=pickR(120)>120</button><button type=button class=preset onclick=pickR(300)>300</button><button type=button class=preset onclick=pickR(600)>600</button><button type=button class=preset onclick=pickR(900)>900</button></div></div>"
    "<div class=control><label for=pulse_pct_range>Длительность импульса (%)</label>"
    "<div class=big-row><input id=pulse_pct_range type=range min=1 max=99 step=1 value=\"10\"><input id=pulse_pct_num type=number min=1 max=99 value=\"10\"></div>"
    "<div class=presets><button type=button class=preset onclick=pickD(5)>5%</button><button type=button class=preset onclick=pickD(10)>10%</button><button type=button class=preset onclick=pickD(20)>20%</button><button type=button class=preset onclick=pickD(50)>50%</button></div></div>"
    "<div class=status><div>Имп: <strong id=status_p>--</strong></div><div>RPM: <strong id=status_r>--</strong></div><div>Hz: <strong id=status_f>--</strong></div><div>%: <strong id=status_d>--</strong></div></div>"
    "<button id=apply_btn_slow class=primary>Применить (Медленный)</button>"
    "</div>"
    "<div style=\"height:20px\"></div>"
    "<div class=section-head><input type=checkbox id=enabled_fast_cb style=\"width:24px;height:24px\"><div class=section-title>Быстрый ШИМ</div></div>"
    "<div id=fast_controls style=\"display:none\">"
    "<div class=control><label for=freq_range>Частота (Гц)</label>"
    "<div class=big-row><input id=freq_range type=range min=100 max=100000 step=100 value=\"1000\"><input id=freq_num type=number min=100 max=100000 step=100 value=\"1000\"></div>"
    "</div>"
    "<div class=control><label for=pulse_pct_range_fast>Длительность импульса (%)</label>"
    "<div class=big-row><input id=pulse_pct_range_fast type=range min=1 max=99 step=1 value=\"10\"><input id=pulse_pct_num_fast type=number min=1 max=99 value=\"10\"></div>"
    "<div class=presets><button type=button class=preset onclick=pickDF(5)>5%</button><button type=button class=preset onclick=pickDF(10)>10%</button><button type=button class=preset onclick=pickDF(20)>20%</button><button type=button class=preset onclick=pickDF(50)>50%</button></div></div>"
    "<div class=fast-info>Текущие: <span id=fast_status_txt>--</span></div>"
    "<button id=apply_btn_fast class=primary>Применить (Быстрый)</button>"
    "</div>"
    "<div style=height:10px></div><button id=reset_btn class=ghost>Сбросить интерфейс</button></div>"
    "<footer>Подключитесь к Wi‑Fi точке доступа ESP32 и откройте http://192.168.4.1</footer></div></div>"
    "<script>"
    "const pulses_range=document.getElementById('pulses_range'),pulses_num=document.getElementById('pulses_num');"
    "const rpm_range=document.getElementById('rpm_range'),rpm_num=document.getElementById('rpm_num');"
    "const pulse_pct_range=document.getElementById('pulse_pct_range'),pulse_pct_num=document.getElementById('pulse_pct_num');"
    "const statusP=document.getElementById('status_p'),statusR=document.getElementById('status_r'),statusF=document.getElementById('status_f'),statusD=document.getElementById('status_d');"
    "const applyBtnSlow=document.getElementById('apply_btn_slow'),applyBtnFast=document.getElementById('apply_btn_fast'),resetBtn=document.getElementById('reset_btn'),enabledCb=document.getElementById('enabled_cb'),enabledFastCb=document.getElementById('enabled_fast_cb');"
    "const fastStatusTxt=document.getElementById('fast_status_txt');"
    "const freq_range=document.getElementById('freq_range'),freq_num=document.getElementById('freq_num'),pulse_pct_range_fast=document.getElementById('pulse_pct_range_fast'),pulse_pct_num_fast=document.getElementById('pulse_pct_num_fast');"
    "pulses_range.oninput=e=>pulses_num.value=e.target.value; pulses_num.oninput=e=>pulses_range.value=e.target.value; rpm_range.oninput=e=>rpm_num.value=e.target.value; rpm_num.oninput=e=>rpm_range.value=e.target.value; pulse_pct_range.oninput=e=>pulse_pct_num.value=e.target.value; pulse_pct_num.oninput=e=>pulse_pct_range.value=e.target.value; freq_range.oninput=e=>freq_num.value=e.target.value; freq_num.oninput=e=>freq_range.value=e.target.value; pulse_pct_range_fast.oninput=e=>pulse_pct_num_fast.value=e.target.value; pulse_pct_num_fast.oninput=e=>pulse_pct_range_fast.value=e.target.value;"
    "function pickP(v){pulses_range.value=v; pulses_num.value=v;} function pickR(v){rpm_range.value=v; rpm_num.value=v;} function pickD(v){pulse_pct_range.value=v; pulse_pct_num.value=v;} function pickDF(v){pulse_pct_range_fast.value=v; pulse_pct_num_fast.value=v;} function resetDefaults(){pickP(1); pickR(60); pickD(10); pickDF(10); freq_range.value=1000; freq_num.value=1000;}"
    "async function fetchStatus(){try{let r=await fetch('/status',{cache:'no-store'}); if(r.ok){let j=await r.json(); statusP.textContent=j.pulses; statusR.textContent=j.rpm; statusF.textContent=j.freq.toFixed(3); statusD.textContent=(j.pulse_pct!==undefined?j.pulse_pct:'--'); if(document.activeElement!==enabledCb){ enabledCb.checked=j.enabled; updateControlsVisibility(); } if(document.activeElement!==enabledFastCb){ enabledFastCb.checked=j.fast_enabled; updateControlsVisibility(); } fastStatusTxt.textContent=(j.fast_freq!==undefined?j.fast_freq:'--')+' Hz, '+(j.fast_pct!==undefined?j.fast_pct:'--')+'%'; } }catch(e){/*silent*/}}"
    "function updateControlsVisibility(){const ctr=document.getElementById('controls');const fctr=document.getElementById('fast_controls'); if(!ctr||!fctr) return; if(enabledCb.checked){ctr.style.display='';}else{ctr.style.display='none';} if(enabledFastCb.checked){fctr.style.display='';}else{fctr.style.display='none';}}"
    "let poll = setInterval(fetchStatus,1500); document.addEventListener('visibilitychange',()=>{ if(document.hidden) clearInterval(poll); else {fetchStatus(); poll=setInterval(fetchStatus,1500);} }); document.addEventListener('DOMContentLoaded',fetchStatus);"
    "async function applySettings(e){const btn=e.target; const oldTxt=btn.textContent; btn.disabled=true; btn.textContent='Применение...'; const body = new URLSearchParams(); body.append('pulses',pulses_num.value); body.append('rpm',rpm_num.value); body.append('pulse_pct',pulse_pct_num.value); body.append('enabled',enabledCb.checked?1:0); body.append('fast_freq',freq_num.value); body.append('fast_pct',pulse_pct_num_fast.value); body.append('fast_enabled',enabledFastCb.checked?1:0); try{let r=await fetch('/submit',{method:'POST',body:body,headers:{'Content-Type':'application/x-www-form-urlencoded'}}); let j=await r.json(); if(j.status==='ok'){btn.textContent='Применено'; fetchStatus(); setTimeout(()=>btn.textContent=oldTxt,900);} else {btn.textContent='Ошибка'; setTimeout(()=>btn.textContent=oldTxt,1500);} }catch(err){btn.textContent='Ошибка'; setTimeout(()=>btn.textContent=oldTxt,1500);} finally{btn.disabled=false;} }"
    "applyBtnSlow.addEventListener('click',applySettings); applyBtnFast.addEventListener('click',applySettings); resetBtn.addEventListener('click',resetDefaults); enabledCb.addEventListener('change',()=>{ updateControlsVisibility(); applyBtnSlow.click(); }); enabledFastCb.addEventListener('change',()=>{ updateControlsVisibility(); applyBtnFast.click(); });"
    "</script></body></html>";

// Обработчик HTTP GET - отдает простую форму
static esp_err_t root_get_handler(httpd_req_t *req)
{
    httpd_resp_set_type(req, "text/html; charset=utf-8");
    httpd_resp_send(req, INDEX_HTML, HTTPD_RESP_USE_STRLEN);
    return ESP_OK;
}

// Обработчик HTTP POST - принимает данные формы
static esp_err_t submit_post_handler(httpd_req_t *req)
{
    int total_len = req->content_len;
    if (total_len <= 0 || total_len >= 512) {
        const char *err = "{\"status\":\"error\",\"msg\":\"empty body\"}";
        httpd_resp_set_type(req, "application/json");
        httpd_resp_send(req, err, HTTPD_RESP_USE_STRLEN);
        return ESP_FAIL;
    }

    char buf[512];

    int ret = 0, recv_len = 0;
    while (recv_len < total_len) {
        ret = httpd_req_recv(req, buf + recv_len, total_len - recv_len);
        if (ret <= 0) {
            const char *err = "{\"status\":\"error\",\"msg\":\"recv failed\"}";
            httpd_resp_set_type(req, "application/json");
            httpd_resp_send(req, err, HTTPD_RESP_USE_STRLEN);
            return ESP_FAIL;
        }
        recv_len += ret;
    }
    buf[recv_len] = '\0';

    // обработка параметров
    handle_frequency_body(buf);

    // Формирование JSON-ответа с текущими настройками
    double freq = (g_rpm / 60.0) * (double)g_pulses_per_rev;
    char json[256];
    int n = snprintf(json, sizeof(json), "{\"status\":\"ok\",\"pulses\":%d,\"rpm\":%.1f,\"freq\":%.3f,\"pulse_pct\":%d,\"enabled\":%d,\"fast_freq\":%.1f,\"fast_pct\":%d,\"fast_enabled\":%d}",
                     g_pulses_per_rev, g_rpm, freq, g_pulse_percent, g_output_enabled, g_fast_freq_hz, g_fast_pulse_pct, g_fast_enabled);

    httpd_resp_set_type(req, "application/json");
    httpd_resp_send(req, json, n);

    return ESP_OK;
}

// GET /status -> возвращает текущие настройки в формате JSON
static esp_err_t status_get_handler(httpd_req_t *req)
{
    char json[192];
    double freq = (g_rpm / 60.0) * (double)g_pulses_per_rev;
    int n = snprintf(json, sizeof(json), "{\"pulses\":%d,\"rpm\":%.1f,\"freq\":%.3f,\"pulse_pct\":%d,\"enabled\":%d,\"fast_freq\":%.1f,\"fast_pct\":%d,\"fast_enabled\":%d}",
                     g_pulses_per_rev, g_rpm, freq, g_pulse_percent, g_output_enabled, g_fast_freq_hz, g_fast_pulse_pct, g_fast_enabled);
    httpd_resp_set_type(req, "application/json");
    httpd_resp_send(req, json, n);
    return ESP_OK;
}

// Сохранение настроек в NVS
static esp_err_t save_settings(void)
{
    // Запись во Flash отключена по запросу пользователя — не сохраняем в NVS.
    return ESP_OK;
}

// Задача передачи RMT: непрерывно отправляет последовательности импульсов, пока g_use_rmt = true
// Callback завершения передачи RMT — уведомляет задачу передачи о необходимости пополнить очередь
static bool IRAM_ATTR rmt_tx_done_cb(rmt_channel_handle_t channel, const rmt_tx_done_event_data_t *edata, void *user_ctx)
{
    BaseType_t high_task_wakeup = pdFALSE;
    if (g_rmt_task) vTaskNotifyGiveFromISR(g_rmt_task, &high_task_wakeup);
    return high_task_wakeup == pdTRUE;
}

static void rmt_tx_task(void *arg)
{
    // RMT уже настроен/установлен в init_pwm_from_globals
    while (1) {
        if (!g_use_rmt) {
            vTaskDelay(pdMS_TO_TICKS(100));
            continue;
        }

        // Проверка статуса включения из снимка или глобальной переменной
        bool enabled_local = true;
        if (g_param_lock && xSemaphoreTake(g_param_lock, pdMS_TO_TICKS(50)) == pdTRUE) {
            enabled_local = g_params.enabled;
            xSemaphoreGive(g_param_lock);
        } else {
            enabled_local = g_output_enabled;
        }

        if (!enabled_local) {
            // Если отключено, убеждаемся, что канал остановлен и GPIO в низком уровне
            if (g_rmt_channel) {
                rmt_tx_wait_all_done(g_rmt_channel, pdMS_TO_TICKS(50));
                rmt_disable(g_rmt_channel);
                rmt_del_channel(g_rmt_channel);
                g_rmt_channel = NULL;
                if (g_rmt_copy_encoder) {
                    rmt_del_encoder(g_rmt_copy_encoder);
                    g_rmt_copy_encoder = NULL;
                }
                gpio_set_level(SLOW_PWM, 0);
                gpio_set_direction(SLOW_PWM, GPIO_MODE_OUTPUT);
            }
            // Ожидание уведомления об изменении конфигурации
            uint32_t notif_val = 0;
            xTaskNotifyWait(0, 0xFFFFFFFF, &notif_val, pdMS_TO_TICKS(500));
            continue;
        }

        // Убеждаемся, что канал существует (на случай, если он был удален при перенастройке)
        if (!g_rmt_channel) {
            init_pwm_from_globals();
            if (!g_rmt_channel) {
                vTaskDelay(pdMS_TO_TICKS(100));
                continue;
            }
        }

        // Канал может быть отключен после обновления конфигурации; убеждаемся, что TX включен.
        esp_err_t en_err = rmt_enable(g_rmt_channel);
        if (en_err != ESP_OK && en_err != ESP_ERR_INVALID_STATE) {
            ESP_LOGE(TAG, "RMT: enable failed (%d)", en_err);
            vTaskDelay(pdMS_TO_TICKS(100));
            continue;
        }

        // Атомарное копирование параметров в локальные переменные
        int pulses;
        uint32_t pulse_us;
        uint32_t pause_us;

        if (g_param_lock && xSemaphoreTake(g_param_lock, pdMS_TO_TICKS(50)) == pdTRUE) {
            pulses = g_params.pulses_per_rev;
            pulse_us = g_params.pulse_us;
            pause_us = g_params.pause_us;
            xSemaphoreGive(g_param_lock);
        } else {
            pulses = g_pulses_per_rev;
            if (pulses < 1) pulses = 1;
            pulse_us = g_pulse_us;
            pause_us = g_pause_us;
            (void)g_pulse_percent;
            (void)g_rpm;
        }

        // вычисление количества фрагментов для импульса (каждый фрагмент <= RMT_MAX_DURATION тиков)
        uint32_t chunks_per_pulse = (pulse_us + RMT_MAX_DURATION - 1) / RMT_MAX_DURATION;
        if (chunks_per_pulse == 0) chunks_per_pulse = 1;

        // общее количество сегментов на один оборот (высокие + низкие фрагменты на импульс)
        // каждый символ RMT содержит до двух сегментов (duration0 + duration1)
        uint32_t chunks_per_pause = (pause_us + RMT_MAX_DURATION - 1) / RMT_MAX_DURATION;
        if (chunks_per_pause == 0) chunks_per_pause = 1;

        uint32_t total_segments = (uint32_t)pulses * (chunks_per_pulse + chunks_per_pause);
        uint32_t total_items = (total_segments + 1) / 2;
        if (total_items > RMT_MAX_ITEMS_CAP) {
            ESP_LOGW(TAG, "RMT: requested %u items exceeds cap %u, clamping", total_items, RMT_MAX_ITEMS_CAP);
            total_items = RMT_MAX_ITEMS_CAP;
        }

        size_t alloc_size = total_items * sizeof(rmt_symbol_word_t);
        rmt_symbol_word_t *items = (rmt_symbol_word_t *)malloc(alloc_size);
        if (!items) {
            ESP_LOGE(TAG, "RMT: malloc failed for %u items", (unsigned)total_items);
            vTaskDelay(pdMS_TO_TICKS(500));
            continue;
        }

        // Построение потока символов полного оборота (высокий+низкий для каждого импульса).
        // Важно: не вставлять duration1=0 внутрь потока, иначе RMT
        // воспримет это как маркер остановки и преждевременно обрежет сигнал.
        rmt_symbol_builder_t builder = {
            .items = items,
            .cap = total_items,
            .idx = 0,
            .half_filled = false,
        };
        bool truncated = false;
        for (int p = 0; p < pulses; ++p) {
            if (!rmt_builder_append_segment(&builder, 1, pulse_us) ||
                !rmt_builder_append_segment(&builder, 0, pause_us)) {
                truncated = true;
                break;
            }
        }
        uint32_t idx = rmt_builder_finalize(&builder);
        if (truncated) {
            ESP_LOGW(TAG, "RMT: symbol buffer truncated (cap=%u)", (unsigned)total_items);
        }

        if (idx == 0) {
            free(items);
            vTaskDelay(pdMS_TO_TICKS(100));
            continue;
        }

        // Использование неблокирующей очереди передач и поддержание небольшого окна пополнения.
        rmt_transmit_config_t transmit_cfg_nonblocking = {
            .loop_count = 0,
            .flags = { .eot_level = 0, .queue_nonblocking = 0 }
        };

        // Регистрация callback-функции завершения передачи для уведомления об окончании транзакции
        rmt_tx_event_callbacks_t tx_cbs = {
            .on_trans_done = rmt_tx_done_cb,
        };
        rmt_tx_register_event_callbacks(g_rmt_channel, &tx_cbs, NULL);

        int queued = 0;
        esp_err_t terr = ESP_OK;
        int initial_queue = RMT_TX_KEEP_QUEUED;
        if (initial_queue > RMT_TX_QUEUE_DEPTH) initial_queue = RMT_TX_QUEUE_DEPTH;
        for (int q = 0; q < initial_queue; ++q) {
            terr = rmt_transmit(g_rmt_channel, g_rmt_copy_encoder, items, idx * sizeof(rmt_symbol_word_t), &transmit_cfg_nonblocking);
            if (terr != ESP_OK) {
                ESP_LOGW(TAG, "RMT: initial transmit queue failed at slot %d (%d)", q, terr);
                break;
            }
            queued++;
        }
        if (queued == 0) {
            free(items);
            vTaskDelay(pdMS_TO_TICKS(100));
            continue;
        }

        // Цикл пополнения: ожидание уведомлений от callback-функции завершения или бита изменения конфигурации
        bool reconfigure_requested = false;
        while (1) {
            uint32_t notif_val = 0;
            // Ожидание либо завершения передачи (notify give увеличивает счетчик), либо обновления конфигурации (установлен старший бит)
            xTaskNotifyWait(0, 0xFFFFFFFF, &notif_val, portMAX_DELAY);

            // Если установлен бит изменения конфигурации, прерываем для пересборки с новыми параметрами
            if (notif_val & 0x80000000) {
                reconfigure_requested = true;
                break;
            }

            // младшие биты содержат количество завершенных транзакций
            uint32_t completed = notif_val & 0x7FFFFFFF;
            for (uint32_t c = 0; c < completed; ++c) {
                // попытка поставить в очередь один новый кадр, чтобы очередь была полной
                esp_err_t terr2 = rmt_transmit(g_rmt_channel, g_rmt_copy_encoder, items, idx * sizeof(rmt_symbol_word_t), &transmit_cfg_nonblocking);
                if (terr2 != ESP_OK) {
                    // если очередь полна или ошибка, просто прерываем; следующий callback уведомит снова
                    break;
                }
                // очередь поддерживается примерно постоянной
            }
        }

        // Запрошено изменение конфигурации: попытка кратковременного сброса, затем отключение канала
        rmt_tx_wait_all_done(g_rmt_channel, pdMS_TO_TICKS(50));

        // Отключение и удаление канала для полного освобождения управления GPIO
        rmt_disable(g_rmt_channel);
        rmt_del_channel(g_rmt_channel);
        g_rmt_channel = NULL;
        if (g_rmt_copy_encoder) {
            rmt_del_encoder(g_rmt_copy_encoder);
            g_rmt_copy_encoder = NULL;
        }

        // Принудительная установка GPIO в низкий уровень для предотвращения плавающего состояния/глюков во время перенастройки
        gpio_set_level(SLOW_PWM, 0);
        gpio_set_direction(SLOW_PWM, GPIO_MODE_OUTPUT);

        free(items);

        // Даем выходной линии время успокоиться перед включением перестроенной частоты.
        if (reconfigure_requested) {
            vTaskDelay(pdMS_TO_TICKS(RMT_REBUILD_DELAY_MS));
        }

        // Повторная инициализация канала RMT (это перенастроит GPIO на функцию RMT)
        init_pwm_from_globals();
    }
}

static esp_err_t load_settings(void)
{
    // Чтение Flash отключено по запросу пользователя — используются скомпилированные/значения по умолчанию.
    // Гарантируем применение значений по умолчанию и инициализацию снимка.

    uint32_t pulse = 0;
    uint32_t pause = 0;
    if (compute_pulse_timing(g_pulses_per_rev, g_rpm, g_pulse_percent, &pulse, &pause, NULL, NULL)) {
        g_pulse_us = pulse;
        g_pause_us = pause;
    }

    // инициализация структуры снимка
    if (!g_param_lock) {
        g_param_lock = xSemaphoreCreateMutex();
    }
    if (g_param_lock) {
        if (xSemaphoreTake(g_param_lock, pdMS_TO_TICKS(50)) == pdTRUE) {
            g_params.pulses_per_rev = g_pulses_per_rev;
            g_params.pulse_us = g_pulse_us;
            g_params.pause_us = g_pause_us;
            g_params.pulse_pct = g_pulse_percent;
            g_params.rpm = g_rpm;
            g_params.enabled = g_output_enabled;
            xSemaphoreGive(g_param_lock);
        }
    }
    // инициализация оборудования быстрого ШИМ и снимка
    init_fast_pwm();
    if (g_param_lock) {
        if (xSemaphoreTake(g_param_lock, pdMS_TO_TICKS(50)) == pdTRUE) {
            // настройки быстрого ШИМ — глобальные переменные; убеждаемся, что они применены
            xSemaphoreGive(g_param_lock);
        }
    }
    return ESP_OK;
}

// Задача инициализации сети, привязанная к ядру 0
static void network_task(void *arg)
{
    // инициализация WiFi и HTTP-сервера на сетевом ядре
    wifi_init_softap();

    // загрузка настроек времени выполнения и инициализация снимка
    load_settings();

    // запуск HTTP-сервера
    start_webserver();

    ESP_LOGI(TAG, "Network task initialized on core %d", xPortGetCoreID());

    // Задача больше не нужна; удаляем для освобождения ресурсов
    vTaskDelete(NULL);
}

// Запуск веб-сервера и регистрация обработчиков URI
static httpd_handle_t start_webserver(void)
{
    httpd_config_t config = HTTPD_DEFAULT_CONFIG();
    httpd_handle_t server = NULL;
    if (httpd_start(&server, &config) != ESP_OK) {
        ESP_LOGE(TAG, "Failed to start HTTP server");
        return NULL;
    }

    httpd_uri_t root_get = {
        .uri = "/",
        .method = HTTP_GET,
        .handler = root_get_handler,
        .user_ctx = NULL
    };
    httpd_register_uri_handler(server, &root_get);

    httpd_uri_t submit_post = {
        .uri = "/submit",
        .method = HTTP_POST,
        .handler = submit_post_handler,
        .user_ctx = NULL
    };
    httpd_register_uri_handler(server, &submit_post);

    httpd_uri_t status_get = {
        .uri = "/status",
        .method = HTTP_GET,
        .handler = status_get_handler,
        .user_ctx = NULL
    };
    httpd_register_uri_handler(server, &status_get);

    ESP_LOGI(TAG, "HTTP server started");
    return server;
}

// Инициализация WiFi в режиме SoftAP
static void wifi_init_softap(void)
{
    esp_netif_init();
    esp_event_loop_create_default();
    esp_netif_create_default_wifi_ap();

    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    ESP_ERROR_CHECK(esp_wifi_init(&cfg));

    wifi_config_t wifi_config = {
        .ap = {
            .ssid = AP_SSID,
            .ssid_len = 0,
            .password = AP_PASS,
            .max_connection = AP_MAX_CONN,
            .authmode = WIFI_AUTH_WPA_WPA2_PSK,
        },
    };

    if (strlen(AP_PASS) == 0) {
        wifi_config.ap.authmode = WIFI_AUTH_OPEN;
    }

    ESP_ERROR_CHECK(esp_wifi_set_mode(WIFI_MODE_AP));
    ESP_ERROR_CHECK(esp_wifi_set_config(WIFI_IF_AP, &wifi_config));
    ESP_ERROR_CHECK(esp_wifi_start());

    ESP_LOGI(TAG, "softAP started SSID:%s password:%s", AP_SSID, AP_PASS);
}

void app_main(void)
{
    esp_err_t err = nvs_flash_init();
    if (err == ESP_ERR_NVS_NO_FREE_PAGES || err == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        ESP_ERROR_CHECK(nvs_flash_erase());
        err = nvs_flash_init();
    }
    ESP_ERROR_CHECK(err);

    // Создание задачи инициализации сети, привязанной к ядру 0
    xTaskCreatePinnedToCore(network_task, "net_init", 4096, NULL, 5, NULL, 0);

    // Инициализация аппаратного ШИМ (запускает/создает задачу RMT, привязанную к ядру 1)
    init_pwm_from_globals();
    // Инициализация быстрого ШИМ LEDC
    init_fast_pwm();

    ESP_LOGI(TAG, "Application started. Connect to SSID '%s' and open http://192.168.4.1/", AP_SSID);
}
