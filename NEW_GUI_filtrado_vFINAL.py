# -*- coding: utf-8 -*-
"""
NEW_GUI.py
Versión liviana de la interfaz para el tablero de bioprocesos
"""
from __future__ import annotations

import os
import csv
import glob
import math
import time
import random
import threading
import datetime as dt
import calendar as pycal
from collections import deque
from importlib import util as importlib_util

import tkinter as tk
from tkinter import ttk, messagebox, filedialog

import numpy as np
from scipy import signal
from PIL import Image, ImageTk


_ADS_I2C = None

# ===== MODO SIMULADOR =====
SIMULADOR = os.environ.get("SIMULADOR", "").strip().lower() in {"1", "true", "yes"}
FLOW_DEBUG = os.environ.get("FLOW_DEBUG", "").strip().lower() in {"1", "true", "yes"}
FLOW_DEBUG_FERMS = {
    f.strip().upper()
    for f in os.environ.get("FLOW_DEBUG_FERMS", "").split(",")
    if f.strip()
}

ASSETS_DIR = os.path.join(os.path.dirname(__file__), "assets")


# ===== Configuracion caudalimetro CO2 (ADS1115) =====
def parse_int(value: str, default: int) -> int:
    raw = (value or "").strip().lower()
    if not raw:
        return default
    if raw.startswith("0x"):
        return int(raw, 16)
    return int(raw, 10)


ADS1115_ADDR = parse_int(os.environ.get("ADS1115_ADDR", "0x48"), 0x48)
ADS1115_CH = parse_int(os.environ.get("ADS1115_CH", "1"), 1)
ADS1115_GAIN = parse_int(os.environ.get("ADS1115_GAIN", "1"), 1)

DEFAULT_SHUNT_OHMS = float(os.environ.get("SHUNT_OHMS", "148.0"))
SHUNT_OHMS = {
    "F1": float(os.environ.get("SHUNT_OHMS_F1", "148.0")),
    "F2": float(os.environ.get("SHUNT_OHMS_F2", "148.5")),
    "F3": float(os.environ.get("SHUNT_OHMS_F3", "147.5")),
}
FLOW_MIN_SCCM = float(os.environ.get("FLOW_MIN_SCCM", os.environ.get("FLOW_MIN_M3H", "0.0")))
FLOW_MAX_SCCM = float(os.environ.get("FLOW_MAX_SCCM", os.environ.get("FLOW_MAX_M3H", "50.0")))
CO2_DENSITY_G_M3 = float(os.environ.get("CO2_DENSITY_G_M3", "1964.0"))
BROTH_VOLUME_L = float(os.environ.get("BROTH_VOLUME_L", "2.0"))

SAMPLE_PERIOD_SEC_ENV = os.environ.get("SAMPLE_PERIOD_SEC", "").strip()
SAMPLE_PERIOD_SEC = parse_int(SAMPLE_PERIOD_SEC_ENV, 0) if SAMPLE_PERIOD_SEC_ENV else None
PLOT_WINDOW_ENV = os.environ.get("PLOT_WINDOW_HOURS", "").strip()
PLOT_WINDOW_HOURS = float(PLOT_WINDOW_ENV) if PLOT_WINDOW_ENV else 0.0
MAX_FLOW_HISTORY_HOURS = 24 * 21

# ===== Filtros CO2 (tiempo real) =====
W_SPIKE_SECONDS = 120.0
K = 3.5
MIN_ABS_SPIKE = 0.5
TAU_SECONDS = 1200.0
BUTTER_ORDER = 3

# ===== Conversión CO2 filtrado (solo gráfico) =====
STANDARD_MOLAR_VOLUME_L_PER_MOL = float(os.environ.get("STANDARD_MOLAR_VOLUME_L_PER_MOL", "24.16"))
CO2_MOLAR_MASS_G_PER_MOL = float(os.environ.get("CO2_MOLAR_MASS_G_PER_MOL", "44.0095"))
REACTOR_WORKING_VOLUME_L = float(os.environ.get("REACTOR_WORKING_VOLUME_L", "2.0"))
CO2_FLOW_CORRECTION_FACTOR = float(os.environ.get("CO2_FLOW_CORRECTION_FACTOR", "0.74"))

# ===== PINES HARDWARE =====
RELAY_PINS = {
    "F1": {"cold": 7, "hot": 8},
    "F2": {"cold": 24, "hot": 23},
    "F3": {"cold": 18, "hot": 15},
}
STEPPER_PINS = {
    "F1": {"pul": 13, "dir": 26},
    "F2": {"pul": 21, "dir": 20},
    "F3": {"pul": 12, "dir": 16},
}

# ===== Utilidades de tiempo =====
MESES_ES = [
    "",
    "Enero",
    "Febrero",
    "Marzo",
    "Abril",
    "Mayo",
    "Junio",
    "Julio",
    "Agosto",
    "Septiembre",
    "Octubre",
    "Noviembre",
    "Diciembre",
]


def now():
    return dt.datetime.now()


def now_str():
    return now().strftime("%Y-%m-%d %H:%M:%S")


def ymd(date: dt.date) -> str:
    return date.strftime("%Y-%m-%d")


def hhmm_ok(s: str) -> bool:
    try:
        h, m = s.split(":")
        h = int(h)
        m = int(m)
        return 0 <= h <= 23 and 0 <= m <= 59
    except Exception:
        return False


def _normalize_date(date_str: str):
    date_str = (date_str or "").strip()
    for fmt in ("%Y-%m-%d", "%d/%m/%Y", "%d-%m-%Y", "%Y/%m/%d"):
        try:
            return dt.datetime.strptime(date_str, fmt).date()
        except Exception:
            continue
    return None


def _restore_focus(widget):
    try:
        root = widget.winfo_toplevel()
        root.focus_force()
        root.update_idletasks()
        root.after(10, root.focus_force)
    except Exception:
        pass


def voltage_to_current_ma(voltage: float, shunt_ohms: float) -> float:
    return (voltage / shunt_ohms) * 1000.0


def current_to_flow_sccm(current_ma: float) -> float:
    if FLOW_MAX_SCCM <= FLOW_MIN_SCCM:
        return 0.0
    current_ma = max(4.0, min(20.0, current_ma))
    span = 16.0
    return FLOW_MIN_SCCM + (current_ma - 4.0) * (FLOW_MAX_SCCM - FLOW_MIN_SCCM) / span


def flow_to_rate_g_l_h(flow_sccm: float) -> float:
    if CO2_DENSITY_G_M3 <= 0 or BROTH_VOLUME_L <= 0:
        return 0.0
    flow_m3h = flow_sccm * 6e-5
    return (flow_m3h * CO2_DENSITY_G_M3) / BROTH_VOLUME_L


def flow_sccm_to_co2_g_l_h_plot(flow_sccm: float) -> float:
    if STANDARD_MOLAR_VOLUME_L_PER_MOL <= 0 or REACTOR_WORKING_VOLUME_L <= 0:
        return 0.0
    # SCCM = cm3/min = mL/min; pasamos a L/min y luego a g/(L*h) de CO2 corregido.
    mol_per_min = (float(flow_sccm) / 1000.0) / STANDARD_MOLAR_VOLUME_L_PER_MOL
    g_per_h = mol_per_min * CO2_MOLAR_MASS_G_PER_MOL * 60.0 * CO2_FLOW_CORRECTION_FACTOR
    return g_per_h / REACTOR_WORKING_VOLUME_L


# ===== Filtros CO2 en streaming (causales) =====
class HampelCausal:
    def __init__(self, w, k, min_abs_spike):
        self.w = max(1, int(w))
        self.k = float(k)
        self.min_abs_spike = float(min_abs_spike)
        self.buf = deque(maxlen=self.w)

    def update(self, x):
        x = float(x)
        self.buf.append(x)
        if len(self.buf) < 3:
            return x, False

        arr = np.asarray(self.buf, dtype=float)
        med = float(np.median(arr))
        mad = float(np.median(np.abs(arr - med)))
        sigma = 1.4826 * mad
        threshold = max(self.k * sigma, self.min_abs_spike)
        is_spike = abs(x - med) > threshold
        if is_spike:
            return med, True
        return x, False


class ButterworthCausalSOS:
    def __init__(self, dt_seconds, tau_seconds, order):
        self.dt_seconds = float(dt_seconds)
        self.tau_seconds = float(tau_seconds)
        self.order = int(order)
        if self.dt_seconds <= 0:
            raise ValueError("dt_seconds debe ser > 0")
        if self.tau_seconds <= 0:
            raise ValueError("tau_seconds debe ser > 0")
        if self.order < 1:
            raise ValueError("order debe ser >= 1")

        fs = 1.0 / self.dt_seconds
        fc = 1.0 / (2.0 * math.pi * self.tau_seconds)
        wn = fc / (fs / 2.0)
        wn = min(max(wn, 1e-8), 0.999999)

        self.sos = signal.butter(self.order, wn, btype="low", output="sos")
        self.zi = None

    def update(self, x):
        x = float(x)
        x_in = np.asarray([x], dtype=float)
        if self.zi is None:
            self.zi = signal.sosfilt_zi(self.sos) * x
        y, self.zi = signal.sosfilt(self.sos, x_in, zi=self.zi)
        return float(y[-1])


class CO2RealtimeFilter:
    def __init__(self, dt_seconds, w_spike_seconds, k, min_abs_spike, tau_seconds, butter_order):
        dt_seconds = float(dt_seconds)
        w = max(1, int(round(float(w_spike_seconds) / max(dt_seconds, 1e-9))))
        self.hampel = HampelCausal(w=w, k=k, min_abs_spike=min_abs_spike)
        self.butter = ButterworthCausalSOS(dt_seconds=dt_seconds, tau_seconds=tau_seconds, order=butter_order)

    def update(self, flow_raw):
        flow_despike, is_spike = self.hampel.update(flow_raw)
        flow_filt = self.butter.update(flow_despike)
        return float(flow_despike), float(flow_filt), bool(is_spike)


# ===== Hardware layer (con fallback simulador) =====
class Hardware:
    def __init__(self):
        self.sim = SIMULADOR
        self.sim_reason = "Forzado por variable de entorno" if self.sim else ""
        self.sim_gpio = self.sim
        self.sim_gpio_reason = "Forzado por variable de entorno" if self.sim else ""
        self.gpio = None
        self.pwms = {}
        self._last_temp_error = False
        self._sim_bias = [random.uniform(-1, 1) for _ in range(3)]
        self.ds_devices = []

        if not self.sim:
            try:
                import RPi.GPIO as GPIO  # type: ignore

                self.gpio = GPIO
                GPIO.setmode(GPIO.BCM)
                GPIO.setwarnings(False)
            except Exception as e:
                # Solo desactivamos GPIO; no afecta ADS1115 ni DS18B20.
                self.sim_gpio = True
                self.sim_gpio_reason = f"GPIO fallback: {e}"
                self.gpio = None

            # Buscamos los DS18B20, pero NO forzamos simulador si no hay
            self.ds_devices = sorted(glob.glob("/sys/bus/w1/devices/28-*"))
            if len(self.ds_devices) < 1:
                print(
                    "[HW] Advertencia: no se encontraron DS18B20, "
                    "se usará 20°C de respaldo para la temperatura."
                )

        if self.sim:
            print(f"[HW] Modo simulador activo. {self.sim_reason}")
        else:
            if self.sim_gpio:
                print(f"[HW] GPIO en simulador. {self.sim_gpio_reason}")
            else:
                print("[HW] GPIO activo.")
            print("[HW] Modo hardware activo. Sensores detectados:", self.ds_devices)

    def _gpio_fallback(self, exc: Exception):
        if self.sim_gpio:
            return
        self.sim_gpio = True
        self.sim_gpio_reason = f"GPIO fallback: {exc}"
        self.gpio = None
        self.pwms = {}
        print(f"[HW] {self.sim_gpio_reason}")

    # --- DS18B20 ---
    def read_temp_ds18b20(self, index: int) -> float:
        if self.sim or not self.ds_devices:
            base = 20.0 + self._sim_bias[min(index, len(self._sim_bias) - 1)]
            return base + random.uniform(-0.5, 0.5)
        if index >= len(self.ds_devices):
            index = len(self.ds_devices) - 1
        dev = self.ds_devices[index]
        try:
            with open(os.path.join(dev, "w1_slave"), "r") as f:
                lines = f.readlines()
            if len(lines) < 2 or "YES" not in lines[0]:
                raise RuntimeError("CRC inválido")
            temp_str = lines[1].split("t=")[-1].strip()
            return float(temp_str) / 1000.0
        except Exception as e:
            if not self._last_temp_error:
                print(f"[HW] Error leyendo {dev}: {e}. Usando 20°C de respaldo.")
                self._last_temp_error = True
            return 20.0
        finally:
            self._last_temp_error = False

    # --- Relés ---
    def setup_relay(self, pin: int):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        try:
            self.gpio.setup(pin, self.gpio.OUT)
            self.gpio.output(pin, self.gpio.HIGH)
        except Exception as e:
            self._gpio_fallback(e)

    def relay_on(self, pin: int):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        try:
            self.gpio.output(pin, self.gpio.LOW)
        except Exception as e:
            self._gpio_fallback(e)

    def relay_off(self, pin: int):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        try:
            self.gpio.output(pin, self.gpio.HIGH)
        except Exception as e:
            self._gpio_fallback(e)

    # --- Stepper ---
    def setup_stepper(self, name: str, pul: int, direction: int, freq: float):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        try:
            GPIO = self.gpio
            GPIO.setup(direction, GPIO.OUT)
            GPIO.output(direction, GPIO.LOW)
            GPIO.setup(pul, GPIO.OUT)
            pwm = GPIO.PWM(pul, max(1, int(freq)))
            self.pwms[name] = {"pwm": pwm, "dir": direction, "pul": pul}
        except Exception as e:
            self._gpio_fallback(e)

    def start_stepper(self, name: str, freq: float):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        if name not in self.pwms:
            return
        try:
            pwm = self.pwms[name]["pwm"]
            pwm.ChangeFrequency(max(1, int(freq)))
            pwm.start(1)
        except Exception as e:
            self._gpio_fallback(e)

    def stop_stepper(self, name: str):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        if name not in self.pwms:
            return
        try:
            pwm = self.pwms[name]["pwm"]
            pwm.stop()
            self.gpio.output(self.pwms[name]["dir"], self.gpio.LOW)
        except Exception as e:
            self._gpio_fallback(e)

    def cleanup(self):
        if self.sim or self.sim_gpio or not self.gpio:
            return
        try:
            self.gpio.cleanup()
        except Exception:
            pass


# ===== ADS1115 / Caudalimetro CO2 =====
class ADS1115Reader:
    def __init__(self, address: int, channel: int, gain: int, shunt_ohms: float):
        self.address = address
        self.channel = max(0, min(3, channel))
        self.gain = gain
        self.shunt_ohms = shunt_ohms
        self.sim = SIMULADOR
        self.sim_reason = ""
        self._sim_start = time.monotonic()
        self._ads = None
        self._chan = None
        self._init_hw()

    def _init_hw(self):
        global _ADS_I2C
        if self.sim:
            self.sim_reason = "Forzado por variable de entorno"
            return
        try:
            import board  # type: ignore
            import busio  # type: ignore
            import adafruit_ads1x15.ads1115 as ADS  # type: ignore
            from adafruit_ads1x15.analog_in import AnalogIn  # type: ignore
        except Exception as exc:
            self.sim = True
            self.sim_reason = f"Fallback a simulador: {exc}"
            return

        try:
            if _ADS_I2C is None:
                _ADS_I2C = busio.I2C(board.SCL, board.SDA)
            i2c = _ADS_I2C
            ads = ADS.ADS1115(i2c, address=self.address)
            ads.gain = self.gain
            try:
                ch_map = [ADS.P0, ADS.P1, ADS.P2, ADS.P3]
            except AttributeError:
                try:
                    from adafruit_ads1x15.ads1x15 import Pin  # type: ignore

                    ch_map = [Pin.A0, Pin.A1, Pin.A2, Pin.A3]
                except Exception:
                    ch_map = [0, 1, 2, 3]
            self._ads = ads
            self._chan = AnalogIn(ads, ch_map[self.channel])
        except Exception as exc:
            self.sim = True
            self.sim_reason = f"Fallback a simulador: {exc}"
            self._ads = None
            self._chan = None

    def read_voltage(self) -> float:
        if self.sim or not self._chan:
            t_hours = (time.monotonic() - self._sim_start) / 3600.0
            tr = 0.2
            td = 4.0
            if td <= tr:
                td = tr + 0.1
            t_peak = (tr * td / (td - tr)) * math.log(td / tr)
            peak_shape = math.exp(-t_peak / td) - math.exp(-t_peak / tr)
            peak_shape = peak_shape if peak_shape > 0 else 1.0
            amplitude = FLOW_MAX_SCCM / peak_shape
            flow_sccm = amplitude * (math.exp(-t_hours / td) - math.exp(-t_hours / tr))
            flow_sccm += random.uniform(-0.3, 0.3)
            flow_sccm = max(FLOW_MIN_SCCM, min(FLOW_MAX_SCCM, flow_sccm))
            if FLOW_MAX_SCCM > FLOW_MIN_SCCM:
                current_ma = 4.0 + (flow_sccm - FLOW_MIN_SCCM) * 16.0 / (FLOW_MAX_SCCM - FLOW_MIN_SCCM)
            else:
                current_ma = 4.0
            current_ma = max(4.0, min(20.0, current_ma))
            return (current_ma / 1000.0) * self.shunt_ohms
        return float(self._chan.voltage)

    def probe(self):
        if self.sim:
            return False, None, f"SIMULADOR ({self.sim_reason})"
        if not self._chan:
            return False, None, "Canal no inicializado"
        try:
            v = float(self._chan.voltage)
        except Exception as exc:
            return False, None, f"Error leyendo: {exc}"
        low_v = (4.0 / 1000.0) * self.shunt_ohms
        high_v = (20.0 / 1000.0) * self.shunt_ohms
        if low_v <= v <= high_v:
            note = "OK"
        else:
            note = f"OK (fuera de rango esperado {low_v:.2f}-{high_v:.2f} V)"
        return True, v, note

    def close(self):
        global _ADS_I2C
        self._chan = None
        self._ads = None
        if _ADS_I2C is not None:
            try:
                _ADS_I2C.deinit()
            except Exception:
                pass
            _ADS_I2C = None


# ===== LED widget =====
class Led:
    def __init__(self, parent, size=20):
        bg = None
        for key in ("fg_color", "background", "bg"):
            try:
                bg = parent.cget(key)
                break
            except Exception:
                continue
        if bg is None:
            bg = "#111827"
        self.canvas = tk.Canvas(
            parent,
            width=size,
            height=size,
            highlightthickness=0,
            bd=0,
            bg=bg,
        )
        r = 2
        self.oval = self.canvas.create_oval(r, r, size - r, size - r, fill="red", outline="#111")

    def widget(self):
        return self.canvas

    def set_color(self, color: str):
        self.canvas.itemconfig(self.oval, fill=color)

    def set_on(self, on: bool):
        self.set_color("#22c55e" if on else "#ef4444")


# ===== Calendario por FECHAS =====
DAYS_SHORT = ["L", "Ma", "Mi", "J", "V", "S", "D"]


class DateCalendarDialog(tk.Toplevel):
    def __init__(self, master, title_label, value_label, value_type=float, initial=None, import_callback=None):
        super().__init__(master)
        self.title(title_label)
        self.geometry("840x540")
        self.resizable(False, False)
        self.transient(master)
        self.grab_set()

        self.value_type = value_type
        self.data = {}
        self.import_callback = import_callback
        if isinstance(initial, dict):
            for k, v in initial.items():
                self.data[k] = [dict(ev) for ev in v]

        self.today = dt.date.today()
        self.selected_date = self.today
        self.view_year = self.today.year
        self.view_month = self.today.month

        container = ttk.Frame(self, padding=10)
        container.grid(row=0, column=0, sticky="nsew")
        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)

        left = ttk.Frame(container)
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 10))
        right = ttk.Frame(container)
        right.grid(row=0, column=1, sticky="nsew")

        container.columnconfigure(0, weight=0)
        container.columnconfigure(1, weight=1)
        container.rowconfigure(0, weight=1)

        nav = ttk.Frame(left)
        nav.grid(row=0, column=0, sticky="ew")
        ttk.Button(nav, text="◀", width=3, command=self.prev_month).grid(row=0, column=0, padx=2)
        self.lbl_month = ttk.Label(nav, text="", font=("Segoe UI", 12, "bold"))
        self.lbl_month.grid(row=0, column=1, padx=4)
        ttk.Button(nav, text="▶", width=3, command=self.next_month).grid(row=0, column=2, padx=2)
        nav.columnconfigure(1, weight=1)

        self.cal_grid = ttk.Frame(left)
        self.cal_grid.grid(row=1, column=0, sticky="nsew", pady=(8, 0))
        for c in range(7):
            self.cal_grid.columnconfigure(c, weight=1, uniform="days")
        for col, d in enumerate(DAYS_SHORT):
            ttk.Label(self.cal_grid, text=d, width=4, anchor="center").grid(
                row=0, column=col, padx=2, pady=2, sticky="nsew"
            )

        ttk.Label(right, text="Fecha seleccionada:", font=("Segoe UI", 10, "bold")).grid(row=0, column=0, sticky="w")
        self.lbl_sel = ttk.Label(right, text="")
        self.lbl_sel.grid(row=1, column=0, sticky="w", pady=(0, 6))

        self.listbox = tk.Listbox(right, height=16)
        self.listbox.grid(row=2, column=0, sticky="nsew")
        sb = ttk.Scrollbar(right, orient="vertical", command=self.listbox.yview)
        sb.grid(row=2, column=1, sticky="ns")
        self.listbox.config(yscrollcommand=sb.set)

        form = ttk.Frame(right)
        form.grid(row=3, column=0, sticky="ew", pady=8)
        ttk.Label(form, text="Hora (HH:MM):").grid(row=0, column=0, padx=4, pady=2, sticky="e")
        self.time_var = tk.StringVar(value="08:00")
        ttk.Entry(form, textvariable=self.time_var, width=8, justify="center").grid(row=0, column=1, padx=4, pady=2)

        ttk.Label(form, text=value_label).grid(row=1, column=0, padx=4, pady=2, sticky="e")
        self.val_var = tk.StringVar(value="20.0")
        ttk.Entry(form, textvariable=self.val_var, width=10, justify="center").grid(row=1, column=1, padx=4, pady=2)

        btns = ttk.Frame(right)
        btns.grid(row=4, column=0, sticky="ew", pady=(0, 4))
        ttk.Button(btns, text="Agregar", command=self.add_event).grid(row=0, column=0, padx=4)
        ttk.Button(btns, text="Editar", command=self.edit_event).grid(row=0, column=1, padx=4)
        ttk.Button(btns, text="Borrar", command=self.del_event).grid(row=0, column=2, padx=4)
        ttk.Button(btns, text="Borrar todo (día)", command=self.clear_day).grid(row=0, column=3, padx=4)
        if self.import_callback:
            ttk.Button(btns, text="Importar CSV/Excel", command=self.import_file).grid(
                row=1, column=0, columnspan=4, padx=4, pady=(6, 0)
            )

        right.rowconfigure(2, weight=1)

        sep = ttk.Separator(self, orient="horizontal")
        sep.grid(row=1, column=0, sticky="ew", padx=10, pady=(6, 0))
        footer = ttk.Frame(self, padding=(10, 6))
        footer.grid(row=2, column=0, sticky="e")
        ttk.Button(footer, text="Aceptar", command=self.accept).grid(row=0, column=0, padx=6)
        ttk.Button(footer, text="Cancelar", command=self.cancel).grid(row=0, column=1, padx=6)

        self.styles = {
            "normal_bg": self.cget("bg"),
            "today_bg": "#BEE3F8",
            "has_bg": "#C6F6D5",
            "other_bg": "#EDF2F7",
            "disabled_bg": "#E2E8F0",
        }

        self.day_buttons = []
        self.refresh_calendar()
        self.refresh_day_list()

    def month_title(self):
        return f"{MESES_ES[self.view_month]} {self.view_year}"

    def refresh_calendar(self):
        for child in list(self.cal_grid.grid_slaves()):
            info = child.grid_info()
            if int(info["row"]) > 0:
                child.destroy()

        self.lbl_month.config(text=self.month_title())
        self.day_buttons.clear()

        cal = pycal.Calendar(firstweekday=0)
        weeks = cal.monthdatescalendar(self.view_year, self.view_month)

        for r, week in enumerate(weeks, start=1):
            for c, d in enumerate(week):
                btn = tk.Button(
                    self.cal_grid,
                    text=str(d.day),
                    width=4,
                    relief="raised",
                    bd=1,
                    command=lambda dd=d: self.select_date(dd),
                )
                btn.grid(row=r, column=c, padx=2, pady=2, sticky="nsew")

                is_other_month = d.month != self.view_month
                is_past = d < self.today
                has_ev = ymd(d) in self.data and len(self.data[ymd(d)]) > 0
                is_today = d == self.today

                if is_past:
                    btn.config(
                        state="disabled",
                        bg=self.styles["disabled_bg"],
                        activebackground=self.styles["disabled_bg"],
                    )
                else:
                    bg = self.styles["other_bg"] if is_other_month else self.styles["normal_bg"]
                    if has_ev:
                        bg = self.styles["has_bg"]
                    if is_today:
                        bg = self.styles["today_bg"] if not has_ev else "#9AE6B4"
                    btn.config(bg=bg, activebackground=bg)

                if d == self.selected_date:
                    btn.config(relief="sunken")

                self.day_buttons.append((btn, d))

        self.lbl_sel.config(text=ymd(self.selected_date))

    def select_date(self, date_obj: dt.date):
        if date_obj < self.today:
            return
        self.selected_date = date_obj
        self.refresh_calendar()
        self.refresh_day_list()

    def prev_month(self):
        y, m = self.view_year, self.view_month
        if m == 1:
            y, m = y - 1, 12
        else:
            m -= 1
        self.view_year, self.view_month = y, m
        self.refresh_calendar()

    def next_month(self):
        y, m = self.view_year, self.view_month
        if m == 12:
            y, m = y + 1, 1
        else:
            m += 1
        self.view_year, self.view_month = y, m
        self.refresh_calendar()

    def refresh_day_list(self):
        self.listbox.delete(0, tk.END)
        flist = self.data.get(ymd(self.selected_date), [])
        for it in sorted(flist, key=lambda x: x["time"]):
            self.listbox.insert(tk.END, f"{it['time']}  •  {it['value']}")

    def _sel_index(self):
        sel = self.listbox.curselection()
        return sel[0] if sel else None

    def add_event(self):
        if self.selected_date < self.today:
            messagebox.showerror("Calendario", "No se pueden programar días anteriores al actual.")
            return
        t = self.time_var.get().strip()
        if not hhmm_ok(t):
            messagebox.showerror("Calendario", "Hora inválida (HH:MM).")
            return
        try:
            val = self.value_type(self.val_var.get().strip())
        except Exception:
            messagebox.showerror("Calendario", "Valor inválido.")
            return
        key = ymd(self.selected_date)
        self.data.setdefault(key, []).append({"time": t, "value": val})
        self.refresh_day_list()
        self.refresh_calendar()

    def edit_event(self):
        idx = self._sel_index()
        if idx is None:
            return
        key = ymd(self.selected_date)
        flist = sorted(self.data.get(key, []), key=lambda x: x["time"])
        if not flist:
            return
        t = self.time_var.get().strip()
        if not hhmm_ok(t):
            messagebox.showerror("Calendario", "Hora inválida (HH:MM).")
            return
        try:
            val = self.value_type(self.val_var.get().strip())
        except Exception:
            messagebox.showerror("Calendario", "Valor inválido.")
            return
        old = flist[idx]
        orig = self.data[key].index(old)
        self.data[key][orig] = {"time": t, "value": val}
        self.refresh_day_list()
        self.refresh_calendar()

    def del_event(self):
        idx = self._sel_index()
        if idx is None:
            return
        key = ymd(self.selected_date)
        flist = sorted(self.data.get(key, []), key=lambda x: x["time"])
        if not flist:
            return
        self.data[key].remove(flist[idx])
        if not self.data[key]:
            del self.data[key]
        self.refresh_day_list()
        self.refresh_calendar()

    def clear_day(self):
        key = ymd(self.selected_date)
        if key in self.data and self.data[key]:
            if messagebox.askyesno("Calendario", f"¿Borrar todos los eventos del {key}?"):
                del self.data[key]
                self.refresh_day_list()
                self.refresh_calendar()

    def import_file(self):
        if not self.import_callback:
            return
        data = self.import_callback()
        if data:
            self.data = data
            self.refresh_day_list()
            self.refresh_calendar()

    def accept(self):
        self.grab_release()
        self.destroy()

    def cancel(self):
        self.data = None
        self.grab_release()
        self.destroy()


# ===== Funciones calendario =====
def sp_from_date_calendar(events_dict: dict | None, t: dt.datetime, default=None):
    if not events_dict:
        return default
    key = ymd(t.date())
    flist = events_dict.get(key, [])
    if not flist:
        return default
    hhmm_now = t.strftime("%H:%M")
    todays = [e for e in flist if e.get("time") and e["time"] <= hhmm_now]
    if not todays:
        return default
    todays = sorted(todays, key=lambda e: e["time"])
    return todays[-1].get("value", default)


def nut_fire_for_minute(events_dict: dict | None, t: dt.datetime):
    if not events_dict:
        return []
    key = ymd(t.date())
    flist = events_dict.get(key, [])
    if not flist:
        return []
    hhmm_now = t.strftime("%H:%M")
    return [e.get("value") for e in flist if e.get("time") == hhmm_now]


def _events_from_rows(rows, value_type=float):
    events = {}
    for row in rows:
        date_raw = row.get("date") or row.get("fecha") or row.get("dia") or row.get("d")
        time_raw = row.get("time") or row.get("hora") or row.get("t")
        val_raw = row.get("value") or row.get("valor") or row.get("v")
        if not date_raw or not time_raw or val_raw is None:
            continue
        date_obj = _normalize_date(str(date_raw))
        if not date_obj:
            continue
        hhmm = str(time_raw).strip()
        if not hhmm_ok(hhmm):
            continue
        try:
            val = value_type(val_raw)
        except Exception:
            continue
        key = ymd(date_obj)
        events.setdefault(key, []).append({"time": hhmm, "value": val})
    return events


def _load_calendar_file(path: str, value_type=float):
    ext = os.path.splitext(path)[1].lower()
    if ext in {".csv", ".txt"}:
        with open(path, "r", encoding="utf-8") as f:
            rows = list(csv.DictReader(f))
        return _events_from_rows(rows, value_type=value_type)
    if ext in {".xlsx", ".xls"}:
        pd_spec = importlib_util.find_spec("pandas")
        if not pd_spec:
            raise RuntimeError("Necesitas instalar pandas para leer archivos de Excel (.xlsx/.xls)")
        import pandas as pd  # type: ignore

        df = pd.read_excel(path)
        rows = df.to_dict(orient="records")
        return _events_from_rows(rows, value_type=value_type)
    raise RuntimeError("Formato no soportado. Usa CSV o Excel.")

# ------------------------------------------------------------
# Utilidades GUI
# ------------------------------------------------------------


class ScrollableFrame(ttk.Frame):
    """Frame scrollable vertical simple (más liviano que CTkScrollableFrame)."""

    def __init__(self, parent):
        super().__init__(parent)
        self.canvas = tk.Canvas(self, highlightthickness=0)
        self.vsb = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.inner = ttk.Frame(self.canvas)

        self.inner.bind(
            "<Configure>",
            lambda _e: self.canvas.configure(scrollregion=self.canvas.bbox("all")),
        )
        self._window_id = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")

        self.canvas.configure(yscrollcommand=self.vsb.set)

        self.canvas.pack(side="left", fill="both", expand=True)
        self.vsb.pack(side="right", fill="y")

        self.canvas.bind("<Configure>", self._on_canvas_configure)

    def _on_canvas_configure(self, event):
        # Asegura que el frame interno ocupe el ancho del canvas.
        self.canvas.itemconfigure(self._window_id, width=event.width)


# ------------------------------------------------------------
# Panel por fermentador (GUI liviana)
# ------------------------------------------------------------


class LightFermenterPanel(ttk.Frame):
    def __init__(self, parent, app, name, hw: Hardware, backup_path_getter):
        super().__init__(parent, padding=8)
        self.app = app
        self.name = name
        self.hw = hw
        self.get_backup_path = backup_path_getter

        if self.hw.sim:
            self.t = 21.5 + random.uniform(-0.3, 0.3)
            self._sim_ambient = 21.0 + random.uniform(-0.4, 0.4)
        else:
            self.t = self.hw.read_temp_ds18b20(index=int(self.name[1:]) - 1)
            self._sim_ambient = None
        self._last_update = now()

        self.t_str = tk.StringVar(value=f"{self.t:.1f}")
        self.flow_str = tk.StringVar(value="-- SCCM")
        self.sp = tk.DoubleVar(value=20.0)
        self.band = tk.DoubleVar(value=0.5)
        self.manual_mode = tk.BooleanVar(value=False)

        self.cold_in = False
        self.hot_in = False

        self.cal_sp = {}
        self.cal_nut = {}

        self.nut_running_until = None
        self._nut_led_on = False
        self._last_min = None
        self.freq_nut = tk.DoubleVar(value=1000.0)
        self.sp_entry = tk.StringVar(value=f"{self.sp.get():.1f}")
        self.band_entry = tk.StringVar(value=f"{self.band.get():.2f}")
        self.freq_entry = tk.StringVar(value=f"{self.freq_nut.get():.1f}")
        self.manual_nut_on = False

        self.csv_dir = tk.StringVar(value=os.path.abspath("./Proceso"))
        self.csv_name = tk.StringVar(value=f"Temp_{self.name}.csv")
        self._csv_running = False
        self._csv_paused = False
        self._csv_last_export_ok = False
        os.makedirs(self.csv_dir.get(), exist_ok=True)

        rel = RELAY_PINS[self.name]
        self.relay_cold = rel["cold"]
        self.relay_hot = rel["hot"]
        self.stepper_name = self.name
        step = STEPPER_PINS[self.name]
        if not hw.sim:
            hw.setup_relay(self.relay_cold)
            hw.setup_relay(self.relay_hot)
            hw.setup_stepper(self.stepper_name, step["pul"], step["dir"], 50)

        self._build_ui()

    # ---------------- UI ----------------
    def _build_ui(self):
        self.columnconfigure(0, weight=1)

        title = ttk.Label(self, text=f"Fermentador {self.name}", font=("Segoe UI", 13, "bold"))
        title.grid(row=0, column=0, sticky="w", padx=4, pady=(2, 6))

        # Medición/Control
        meas = ttk.Frame(self)
        meas.grid(row=1, column=0, sticky="ew", padx=4)
        meas.columnconfigure((0, 1, 2, 3), weight=1)

        ttk.Label(meas, text="T (°C)").grid(row=0, column=0, sticky="w")
        ttk.Label(meas, textvariable=self.t_str, font=("Segoe UI", 16, "bold")).grid(
            row=1, column=0, sticky="w", pady=(0, 6)
        )

        ttk.Label(meas, text="Caudal (SCCM)").grid(row=0, column=1, sticky="w")
        ttk.Label(meas, textvariable=self.flow_str, font=("Segoe UI", 12, "bold")).grid(
            row=1, column=1, sticky="w", pady=(0, 6)
        )

        ttk.Label(meas, text="SP (°C)").grid(row=0, column=2, sticky="w")
        sp_entry = ttk.Entry(meas, textvariable=self.sp_entry, width=8, justify="center")
        sp_entry.grid(row=1, column=2, sticky="w")
        sp_entry.bind("<Return>", lambda _e: self.apply_sp())
        ttk.Button(meas, text="Aplicar", command=self.apply_sp).grid(row=2, column=2, sticky="w", pady=(2, 6))

        ttk.Label(meas, text="Banda (°C)").grid(row=0, column=3, sticky="w")
        band_entry = ttk.Entry(meas, textvariable=self.band_entry, width=8, justify="center")
        band_entry.grid(row=1, column=3, sticky="w")
        band_entry.bind("<Return>", lambda _e: self.apply_band())
        ttk.Button(meas, text="Aplicar", command=self.apply_band).grid(row=2, column=3, sticky="w", pady=(2, 6))

        # Modo manual
        ttk.Checkbutton(self, text="Modo manual (forzar)", variable=self.manual_mode).grid(
            row=2, column=0, sticky="w", padx=4, pady=(2, 6)
        )

        # LEDs Caliente / Fría
        status_row = ttk.Frame(self)
        status_row.grid(row=3, column=0, sticky="w", padx=4, pady=(0, 6))
        ttk.Label(status_row, text="Caliente").grid(row=0, column=0, padx=(0, 4))
        self.led_hot_in = Led(status_row)
        self.led_hot_in.widget().grid(row=0, column=1, padx=(0, 12))
        ttk.Label(status_row, text="Fría").grid(row=0, column=2, padx=(0, 4))
        self.led_cold_in = Led(status_row)
        self.led_cold_in.widget().grid(row=0, column=3)
        self._sync_leds()

        # Botones frío / caliente
        btn_row = ttk.Frame(self)
        btn_row.grid(row=4, column=0, sticky="ew", padx=4, pady=(2, 6))
        btn_row.columnconfigure((0, 1, 2), weight=1)
        ttk.Button(btn_row, text="Forzar FRÍO", command=self.forzar_frio).grid(row=0, column=0, padx=2, sticky="ew")
        ttk.Button(btn_row, text="Cerrar TODO", command=self.cerrar_todo).grid(row=0, column=1, padx=2, sticky="ew")
        ttk.Button(btn_row, text="Forzar CALIENTE", command=self.forzar_caliente).grid(
            row=0, column=2, padx=2, sticky="ew"
        )

        # Calendarios
        cal_row = ttk.Frame(self)
        cal_row.grid(row=5, column=0, sticky="ew", padx=4, pady=(2, 8))
        cal_row.columnconfigure((0, 1), weight=1)
        ttk.Button(cal_row, text="Calendario Setpoint", command=self.edit_cal_sp).grid(
            row=0, column=0, padx=2, sticky="ew"
        )
        ttk.Button(cal_row, text="Calendario Nutrición", command=self.edit_cal_nut).grid(
            row=0, column=1, padx=2, sticky="ew"
        )

        # Nutrición + frecuencia
        nut_frame = ttk.Frame(self)
        nut_frame.grid(row=6, column=0, sticky="ew", padx=4, pady=(2, 6))
        ttk.Label(nut_frame, text="Nutrición en curso:").grid(row=0, column=0, sticky="w")
        self.led_nut = Led(nut_frame)
        self.led_nut.widget().grid(row=0, column=1, padx=(4, 0), sticky="w")
        ttk.Label(nut_frame, text="Frecuencia bomba (Hz):").grid(row=1, column=0, sticky="w", pady=(4, 0))
        freq_entry = ttk.Entry(nut_frame, textvariable=self.freq_entry, width=8, justify="center")
        freq_entry.grid(row=1, column=1, sticky="w", padx=(4, 0), pady=(4, 0))
        freq_entry.bind("<Return>", lambda _e: self.apply_freq())
        ttk.Button(nut_frame, text="Aplicar", command=self.apply_freq).grid(row=1, column=2, sticky="w", padx=(6, 0))

        # Bomba manual
        self.btn_manual_nut = ttk.Button(self, text="Bomba manual OFF", command=self.toggle_manual_nut)
        self.btn_manual_nut.grid(row=7, column=0, padx=4, pady=(4, 8), sticky="ew")
        self._update_manual_nut_button()

        # CSV frame
        csv_box = ttk.LabelFrame(self, text="CSV Temperatura")
        csv_box.grid(row=8, column=0, padx=4, pady=(2, 8), sticky="ew")
        csv_box.columnconfigure(1, weight=1)

        ttk.Label(csv_box, text="Carpeta:").grid(row=0, column=0, sticky="e", padx=(4, 2), pady=2)
        ttk.Entry(csv_box, textvariable=self.csv_dir).grid(row=0, column=1, sticky="ew", pady=2)
        ttk.Button(csv_box, text="...", width=3, command=self.pick_dir).grid(row=0, column=2, sticky="w", padx=2)

        ttk.Label(csv_box, text="Archivo:").grid(row=1, column=0, sticky="e", padx=(4, 2), pady=2)
        ttk.Entry(csv_box, textvariable=self.csv_name).grid(row=1, column=1, sticky="ew", pady=2)

        btn_csv_row = ttk.Frame(csv_box)
        btn_csv_row.grid(row=2, column=0, columnspan=3, sticky="ew", pady=(4, 2))
        btn_csv_row.columnconfigure((0, 1, 2, 3), weight=1)
        ttk.Button(btn_csv_row, text="Inicio/Reanudar", command=self.csv_start).grid(row=0, column=0, padx=2, sticky="ew")
        ttk.Button(btn_csv_row, text="Pausar/Detener", command=self.csv_pause).grid(row=0, column=1, padx=2, sticky="ew")
        ttk.Button(btn_csv_row, text="Exportar CSV", command=self.csv_export).grid(row=0, column=2, padx=2, sticky="ew")
        ttk.Button(btn_csv_row, text="Borrar/Reiniciar", command=self.csv_restart).grid(row=0, column=3, padx=2, sticky="ew")

        state_row = ttk.Frame(csv_box)
        state_row.grid(row=3, column=0, columnspan=3, sticky="w", pady=(2, 4))
        ttk.Label(state_row, text="Estado:").grid(row=0, column=0, sticky="w")
        self.led_csv = Led(state_row)
        self.led_csv.widget().grid(row=0, column=1, sticky="w", padx=(4, 12))
        self._csv_state_led("red")

        ttk.Button(csv_box, text="Gráfico Temperatura", command=lambda: self.app.open_realtime_plot(self.name)).grid(
            row=4, column=0, columnspan=3, sticky="ew", padx=2, pady=(2, 4)
        )

        # CSV CO2
        co2_box = ttk.LabelFrame(self, text="CSV CO2")
        co2_box.grid(row=9, column=0, padx=4, pady=(2, 4), sticky="ew")
        co2_box.columnconfigure(1, weight=1)

        ttk.Label(co2_box, text="Carpeta:").grid(row=0, column=0, sticky="e", padx=(4, 2), pady=2)
        ttk.Entry(co2_box, textvariable=self.app.co2_csv_dir[self.name]).grid(row=0, column=1, sticky="ew", pady=2)
        ttk.Button(co2_box, text="...", width=3, command=lambda: self.app.co2_pick_dir(self.name)).grid(
            row=0, column=2, sticky="w", padx=2
        )

        ttk.Label(co2_box, text="Archivo:").grid(row=1, column=0, sticky="e", padx=(4, 2), pady=2)
        ttk.Entry(co2_box, textvariable=self.app.co2_csv_name[self.name]).grid(row=1, column=1, sticky="ew", pady=2)

        btn_co2_row = ttk.Frame(co2_box)
        btn_co2_row.grid(row=2, column=0, columnspan=3, sticky="ew", pady=(4, 2))
        btn_co2_row.columnconfigure((0, 1, 2, 3), weight=1)
        ttk.Button(btn_co2_row, text="Inicio/Reanudar", command=lambda: self.app.co2_csv_start(self.name)).grid(
            row=0, column=0, padx=2, sticky="ew"
        )
        ttk.Button(btn_co2_row, text="Pausar/Detener", command=lambda: self.app.co2_csv_pause(self.name)).grid(
            row=0, column=1, padx=2, sticky="ew"
        )
        ttk.Button(btn_co2_row, text="Exportar CSV", command=lambda: self.app.co2_csv_export(self.name)).grid(
            row=0, column=2, padx=2, sticky="ew"
        )
        ttk.Button(btn_co2_row, text="Borrar/Reiniciar", command=lambda: self.app.co2_csv_restart(self.name)).grid(
            row=0, column=3, padx=2, sticky="ew"
        )

        state_co2 = ttk.Frame(co2_box)
        state_co2.grid(row=3, column=0, columnspan=3, sticky="w", pady=(2, 4))
        ttk.Label(state_co2, text="Estado:").grid(row=0, column=0, sticky="w")
        led_co2 = Led(state_co2)
        led_co2.widget().grid(row=0, column=1, sticky="w", padx=(4, 12))
        self.app._co2_csv_register_led(self.name, led_co2)
        if self.app.co2_csv_running.get(self.name):
            self.app._co2_csv_state_led(self.name, "#22c55e")
        elif self.app.co2_csv_paused.get(self.name):
            self.app._co2_csv_state_led(self.name, "#eab308")
        elif self.app.co2_csv_last_export_ok.get(self.name):
            self.app._co2_csv_state_led(self.name, "#3b82f6")
        else:
            self.app._co2_csv_state_led(self.name, "red")

        ttk.Button(co2_box, text="Gráfico caudal CO2", command=lambda: self.app.open_flow_plot(self.name)).grid(
            row=4, column=0, columnspan=3, sticky="ew", padx=2, pady=(2, 4)
        )

        # CSV CO2 FILTRADO
        co2f_box = ttk.LabelFrame(self, text="CSV CO2 FILTRADO")
        co2f_box.grid(row=10, column=0, padx=4, pady=(2, 4), sticky="ew")
        co2f_box.columnconfigure(1, weight=1)

        ttk.Label(co2f_box, text="Carpeta:").grid(row=0, column=0, sticky="e", padx=(4, 2), pady=2)
        ttk.Entry(co2f_box, textvariable=self.app.co2f_csv_dir[self.name]).grid(row=0, column=1, sticky="ew", pady=2)
        ttk.Button(co2f_box, text="...", width=3, command=lambda: self.app.co2f_pick_dir(self.name)).grid(
            row=0, column=2, sticky="w", padx=2
        )

        ttk.Label(co2f_box, text="Archivo:").grid(row=1, column=0, sticky="e", padx=(4, 2), pady=2)
        ttk.Entry(co2f_box, textvariable=self.app.co2f_csv_name[self.name]).grid(row=1, column=1, sticky="ew", pady=2)

        btn_co2f_row = ttk.Frame(co2f_box)
        btn_co2f_row.grid(row=2, column=0, columnspan=3, sticky="ew", pady=(4, 2))
        btn_co2f_row.columnconfigure((0, 1, 2, 3), weight=1)
        ttk.Button(btn_co2f_row, text="Inicio/Reanudar", command=lambda: self.app.co2f_csv_start(self.name)).grid(
            row=0, column=0, padx=2, sticky="ew"
        )
        ttk.Button(btn_co2f_row, text="Pausar/Detener", command=lambda: self.app.co2f_csv_pause(self.name)).grid(
            row=0, column=1, padx=2, sticky="ew"
        )
        ttk.Button(btn_co2f_row, text="Exportar CSV", command=lambda: self.app.co2f_csv_export(self.name)).grid(
            row=0, column=2, padx=2, sticky="ew"
        )
        ttk.Button(btn_co2f_row, text="Borrar/Reiniciar", command=lambda: self.app.co2f_csv_restart(self.name)).grid(
            row=0, column=3, padx=2, sticky="ew"
        )

        state_co2f = ttk.Frame(co2f_box)
        state_co2f.grid(row=3, column=0, columnspan=3, sticky="w", pady=(2, 4))
        ttk.Label(state_co2f, text="Estado:").grid(row=0, column=0, sticky="w")
        led_co2f = Led(state_co2f)
        led_co2f.widget().grid(row=0, column=1, sticky="w", padx=(4, 12))
        self.app._co2f_csv_register_led(self.name, led_co2f)
        if self.app.co2f_csv_running.get(self.name):
            self.app._co2f_csv_state_led(self.name, "#22c55e")
        elif self.app.co2f_csv_paused.get(self.name):
            self.app._co2f_csv_state_led(self.name, "#eab308")
        elif self.app.co2f_csv_last_export_ok.get(self.name):
            self.app._co2f_csv_state_led(self.name, "#3b82f6")
        else:
            self.app._co2f_csv_state_led(self.name, "red")

        ttk.Button(
            co2f_box,
            text="Gráfico caudal CO2 FILTRADO",
            command=lambda: self.app.open_flow_plot_filtered(self.name),
        ).grid(row=4, column=0, columnspan=3, sticky="ew", padx=2, pady=(2, 4))

    # --------- Forzados y LEDs ----------
    def _sync_leds(self):
        self.led_cold_in.set_on(self.cold_in)
        self.led_hot_in.set_on(self.hot_in)

    def _update_manual_nut_button(self):
        if self.manual_nut_on:
            self.btn_manual_nut.configure(text="Bomba manual ON")
        else:
            self.btn_manual_nut.configure(text="Bomba manual OFF")

    def _can_force(self):
        return self.manual_mode.get()

    def _apply_entry_float(self, entry_var, current_text, label, min_val=None):
        raw = (entry_var.get() or "").strip()
        if not raw:
            messagebox.showerror("Valor inválido", f"{label}: ingresa un número.")
            entry_var.set(current_text)
            return None
        raw = raw.replace(",", ".")
        try:
            value = float(raw)
        except Exception:
            messagebox.showerror("Valor inválido", f"{label}: '{raw}' no es un número.")
            entry_var.set(current_text)
            return None
        if min_val is not None and value < min_val:
            messagebox.showerror("Valor inválido", f"{label}: debe ser ≥ {min_val}.")
            entry_var.set(current_text)
            return None
        return value

    def apply_sp(self):
        current_text = f"{self.sp.get():.1f}"
        value = self._apply_entry_float(self.sp_entry, current_text, "Setpoint")
        if value is None:
            return
        self.sp.set(value)
        self.sp_entry.set(f"{value:.1f}")

    def apply_band(self):
        current_text = f"{self.band.get():.2f}"
        value = self._apply_entry_float(self.band_entry, current_text, "Banda", min_val=0.05)
        if value is None:
            return
        self.band.set(value)
        self.band_entry.set(f"{value:.2f}")

    def apply_freq(self):
        current_text = f"{self.freq_nut.get():.1f}"
        value = self._apply_entry_float(self.freq_entry, current_text, "Frecuencia", min_val=0.0)
        if value is None:
            return
        self.freq_nut.set(value)
        self.freq_entry.set(f"{value:.1f}")

    def forzar_frio(self):
        if not self._can_force():
            return
        self.cold_in = True
        self.hot_in = False
        self._apply_relays()
        self._sync_leds()

    def forzar_caliente(self):
        if not self._can_force():
            return
        self.hot_in = True
        self.cold_in = False
        self._apply_relays()
        self._sync_leds()

    def cerrar_todo(self):
        self.cold_in = False
        self.hot_in = False
        self._apply_relays()
        self._sync_leds()

    def stop_all(self):
        self.manual_mode.set(True)
        self.cold_in = False
        self.hot_in = False
        self.nut_running_until = None
        self.manual_nut_on = False
        self._apply_nutricion_state(False)
        self._apply_relays()
        self._sync_leds()
        self._update_manual_nut_button()

    def _apply_relays(self):
        if self.cold_in:
            self.hw.relay_on(self.relay_cold)
        else:
            self.hw.relay_off(self.relay_cold)
        if self.hot_in:
            self.hw.relay_on(self.relay_hot)
        else:
            self.hw.relay_off(self.relay_hot)

    def toggle_manual_nut(self):
        self.manual_nut_on = not self.manual_nut_on
        self._update_manual_nut_button()
        tnow = now()
        schedule_active = bool(self.nut_running_until and tnow < self.nut_running_until)
        self._apply_nutricion_state(schedule_active or self.manual_nut_on)

    # -------------- Calendarios --------------
    def edit_cal_sp(self):
        dlg = DateCalendarDialog(
            self.app,
            title_label=f"Calendario de Setpoint – {self.name}",
            value_label="Setpoint (°C):",
            value_type=float,
            initial=self.cal_sp,
            import_callback=lambda: self._import_calendar(value_type=float),
        )
        self.app.wait_window(dlg)
        if dlg.data is not None:
            self.cal_sp = dlg.data

    def edit_cal_nut(self):
        dlg = DateCalendarDialog(
            self.app,
            title_label=f"Calendario de Nutrición – {self.name}",
            value_label="Duración (seg):",
            value_type=float,
            initial=self.cal_nut,
            import_callback=lambda: self._import_calendar(value_type=float),
        )
        self.app.wait_window(dlg)
        if dlg.data is not None:
            self.cal_nut = dlg.data

    def _import_calendar(self, value_type=float):
        path = filedialog.askopenfilename(
            title="Importar calendario (CSV/Excel)",
            filetypes=[
                ("CSV", "*.csv"),
                ("Excel", "*.xlsx *.xls"),
                ("Todos", "*.*"),
            ],
        )
        _restore_focus(self)
        if not path:
            return None
        try:
            data = _load_calendar_file(path, value_type=value_type)
            if not data:
                messagebox.showwarning("Importar calendario", "El archivo no tiene filas válidas (fecha, hora, valor).")
                return None
            return data
        except Exception as e:
            messagebox.showerror("Importar calendario", f"No se pudo importar el archivo.\n{e}")
            return None

    def _apply_nutricion_state(self, should_run: bool):
        if should_run and not self._nut_led_on:
            self.hw.start_stepper(self.stepper_name, self.freq_nut.get())
        elif not should_run and self._nut_led_on:
            self.hw.stop_stepper(self.stepper_name)
        self._nut_led_on = should_run
        self.led_nut.set_on(self._nut_led_on)

    # ---------------- CSV --------------------
    def pick_dir(self):
        d = filedialog.askdirectory(title="Elegir carpeta de trabajo CSV")
        _restore_focus(self)
        if d:
            self.csv_dir.set(d)
            os.makedirs(d, exist_ok=True)

    def _csv_path(self):
        name = self.csv_name.get().strip() or f"{self.name}.csv"
        if not name.lower().endswith(".csv"):
            name += ".csv"
        return os.path.join(self.csv_dir.get(), name)

    def _csv_state_led(self, color):
        self.led_csv.set_color(color)

    def csv_start(self):
        self._csv_running = True
        self._csv_paused = False
        self._csv_last_export_ok = False
        self._csv_state_led("#22c55e")

    def csv_pause(self):
        self._csv_running = False
        self._csv_paused = True
        self._csv_state_led("#eab308")

    def csv_export(self):
        if self._csv_running:
            messagebox.showerror("Exportar", "Detén o pausa el CSV antes de exportar.")
            return
        src = self._csv_path()
        if not os.path.exists(src):
            messagebox.showerror("Exportar", f"No existe {src}")
            return
        dst_dir = filedialog.askdirectory(title="Seleccionar carpeta de destino")
        _restore_focus(self)
        if not dst_dir:
            return
        try:
            dst = os.path.join(dst_dir, os.path.basename(src))
            with open(src, "r", encoding="utf-8") as fsrc, open(dst, "w", encoding="utf-8", newline="") as fdst:
                fdst.write(fsrc.read())
            self._csv_last_export_ok = True
            self._csv_state_led("#3b82f6")
            messagebox.showinfo("Exportar", f"Archivo exportado a:\n{dst}")
        except Exception as e:
            messagebox.showerror("Exportar", f"No se pudo exportar.\n{e}")

    def csv_restart(self):
        self._csv_running = False
        self._csv_paused = False
        path = self._csv_path()
        try:
            if os.path.exists(path):
                os.remove(path)
            self._csv_state_led("#ef4444")
            messagebox.showinfo("CSV", f"Archivo reiniciado:\n{path}")
        except Exception as e:
            messagebox.showerror("CSV", f"No se pudo reiniciar.\n{e}")

    def _csv_write_row(self):
        row = {
            "timestamp": now_str(),
            "fermentador": self.name,
            "T": f"{self.t:.1f}",
            "SP": f"{float(self.sp.get()):.2f}",
            "banda": f"{float(self.band.get()):.2f}",
            "cold": int(self.cold_in),
            "hot": int(self.hot_in),
            "nutricion_activa": int(self._nut_led_on),
            "freq_nut": f"{float(self.freq_nut.get()):.1f}",
        }

        if self._csv_running:
            ipath = self._csv_path()
            cabe = not os.path.exists(ipath)
            try:
                os.makedirs(os.path.dirname(ipath), exist_ok=True)
                with open(ipath, "a", newline="", encoding="utf-8") as f:
                    w = csv.DictWriter(f, fieldnames=list(row.keys()))
                    if cabe:
                        w.writeheader()
                    w.writerow(row)
            except Exception as e:
                messagebox.showerror("CSV", f"No se pudo escribir en {ipath}\n{e}")

        bpath = self.get_backup_path()
        bdir = os.path.dirname(bpath) or "."
        os.makedirs(bdir, exist_ok=True)

        backup_fields = [
            "timestamp",
            "fermentador",
            "T",
            "SP",
            "banda",
            "cold",
            "hot",
            "nutricion_activa",
            "freq_nut",
        ]
        write_header = not os.path.exists(bpath) or os.path.getsize(bpath) == 0

        try:
            with open(bpath, "a", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=backup_fields, extrasaction="ignore")
                if write_header:
                    w.writeheader()
                w.writerow(row)
        except Exception as e:
            messagebox.showerror("Backup global", f"No se pudo escribir en {bpath}\n{e}")

    # ----------------- Simulación de temperatura -----------------
    def _simulate_temp(self, dt_seconds: float):
        if dt_seconds <= 0:
            return

        sp_obj = float(self.sp.get())

        ambient_pull = (self._sim_ambient - self.t) * 0.0008
        ferment_target = max(sp_obj, self._sim_ambient + 4.0)
        ferment_heat = (ferment_target - self.t) * 0.018

        heating = 0.22 if self.hot_in else 0.0
        cooling = -0.28 if self.cold_in else 0.0

        ruido = random.uniform(-0.008, 0.008)
        delta = (ambient_pull + ferment_heat + heating + cooling + ruido) * dt_seconds
        self.t = max(-5.0, min(40.0, self.t + delta))

    # ----------------- Loop del proceso -----------------
    def update_process(self):
        tnow = now()
        dt_seconds = max(0.001, (tnow - self._last_update).total_seconds())
        self._last_update = tnow

        sp_cal = None
        if not self.manual_mode.get():
            sp_cal = sp_from_date_calendar(self.cal_sp, tnow, default=None)
            if sp_cal is not None:
                try:
                    sp_val = float(sp_cal)
                    self.sp.set(sp_val)
                    self.sp_entry.set(f"{sp_val:.1f}")
                except Exception:
                    pass

        current_min = tnow.strftime("%Y-%m-%d %H:%M")
        if self._last_min != current_min:
            doses = nut_fire_for_minute(self.cal_nut, tnow)
            if doses:
                dur_total = sum(float(d) for d in doses if float(d) > 0)
                if dur_total > 0:
                    self.nut_running_until = tnow + dt.timedelta(seconds=dur_total)
                    self.hw.start_stepper(self.stepper_name, self.freq_nut.get())
            self._last_min = current_min

        schedule_active = False
        if self.nut_running_until and tnow < self.nut_running_until:
            schedule_active = True
        else:
            self.nut_running_until = None
        self._apply_nutricion_state(schedule_active or self.manual_nut_on)
        self.app._record_nut_sample(self.name, tnow, self._nut_led_on)

        if self.hw.sim:
            self._simulate_temp(dt_seconds)
        else:
            self.t = self.hw.read_temp_ds18b20(index=int(self.name[1:]) - 1)
        self.t_str.set(f"{self.t:.1f}")
        samples = self.app.flow_samples.get(self.name, [])
        if samples:
            self.flow_str.set(f"{samples[-1][1]:.2f} SCCM")

        if not self.manual_mode.get():
            sp = float(self.sp.get())
            band = max(0.05, float(self.band.get()))
            # control frío
            if self.cold_in:
                if self.t <= sp - band:
                    self.cold_in = False
            else:
                if self.t >= sp + band:
                    self.cold_in = True
            # control caliente
            if self.hot_in:
                if self.t >= sp + band:
                    self.hot_in = False
            else:
                if self.t <= sp - band:
                    self.hot_in = True
            if not self.cold_in and not self.hot_in:
                self.cerrar_todo()
            self._apply_relays()
            self._sync_leds()

        self._csv_write_row()


# ------------------------------------------------------------
# Ventanas de gráficos (carga asíncrona)
# ------------------------------------------------------------


class RealTimePlotWindow:
    def __init__(self, app, fermenter=None):
        self.app = app
        self.fermenter = fermenter
        self.top = tk.Toplevel(app)
        title_suffix = f" – {fermenter}" if fermenter else " (todos)"
        self.top.title(f"Gráfico en tiempo real{title_suffix}")

        self.current_window_hours = None
        self._loading = False
        self._load_id = 0
        self._refresh_job = None

        # UI
        control = ttk.Frame(self.top)
        control.pack(side="top", fill="x", padx=8, pady=4)
        ttk.Label(control, text="Rango eje X:").pack(side="left")

        def set_window(h):
            self.current_window_hours = h
            self.request_data()

        for label, hours in [
            ("Tiempo real", None),
            ("1 h", 1),
            ("12 h", 12),
            ("24 h", 24),
            ("48 h", 48),
            ("72 h", 72),
            ("1 semana", 24 * 7),
            ("2 semanas", 24 * 14),
        ]:
            ttk.Button(control, text=label, command=lambda h=hours: set_window(h)).pack(side="left", padx=2)

        self.status = ttk.Label(self.top, text="Cargando datos…")
        self.status.pack(anchor="w", padx=8, pady=4)

        # Matplotlib
        import matplotlib.pyplot as plt  # type: ignore
        from matplotlib import dates as mdates  # type: ignore
        from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg  # type: ignore

        self.fig, (self.ax_temp, self.ax_nut) = plt.subplots(
            2,
            1,
            sharex=True,
            figsize=(9, 5),
            gridspec_kw={"height_ratios": [3, 1], "hspace": 0.1},
        )
        self.canvas = FigureCanvasTkAgg(self.fig, master=self.top)
        self.canvas.get_tk_widget().pack(fill="both", expand=True)

        self.ax_nut.xaxis.set_major_formatter(mdates.DateFormatter("%m-%d %H:%M"))

        self.top.protocol("WM_DELETE_WINDOW", self.close)
        self.app._plot_windows.append(self.top)

        self.request_data()

    def close(self):
        if self._refresh_job is not None:
            try:
                self.top.after_cancel(self._refresh_job)
            except Exception:
                pass
            self._refresh_job = None
        if self.top in self.app._plot_windows:
            self.app._plot_windows.remove(self.top)
        self.top.destroy()

    def request_data(self):
        if self._loading:
            return
        self._loading = True
        self._load_id += 1
        req_id = self._load_id

        days_window = 3650 if self.current_window_hours is None else (self.current_window_hours / 24.0)
        path = self.app.get_backup_path()

        def worker():
            data = self.app._read_recent_backup(days=days_window, fermenter=self.fermenter, path=path)
            self.app.after(0, lambda: self._on_data(req_id, data))

        threading.Thread(target=worker, daemon=True).start()

    def _on_data(self, req_id, data):
        if not self.top.winfo_exists() or req_id != self._load_id:
            return
        self._loading = False

        self.ax_temp.clear()
        self.ax_nut.clear()

        if not data:
            self.status.config(text="Sin datos recientes en el backup.")
        else:
            temps_all = []
            for ferm, series in sorted(data.items()):
                if not series["ts"]:
                    continue
                self.ax_temp.plot(series["ts"], series["t"], label=f"{ferm} T")
                self.ax_temp.plot(series["ts"], series["sp"], linestyle="--", label=f"{ferm} SP")
                temps_all.extend(series["t"])
                nut = series.get("nut", [])
                if nut and any(nut):
                    self.ax_nut.step(series["ts"], nut, where="post", color="red", alpha=0.8, label=f"{ferm} Nutrición")

            self.ax_temp.set_title("Temperatura vs. tiempo")
            self.ax_temp.set_ylabel("°C")

            if temps_all:
                tmin = min(temps_all)
                tmax = max(temps_all)
                pad = (tmax - tmin) * 0.1 if tmax != tmin else 1.0
                self.ax_temp.set_ylim(tmin - pad, tmax + pad)

            self.ax_nut.set_ylabel("Nutrición ON=1")
            self.ax_nut.set_ylim(-0.1, 1.1)
            self.ax_nut.set_yticks([0, 1])
            self.ax_nut.set_xlabel("Fecha y hora")

            lines1, labels1 = self.ax_temp.get_legend_handles_labels()
            lines2, labels2 = self.ax_nut.get_legend_handles_labels()
            if lines1 or lines2:
                self.ax_temp.legend(lines1 + lines2, labels1 + labels2, loc="upper left")

            if self.current_window_hours is None:
                all_ts = []
                for series in data.values():
                    all_ts.extend(series["ts"])
                if all_ts:
                    right = max(all_ts)
                    left = min(all_ts)
                    if left == right:
                        left = right - dt.timedelta(minutes=1)
                    self.ax_temp.set_xlim(left, right)
                self.status.config(text="Fuente: backup global (tiempo real)")
            else:
                right = now()
                left = right - dt.timedelta(hours=self.current_window_hours)
                self.ax_temp.set_xlim(left, right)

                if self.current_window_hours >= 24:
                    rango = f"últimos {int(self.current_window_hours // 24)} días"
                else:
                    rango = f"últimas {self.current_window_hours} horas"
                self.status.config(text=f"Fuente: backup global ({rango})")

        self.fig.autofmt_xdate()
        self.canvas.draw_idle()

        # Programar siguiente actualización
        self._refresh_job = self.top.after(5000, self.request_data)


class FlowPlotWindow:
    def __init__(self, app, fermenter):
        self.app = app
        self.fermenter = fermenter
        self.reader = app.flow_readers.get(fermenter)

        self.top = tk.Toplevel(app)
        self.top.title(f"Caudal CO2 en tiempo real – {fermenter}")

        header = ttk.Frame(self.top)
        header.pack(fill="x", padx=8, pady=(8, 4))
        ttk.Label(header, text="Caudalímetro CO2", font=("Segoe UI", 12, "bold")).pack(side="left")
        if self.reader is not None:
            mode_text = "SIMULADOR" if self.reader.sim else "HARDWARE"
        else:
            mode_text = "N/D"
        ttk.Label(header, text=mode_text).pack(side="right")

        stats = ttk.Frame(self.top)
        stats.pack(fill="x", padx=8, pady=(0, 6))
        stats.grid_columnconfigure(1, weight=1)

        self.flow_var = tk.StringVar(value="0.00 SCCM")
        self.status_var = tk.StringVar(value="Esperando...")
        self.next_var = tk.StringVar(value="--:--:--")

        ttk.Label(stats, text="Caudal:").grid(row=0, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.flow_var).grid(row=0, column=1, sticky="w")
        ttk.Label(stats, text="Estado:").grid(row=1, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.status_var).grid(row=1, column=1, sticky="w")
        ttk.Label(stats, text="Siguiente muestra:").grid(row=2, column=0, sticky="w")
        ttk.Label(stats, textvariable=self.next_var).grid(row=2, column=1, sticky="w")
        ttk.Label(stats, text="SCCM = cm3/min", font=("Segoe UI", 9, "italic")).grid(
            row=3, column=0, columnspan=2, sticky="w", pady=(4, 0)
        )

        control = ttk.Frame(self.top)
        control.pack(fill="x", padx=8, pady=(0, 6))
        ttk.Label(control, text="Escala:").pack(side="left")

        self.current_window_hours = PLOT_WINDOW_HOURS if PLOT_WINDOW_HOURS > 0 else None

        def set_window(h):
            self.current_window_hours = h
            self.request_flow_data()
            self.request_nut_data()
            self.refresh_plot()

        for label, hours in [
            ("Tiempo real", None),
            ("1 h", 1),
            ("12 h", 12),
            ("24 h", 24),
            ("48 h", 48),
            ("72 h", 72),
            ("1 semana", 24 * 7),
            ("2 semanas", 24 * 14),
        ]:
            ttk.Button(control, text=label, command=lambda h=hours: set_window(h)).pack(side="left", padx=2)

        # Matplotlib
        import matplotlib.pyplot as plt  # type: ignore
        from matplotlib import dates as mdates  # type: ignore
        from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg  # type: ignore

        self.fig, (self.ax_flow, self.ax_nut) = plt.subplots(
            2,
            1,
            sharex=True,
            figsize=(9, 7),
            gridspec_kw={"height_ratios": [3, 1], "hspace": 0.1},
        )
        self.line_flow, = self.ax_flow.plot([], [], color="#2563eb", linewidth=2, label="Caudal")
        self.line_nut = self.ax_nut.step([], [], where="post", color="red", alpha=0.8, label="Nutrición")[0]
        self.ax_flow.set_title("Caudal CO2 (SCCM)")
        self.ax_flow.set_ylabel("SCCM")
        self.ax_flow.grid(True, alpha=0.2)
        self.ax_nut.set_ylabel("Nutrición ON=1")
        self.ax_nut.set_ylim(-0.1, 1.1)
        self.ax_nut.set_yticks([0, 1])
        self.ax_nut.set_xlabel("Fecha y hora")
        self.ax_nut.grid(True, alpha=0.2)
        self.ax_nut.xaxis.set_major_formatter(mdates.DateFormatter("%m-%d %H:%M"))

        self.canvas = FigureCanvasTkAgg(self.fig, master=self.top)
        self.canvas.get_tk_widget().pack(fill="both", expand=True)

        self._refresh_job = None
        self._nut_refresh_job = None
        self._nut_loading = False
        self._nut_load_id = 0
        self.nut_cache = []
        self._flow_loading = False
        self._flow_load_id = 0
        self.flow_cache = []

        self.top.protocol("WM_DELETE_WINDOW", self.close)
        self.app._plot_windows.append(self.top)

        self.request_flow_data()
        self.request_nut_data()
        self.refresh_loop()

    def close(self):
        if self._refresh_job is not None:
            try:
                self.top.after_cancel(self._refresh_job)
            except Exception:
                pass
            self._refresh_job = None
        if self._nut_refresh_job is not None:
            try:
                self.top.after_cancel(self._nut_refresh_job)
            except Exception:
                pass
            self._nut_refresh_job = None
        if self.top in self.app._plot_windows:
            self.app._plot_windows.remove(self.top)
        if self.app._flow_plot_windows.get(self.fermenter) is self.top:
            self.app._flow_plot_windows.pop(self.fermenter, None)
        self.top.destroy()

    def request_flow_data(self):
        if self._flow_loading:
            return
        self._flow_loading = True
        self._flow_load_id += 1
        req_id = self._flow_load_id

        hours = self.current_window_hours
        days_window = 3650 if hours is None else (hours / 24.0)
        path = self.app.get_co2_backup_path()

        def worker():
            data = self.app._read_recent_co2_backup(days=days_window, fermenter=self.fermenter, path=path)
            series = data.get(self.fermenter) if data else None
            self.app.after(0, lambda: self._on_flow_data(req_id, series))

        threading.Thread(target=worker, daemon=True).start()

    def _on_flow_data(self, req_id, series):
        if not self.top.winfo_exists() or req_id != self._flow_load_id:
            return
        self._flow_loading = False
        if series and series.get("ts"):
            self.flow_cache = list(zip(series["ts"], series.get("flow", [])))
        else:
            self.flow_cache = []

    def request_nut_data(self):
        if self._nut_loading:
            return
        self._nut_loading = True
        self._nut_load_id += 1
        req_id = self._nut_load_id

        hours = self.current_window_hours
        days_window = 3650 if hours is None else (hours / 24.0)
        path = self.app.get_backup_path()

        def worker():
            data = self.app._read_recent_backup(days=days_window, fermenter=self.fermenter, path=path)
            series = data.get(self.fermenter) if data else None
            self.app.after(0, lambda: self._on_nut_data(req_id, series))

        threading.Thread(target=worker, daemon=True).start()

    def _on_nut_data(self, req_id, series):
        if not self.top.winfo_exists() or req_id != self._nut_load_id:
            return
        self._nut_loading = False
        if series and series.get("ts"):
            self.nut_cache = list(zip(series["ts"], series.get("nut", [])))
        else:
            self.nut_cache = []

        # refrescar cache cada 15s
        self._nut_refresh_job = self.top.after(15000, self.request_nut_data)

    def refresh_loop(self):
        if not self.top.winfo_exists():
            return
        self.refresh_plot()
        self.refresh_stats()
        self.refresh_countdown()
        self._refresh_job = self.top.after(1000, self.refresh_loop)

    def _combined_flow_samples(self):
        samples = list(self.app.flow_samples.get(self.fermenter, []))
        if not self.flow_cache:
            return samples
        sample_ts = {ts for ts, *_ in samples}
        combined = [(ts, flow, None, None, "BACKUP") for ts, flow in self.flow_cache if ts not in sample_ts]
        combined.extend(samples)
        combined.sort(key=lambda row: row[0])
        return combined

    def _current_nut_state(self):
        for panel in self.app.ferms:
            if panel.name == self.fermenter:
                return 1 if panel._nut_led_on else 0
        return None

    def _combined_nut_samples(self, left, right):
        points = []
        for source in (self.nut_cache, self.app.nut_samples.get(self.fermenter, [])):
            for ts, val in source:
                if left <= ts <= right:
                    points.append((ts, val))
        if points:
            points.sort(key=lambda row: row[0])
            dedup = []
            for ts, val in points:
                if dedup and ts == dedup[-1][0]:
                    dedup[-1] = (ts, val)
                else:
                    dedup.append((ts, val))
            points = dedup
        current_state = self._current_nut_state()
        if current_state is not None:
            if not points or points[-1][0] < right:
                points.append((right, current_state))
        return points

    def refresh_plot(self):
        samples = self._combined_flow_samples()
        if not samples:
            self.line_flow.set_data([], [])
            self.line_nut.set_data([], [])
            self.canvas.draw_idle()
            return

        if self.current_window_hours is None:
            windowed = samples
            right = windowed[-1][0]
            left = windowed[0][0]
            if left == right:
                left = right - dt.timedelta(seconds=max(1, self.app.flow_sample_period[self.fermenter]))
            right = max(right, now())
        else:
            right = now()
            left = right - dt.timedelta(hours=self.current_window_hours)
            windowed = [row for row in samples if left <= row[0] <= right]
            if not windowed:
                self.line_flow.set_data([], [])
                self.line_nut.set_data([], [])
                self.ax_flow.set_xlim(left, right)
                self.canvas.draw_idle()
                return

        times = [ts for ts, _, _, _, _ in windowed]
        values = [flow for _, flow, _, _, _ in windowed]
        self.line_flow.set_data(times, values)
        self.ax_flow.set_xlim(left, right)

        vmin = min(values)
        vmax = max(values)
        pad = (vmax - vmin) * 0.1 if vmax != vmin else 1.0
        self.ax_flow.set_ylim(vmin - pad, vmax + pad)

        nut_points = self._combined_nut_samples(left, right)
        if nut_points:
            nut_times = [ts for ts, _ in nut_points]
            nut_values = [val for _, val in nut_points]
            self.line_nut.set_data(nut_times, nut_values)
        else:
            self.line_nut.set_data([], [])

        self.fig.autofmt_xdate()
        self.canvas.draw_idle()

    def refresh_stats(self):
        samples = self.app.flow_samples.get(self.fermenter, [])
        if not samples:
            self.flow_var.set("0.00 SCCM")
            self.status_var.set("Esperando...")
            return
        _, flow, _current_ma, _voltage, status = samples[-1]
        self.flow_var.set(f"{flow:0.2f} SCCM")
        self.status_var.set(status)

    def refresh_countdown(self):
        next_sample = self.app.flow_next_sample.get(self.fermenter)
        if next_sample is None:
            self.next_var.set("--:--:--")
            return
        delta = next_sample - now()
        if delta.total_seconds() < 0:
            self.next_var.set("00:00:00")
        else:
            total = int(delta.total_seconds())
            hh = total // 3600
            mm = (total % 3600) // 60
            ss = total % 60
            self.next_var.set(f"{hh:02d}:{mm:02d}:{ss:02d}")


class FlowPlotFilteredWindow(FlowPlotWindow):
    def __init__(self, app, fermenter):
        self._y_axis_mode = "g_l_h"
        self._x_axis_mode = "date"
        self._btn_y_axis = None
        self._btn_x_axis = None
        super().__init__(app, fermenter)
        self.top.title(f"Caudal CO2 filtrado en tiempo real – {fermenter}")
        self.line_flow.set_color("#0f766e")
        self._build_extra_controls()
        self._update_toggle_buttons()
        self.canvas.draw_idle()

    def _build_extra_controls(self):
        try:
            canvas_widget = self.canvas.get_tk_widget()
        except Exception:
            return
        extra = ttk.Frame(self.top)
        extra.pack(fill="x", padx=8, pady=(0, 6), before=canvas_widget)
        self._btn_y_axis = ttk.Button(extra, command=self._toggle_y_axis_mode)
        self._btn_y_axis.pack(side="left", padx=(0, 6))
        self._btn_x_axis = ttk.Button(extra, command=self._toggle_x_axis_mode)
        self._btn_x_axis.pack(side="left")

    def _update_toggle_buttons(self):
        if self._btn_y_axis is not None:
            if self._y_axis_mode == "sccm":
                self._btn_y_axis.configure(text="Eje Y: SCCM (cambiar a g/(L*h))")
            else:
                self._btn_y_axis.configure(text="Eje Y: g/(L*h) (cambiar a SCCM)")
        if self._btn_x_axis is not None:
            if self._x_axis_mode == "date":
                self._btn_x_axis.configure(text="Eje X: Fecha (cambiar a horas)")
            else:
                self._btn_x_axis.configure(text="Eje X: Horas (cambiar a fecha)")

    def _toggle_y_axis_mode(self):
        self._y_axis_mode = "g_l_h" if self._y_axis_mode == "sccm" else "sccm"
        self._update_toggle_buttons()
        self.refresh_stats()
        self.refresh_plot()

    def _toggle_x_axis_mode(self):
        self._x_axis_mode = "hours" if self._x_axis_mode == "date" else "date"
        self._update_toggle_buttons()
        self.refresh_plot()

    def _flow_value_for_y_axis(self, flow_sccm):
        if self._y_axis_mode == "g_l_h":
            return flow_sccm_to_co2_g_l_h_plot(flow_sccm)
        return float(flow_sccm)

    def _format_flow_stats(self, flow_sccm):
        if self._y_axis_mode == "g_l_h":
            return f"{flow_sccm_to_co2_g_l_h_plot(flow_sccm):0.4f} g/(L*h)"
        return f"{float(flow_sccm):0.2f} SCCM"

    def close(self):
        if self.app._flow_plot_filtered_windows.get(self.fermenter) is self.top:
            self.app._flow_plot_filtered_windows.pop(self.fermenter, None)
        super().close()

    def request_flow_data(self):
        if self._flow_loading:
            return
        self._flow_loading = True
        self._flow_load_id += 1
        req_id = self._flow_load_id

        hours = self.current_window_hours
        days_window = 3650 if hours is None else (hours / 24.0)
        path = self.app.get_co2_backup_path()

        def worker():
            data = self.app._read_recent_co2_backup(days=days_window, fermenter=self.fermenter, path=path)
            series = data.get(self.fermenter) if data else None
            self.app.after(0, lambda: self._on_flow_data(req_id, series))

        threading.Thread(target=worker, daemon=True).start()

    def _on_flow_data(self, req_id, series):
        if not self.top.winfo_exists() or req_id != self._flow_load_id:
            return
        self._flow_loading = False
        if series and series.get("ts"):
            values = series.get("flow_filt", []) or series.get("flow", [])
            self.flow_cache = list(zip(series["ts"], values))
        else:
            self.flow_cache = []

    def _combined_flow_samples(self):
        samples = list(self.app.flow_samples_filt.get(self.fermenter, []))
        if not self.flow_cache:
            return [(ts, flow, None, None, status) for ts, flow, status, _sp in samples]
        sample_ts = {ts for ts, *_ in samples}
        combined = [(ts, flow, None, None, "BACKUP") for ts, flow in self.flow_cache if ts not in sample_ts]
        combined.extend((ts, flow, None, None, status) for ts, flow, status, _sp in samples)
        combined.sort(key=lambda row: row[0])
        return combined

    def refresh_stats(self):
        samples = self.app.flow_samples_filt.get(self.fermenter, [])
        if not samples:
            self.flow_var.set("0.0000 g/(L*h)" if self._y_axis_mode == "g_l_h" else "0.00 SCCM")
            self.status_var.set("Esperando...")
            return
        _ts, flow, status, _is_spike = samples[-1]
        self.flow_var.set(self._format_flow_stats(flow))
        self.status_var.set(status)

    def refresh_plot(self):
        samples = self._combined_flow_samples()
        if not samples:
            self.line_flow.set_data([], [])
            self.line_nut.set_data([], [])
            self.canvas.draw_idle()
            return

        if self.current_window_hours is None:
            windowed = samples
            right = windowed[-1][0]
            left = windowed[0][0]
            if left == right:
                left = right - dt.timedelta(seconds=max(1, self.app.flow_sample_period[self.fermenter]))
            right = max(right, now())
        else:
            right = now()
            left = right - dt.timedelta(hours=self.current_window_hours)
            windowed = [row for row in samples if left <= row[0] <= right]
            if not windowed:
                self.line_flow.set_data([], [])
                self.line_nut.set_data([], [])
                if self._x_axis_mode == "hours":
                    x_span_h = max((right - left).total_seconds() / 3600.0, 1e-6)
                    self.ax_flow.set_xlim(0.0, x_span_h)
                    from matplotlib import ticker as mticker  # type: ignore

                    self.ax_nut.xaxis.set_major_formatter(mticker.FormatStrFormatter("%.2f"))
                    self.ax_nut.set_xlabel("Horas")
                else:
                    from matplotlib import dates as mdates  # type: ignore

                    self.ax_flow.set_xlim(left, right)
                    self.ax_nut.xaxis.set_major_formatter(mdates.DateFormatter("%m-%d %H:%M"))
                    self.ax_nut.set_xlabel("Fecha y hora")
                self.canvas.draw_idle()
                return

        times_dt = [ts for ts, _, _, _, _ in windowed]
        values_sccm = [flow for _, flow, _, _, _ in windowed]
        values_y = [self._flow_value_for_y_axis(flow) for flow in values_sccm]

        if self._x_axis_mode == "hours":
            x_left_dt = left
            times_x = [(ts - x_left_dt).total_seconds() / 3600.0 for ts in times_dt]
            x_right = max((right - x_left_dt).total_seconds() / 3600.0, 1e-6)
            self.line_flow.set_data(times_x, values_y)
            self.ax_flow.set_xlim(0.0, x_right)
            self.ax_nut.set_xlabel("Horas")
            from matplotlib import ticker as mticker  # type: ignore

            self.ax_nut.xaxis.set_major_formatter(mticker.FormatStrFormatter("%.2f"))
        else:
            self.line_flow.set_data(times_dt, values_y)
            self.ax_flow.set_xlim(left, right)
            self.ax_nut.set_xlabel("Fecha y hora")
            from matplotlib import dates as mdates  # type: ignore

            self.ax_nut.xaxis.set_major_formatter(mdates.DateFormatter("%m-%d %H:%M"))

        if self._y_axis_mode == "g_l_h":
            self.ax_flow.set_title("Caudal CO2 filtrado (g/(L*h))")
            self.ax_flow.set_ylabel("g/(L*h)")
        else:
            self.ax_flow.set_title("Caudal CO2 filtrado (SCCM)")
            self.ax_flow.set_ylabel("SCCM")

        vmin = min(values_y)
        vmax = max(values_y)
        pad = (vmax - vmin) * 0.1 if vmax != vmin else (0.05 if self._y_axis_mode == "g_l_h" else 1.0)
        self.ax_flow.set_ylim(vmin - pad, vmax + pad)

        nut_points = self._combined_nut_samples(left, right)
        if nut_points:
            if self._x_axis_mode == "hours":
                x_left_dt = left
                nut_times = [(ts - x_left_dt).total_seconds() / 3600.0 for ts, _ in nut_points]
            else:
                nut_times = [ts for ts, _ in nut_points]
            nut_values = [val for _, val in nut_points]
            self.line_nut.set_data(nut_times, nut_values)
        else:
            self.line_nut.set_data([], [])

        if self._x_axis_mode == "date":
            self.fig.autofmt_xdate()
        self.canvas.draw_idle()


# ------------------------------------------------------------
# App principal
# ------------------------------------------------------------


class App(tk.Tk):
    def __init__(self):
        super().__init__()

        self.title("Panel de control – 3 Fermentadores (Lite)")
        screen_w = self.winfo_screenwidth()
        screen_h = self.winfo_screenheight()
        margin_w = 80
        margin_h = 140

        default_w, default_h = 1400, 780
        avail_w = max(1, screen_w - margin_w)
        avail_h = max(1, screen_h - margin_h)
        win_w = min(default_w, avail_w)
        win_h = min(default_h, avail_h)
        self.geometry(f"{win_w}x{win_h}")

        min_w = min(1200, avail_w)
        min_h = min(720, avail_h)
        self.minsize(min_w, min_h)

        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(0, weight=1)

        # Scroll principal
        main = ScrollableFrame(self)
        main.grid(row=0, column=0, sticky="nsew")
        main.inner.grid_columnconfigure((0, 1, 2), weight=1, uniform="col")

        self.hw = Hardware()
        self.flow_readers = {}
        self.flow_samples = {}
        self.flow_samples_filt = {}
        self.co2_filters = {}
        self.flow_next_sample = {}
        self.flow_sample_period = {}
        self.nut_samples = {}
        self.nut_last_state = {}
        self.co2_csv_dir = {}
        self.co2_csv_name = {}
        self.co2_csv_running = {}
        self.co2_csv_paused = {}
        self.co2_csv_last_export_ok = {}
        self._co2_csv_leds = {}
        self.co2f_csv_dir = {}
        self.co2f_csv_name = {}
        self.co2f_csv_running = {}
        self.co2f_csv_paused = {}
        self.co2f_csv_last_export_ok = {}
        self._co2f_csv_leds = {}

        default_channels = {"F1": 0, "F2": 1, "F3": 2}
        for name in ("F1", "F2", "F3"):
            addr_env = os.environ.get(f"ADS1115_ADDR_{name}", "").strip()
            ch_env = os.environ.get(f"ADS1115_CH_{name}", "").strip()
            gain_env = os.environ.get(f"ADS1115_GAIN_{name}", "").strip()
            addr = parse_int(addr_env, ADS1115_ADDR) if addr_env else ADS1115_ADDR
            default_ch = default_channels.get(name, ADS1115_CH)
            ch = parse_int(ch_env, default_ch) if ch_env else default_ch
            gain = parse_int(gain_env, ADS1115_GAIN) if gain_env else ADS1115_GAIN
            shunt = SHUNT_OHMS.get(name, DEFAULT_SHUNT_OHMS)
            reader = ADS1115Reader(addr, ch, gain, shunt)
            self.flow_readers[name] = reader
            self.flow_samples[name] = []
            self.flow_samples_filt[name] = []
            self.flow_next_sample[name] = None
            if SAMPLE_PERIOD_SEC is None:
                period = 1 if reader.sim else 10
            else:
                period = SAMPLE_PERIOD_SEC
            self.flow_sample_period[name] = period
            self.co2_filters[name] = CO2RealtimeFilter(
                dt_seconds=float(period),
                w_spike_seconds=W_SPIKE_SECONDS,
                k=K,
                min_abs_spike=MIN_ABS_SPIKE,
                tau_seconds=TAU_SECONDS,
                butter_order=BUTTER_ORDER,
            )
            self.nut_samples[name] = []
            self.nut_last_state[name] = None
            self.co2_csv_dir[name] = tk.StringVar(value=os.path.abspath("./Proceso"))
            # Nombre base pedido para CSV CO2 (se agrega .csv en _co2_csv_path si falta)
            self.co2_csv_name[name] = tk.StringVar(value=f"CO2_{name}")
            self.co2_csv_running[name] = False
            self.co2_csv_paused[name] = False
            self.co2_csv_last_export_ok[name] = False
            self.co2f_csv_dir[name] = tk.StringVar(value=os.path.abspath("./Proceso"))
            self.co2f_csv_name[name] = tk.StringVar(value=f"CO2_FILT_{name}")
            self.co2f_csv_running[name] = False
            self.co2f_csv_paused[name] = False
            self.co2f_csv_last_export_ok[name] = False
            os.makedirs(self.co2_csv_dir[name].get(), exist_ok=True)
            os.makedirs(self.co2f_csv_dir[name].get(), exist_ok=True)
        self._flow_plot_windows = {}
        self._flow_plot_filtered_windows = {}

        # ---------- LOGO CII ----------
        self.logo_img = None
        logo_path = os.path.join(ASSETS_DIR, "logo_cii.png")
        if os.path.exists(logo_path):
            try:
                pil_img = Image.open(logo_path)
                pil_img = pil_img.resize((160, 80))
                self.logo_img = ImageTk.PhotoImage(pil_img)
            except Exception as e:
                print(f"[UI] No se pudo cargar el logo {logo_path}: {e}")
        else:
            print(f"[UI] Logo no encontrado en: {logo_path}")

        # TOP BAR
        top_bar = ttk.Frame(main.inner)
        top_bar.grid(row=0, column=0, columnspan=3, sticky="ew", padx=12, pady=(10, 0))
        top_bar.grid_columnconfigure(0, weight=1)

        title_row = ttk.Frame(top_bar)
        title_row.grid(row=0, column=0, sticky="w")
        ttk.Label(title_row, text="Panel Fermentadores", font=("Segoe UI", 20, "bold")).pack(side="left")
        ttk.Label(title_row, text="  by Claudio Rodriguez", font=("Segoe UI", 12, "italic")).pack(side="left")

        sim_mode = self.hw.sim or self.hw.sim_gpio or not self.hw.ds_devices
        mode_text = f"Modo: {'SIMULADOR' if sim_mode else 'HARDWARE'}"
        ttk.Label(top_bar, text=mode_text).grid(row=1, column=0, sticky="w", pady=(4, 0))

        if self.logo_img is not None:
            logo_label = ttk.Label(top_bar, image=self.logo_img)
            logo_label.grid(row=0, column=1, rowspan=2, sticky="e", padx=(0, 10))

        # Backup global temperatura
        backup_frame = ttk.Frame(main.inner)
        backup_frame.grid(row=1, column=0, columnspan=3, sticky="ew", padx=12, pady=(4, 8))
        backup_frame.grid_columnconfigure(1, weight=1)

        self.backup_path = tk.StringVar(value=os.path.abspath("./Backup/backup_global_temperatura.csv"))
        ttk.Label(backup_frame, text="Backup global temperatura:").grid(row=0, column=0, sticky="w")
        ttk.Entry(backup_frame, textvariable=self.backup_path).grid(row=0, column=1, sticky="ew", padx=(4, 4))
        ttk.Button(backup_frame, text="Destino…", command=self.pick_backup).grid(row=0, column=2, padx=(4, 0))

        self.backup_co2_path = tk.StringVar(value=os.path.abspath("./Backup/backup_global_co2.csv"))
        ttk.Label(backup_frame, text="Backup global CO2:").grid(row=1, column=0, sticky="w", pady=(4, 0))
        ttk.Entry(backup_frame, textvariable=self.backup_co2_path).grid(
            row=1, column=1, sticky="ew", padx=(4, 4), pady=(4, 0)
        )
        ttk.Button(backup_frame, text="Destino…", command=self.pick_backup_co2).grid(
            row=1, column=2, padx=(4, 0), pady=(4, 0)
        )
        backup_btns = ttk.Frame(backup_frame)
        backup_btns.grid(row=2, column=0, columnspan=3, sticky="w", pady=(6, 0))
        ttk.Button(backup_btns, text="Borrar backup temperatura", command=self.clear_backup_temp).pack(
            side="left", padx=(0, 6)
        )
        ttk.Button(backup_btns, text="Borrar backup CO2", command=self.clear_backup_co2).pack(side="left")

        # Fermentadores (cada panel con borde)
        self.ferms = []
        for i in range(3):
            border = tk.Frame(
                main.inner,
                highlightthickness=1,
                highlightbackground="#444444",
                highlightcolor="#444444",
                bd=0,
            )
            border.grid(row=2, column=i, padx=8, pady=(4, 10), sticky="nsew")
            border.grid_columnconfigure(0, weight=1)

            panel = LightFermenterPanel(border, self, f"F{i+1}", self.hw, backup_path_getter=self.get_backup_path)
            panel.grid(row=0, column=0, sticky="nsew", padx=4, pady=4)
            self.ferms.append(panel)

        # Footer
        footer = ttk.Frame(main.inner)
        footer.grid(row=3, column=0, columnspan=3, sticky="ew", padx=12, pady=(4, 10))
        footer.grid_columnconfigure(0, weight=1)
        footer.grid_columnconfigure(1, weight=1)
        footer.grid_columnconfigure(2, weight=1)

        ttk.Button(footer, text="DETENER TODO", command=self.cerrar_todo_global).grid(row=0, column=0, sticky="w")
        ttk.Button(footer, text="Exportar CSV de todos", command=self.export_all).grid(
            row=0, column=1, sticky="w", padx=(10, 0)
        )

        self.clock_var = tk.StringVar(value=now_str())
        ttk.Label(footer, textvariable=self.clock_var).grid(row=0, column=2, sticky="e")

        self._tick_job = None
        self._plot_windows = []
        self._closing = False
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self._log_flowmeters_status()
        self._tick()

    # ===== util backup =====
    def _log_flowmeters_status(self):
        print("[CO2] Diagnóstico ADS1115 (AIN0/AIN1/AIN2):")
        ok_count = 0
        for name in ("F1", "F2", "F3"):
            reader = self.flow_readers.get(name)
            if not reader:
                print(f"[CO2] {name}: lector no inicializado.")
                continue
            ok, v, note = reader.probe()
            ch_label = f"AIN{reader.channel}"
            addr = f"0x{reader.address:02X}"
            if ok:
                ok_count += 1
                v_txt = f"{v:.4f} V" if v is not None else "n/a"
                print(f"[CO2] {name} {addr} {ch_label}: {note}. V={v_txt}")
            else:
                print(f"[CO2] {name} {addr} {ch_label}: NO DETECTADO. {note}")
        print(f"[CO2] Caudalímetros detectados: {ok_count}/3")

    def get_backup_path(self):
        path = self.backup_path.get().strip()
        if not path:
            path = os.path.abspath("./Backup/backup_global_temperatura.csv")
            self.backup_path.set(path)
        if not path.lower().endswith(".csv"):
            path += ".csv"
        d = os.path.dirname(path) or "."
        os.makedirs(d, exist_ok=True)
        return path

    def pick_backup(self):
        fn = filedialog.asksaveasfilename(
            title="Elegir archivo de BACKUP global temperatura",
            initialfile=os.path.basename(self.backup_path.get()),
            defaultextension=".csv",
            filetypes=[("CSV", "*.csv"), ("Todos", "*.*")],
        )
        _restore_focus(self)
        if fn:
            self.backup_path.set(fn)
            os.makedirs(os.path.dirname(fn), exist_ok=True)

    def clear_backup_temp(self):
        path = self.get_backup_path()
        if not os.path.exists(path):
            messagebox.showinfo("Backup temperatura", f"No existe:\n{path}")
            return
        if not messagebox.askyesno("Backup temperatura", f"¿Borrar backup?\n{path}"):
            return
        try:
            os.remove(path)
            messagebox.showinfo("Backup temperatura", f"Backup borrado:\n{path}")
        except Exception as e:
            messagebox.showerror("Backup temperatura", f"No se pudo borrar.\n{e}")

    def get_co2_backup_path(self):
        path = self.backup_co2_path.get().strip()
        if not path:
            path = os.path.abspath("./Backup/backup_global_co2.csv")
            self.backup_co2_path.set(path)
        if not path.lower().endswith(".csv"):
            path += ".csv"
        d = os.path.dirname(path) or "."
        os.makedirs(d, exist_ok=True)
        return path

    def pick_backup_co2(self):
        fn = filedialog.asksaveasfilename(
            title="Elegir archivo de BACKUP global CO2",
            initialfile=os.path.basename(self.backup_co2_path.get()),
            defaultextension=".csv",
            filetypes=[("CSV", "*.csv"), ("Todos", "*.*")],
        )
        _restore_focus(self)
        if fn:
            self.backup_co2_path.set(fn)
            os.makedirs(os.path.dirname(fn), exist_ok=True)

    def clear_backup_co2(self):
        path = self.get_co2_backup_path()
        if not os.path.exists(path):
            messagebox.showinfo("Backup CO2", f"No existe:\n{path}")
            return
        if not messagebox.askyesno("Backup CO2", f"¿Borrar backup?\n{path}"):
            return
        try:
            os.remove(path)
            messagebox.showinfo("Backup CO2", f"Backup borrado:\n{path}")
        except Exception as e:
            messagebox.showerror("Backup CO2", f"No se pudo borrar.\n{e}")

    def _read_recent_backup(self, days=10, fermenter=None, path=None):
        if path is None:
            path = self.get_backup_path()
        if not os.path.exists(path):
            return {}
        cutoff = now() - dt.timedelta(days=days)
        data = {}
        try:
            with open(path, "r", encoding="utf-8") as f:
                reader = csv.DictReader(f)
                for row in reader:
                    ts_raw = (row.get("timestamp") or "").strip()
                    ts = None
                    for fmt in ("%Y-%m-%d %H:%M:%S", "%Y/%m/%d %H:%M:%S"):
                        try:
                            ts = dt.datetime.strptime(ts_raw, fmt)
                            break
                        except Exception:
                            continue
                    if not ts or ts < cutoff:
                        continue
                    ferm = row.get("fermentador", "?").strip() or "?"
                    if fermenter and ferm != fermenter:
                        continue
                    try:
                        temp = float(row.get("T", "nan"))
                        sp = float(row.get("SP", "nan"))
                        nut = int(row.get("nutricion_activa", "0") or 0)
                    except Exception:
                        continue
                    data.setdefault(ferm, {"ts": [], "t": [], "sp": [], "nut": []})
                    data[ferm]["ts"].append(ts)
                    data[ferm]["t"].append(temp)
                    data[ferm]["sp"].append(sp)
                    data[ferm]["nut"].append(nut)
        except Exception:
            return {}
        return data

    def _read_recent_co2_backup(self, days=10, fermenter=None, path=None):
        if path is None:
            path = self.get_co2_backup_path()
        if not os.path.exists(path):
            return {}
        cutoff = now() - dt.timedelta(days=days)
        data = {}
        try:
            with open(path, "r", encoding="utf-8") as f:
                reader = csv.DictReader(f)
                for row in reader:
                    ts_raw = (row.get("timestamp") or "").strip()
                    ts = None
                    for fmt in ("%Y-%m-%d %H:%M:%S", "%Y/%m/%d %H:%M:%S"):
                        try:
                            ts = dt.datetime.strptime(ts_raw, fmt)
                            break
                        except Exception:
                            continue
                    if not ts or ts < cutoff:
                        continue
                    ferm = row.get("fermentador", "?").strip() or "?"
                    if fermenter and ferm != fermenter:
                        continue
                    try:
                        flow = float(row.get("flow_sccm", "nan"))
                        flow_filt_raw = row.get("flow_filt_sccm", None)
                        if flow_filt_raw is None or str(flow_filt_raw).strip() == "":
                            flow_filt = flow
                        else:
                            flow_filt = float(flow_filt_raw)
                    except Exception:
                        continue
                    data.setdefault(ferm, {"ts": [], "flow": [], "flow_filt": []})
                    data[ferm]["ts"].append(ts)
                    data[ferm]["flow"].append(flow)
                    data[ferm]["flow_filt"].append(flow_filt)
        except Exception:
            return {}
        return data

    def _co2_csv_path(self, fermenter):
        name = self.co2_csv_name[fermenter].get().strip() or f"{fermenter}_co2.csv"
        if not name.lower().endswith(".csv"):
            name += ".csv"
        return os.path.join(self.co2_csv_dir[fermenter].get(), name)

    def _co2_csv_register_led(self, fermenter, led):
        leds = self._co2_csv_leds.setdefault(fermenter, [])
        if led not in leds:
            leds.append(led)

    def _co2_csv_unregister_led(self, fermenter, led):
        leds = self._co2_csv_leds.get(fermenter)
        if not leds:
            return
        try:
            leds.remove(led)
        except ValueError:
            pass
        if not leds:
            self._co2_csv_leds.pop(fermenter, None)

    def _co2_csv_state_led(self, fermenter, color):
        leds = self._co2_csv_leds.get(fermenter, [])
        for led in list(leds):
            led.set_color(color)

    def co2_pick_dir(self, fermenter):
        d = filedialog.askdirectory(title="Elegir carpeta de trabajo CSV CO2")
        _restore_focus(self)
        if d:
            self.co2_csv_dir[fermenter].set(d)
            os.makedirs(d, exist_ok=True)

    def co2_csv_start(self, fermenter):
        self.co2_csv_running[fermenter] = True
        self.co2_csv_paused[fermenter] = False
        self.co2_csv_last_export_ok[fermenter] = False
        self._co2_csv_state_led(fermenter, "#22c55e")

    def co2_csv_pause(self, fermenter):
        self.co2_csv_running[fermenter] = False
        self.co2_csv_paused[fermenter] = True
        self._co2_csv_state_led(fermenter, "#eab308")

    def co2_csv_export(self, fermenter):
        if self.co2_csv_running[fermenter]:
            messagebox.showerror("Exportar", "Detén o pausa el CSV antes de exportar.")
            return
        src = self._co2_csv_path(fermenter)
        if not os.path.exists(src):
            messagebox.showerror("Exportar", f"No existe {src}")
            return
        dst_dir = filedialog.askdirectory(title="Seleccionar carpeta de destino")
        _restore_focus(self)
        if not dst_dir:
            return
        try:
            dst = os.path.join(dst_dir, os.path.basename(src))
            with open(src, "r", encoding="utf-8") as fsrc, open(dst, "w", encoding="utf-8", newline="") as fdst:
                fdst.write(fsrc.read())
            self.co2_csv_last_export_ok[fermenter] = True
            self._co2_csv_state_led(fermenter, "#3b82f6")
            messagebox.showinfo("Exportar", f"Archivo exportado a:\n{dst}")
        except Exception as e:
            messagebox.showerror("Exportar", f"No se pudo exportar.\n{e}")

    def co2_csv_restart(self, fermenter):
        self.co2_csv_running[fermenter] = False
        self.co2_csv_paused[fermenter] = False
        path = self._co2_csv_path(fermenter)
        try:
            if os.path.exists(path):
                os.remove(path)
            self._co2_csv_state_led(fermenter, "#ef4444")
            messagebox.showinfo("CSV CO2", f"Archivo reiniciado:\n{path}")
        except Exception as e:
            messagebox.showerror("CSV CO2", f"No se pudo reiniciar.\n{e}")

    def _co2_csv_write_row(self, fermenter, ts, flow, current_ma, voltage, status):
        if not self.co2_csv_running.get(fermenter, False):
            return
        row = {
            "timestamp": ts.strftime("%Y-%m-%d %H:%M:%S"),
            "fermentador": fermenter,
            "flow_sccm": f"{flow:.4f}",
            "status": status,
        }
        ipath = self._co2_csv_path(fermenter)
        header = not os.path.exists(ipath)
        try:
            os.makedirs(os.path.dirname(ipath), exist_ok=True)
            with open(ipath, "a", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=list(row.keys()))
                if header:
                    w.writeheader()
                w.writerow(row)
        except Exception as e:
            messagebox.showerror("CSV CO2", f"No se pudo escribir en {ipath}\n{e}")

    def _co2f_csv_path(self, fermenter):
        name = self.co2f_csv_name[fermenter].get().strip() or f"{fermenter}_co2_filt.csv"
        if not name.lower().endswith(".csv"):
            name += ".csv"
        return os.path.join(self.co2f_csv_dir[fermenter].get(), name)

    def _co2f_csv_register_led(self, fermenter, led):
        leds = self._co2f_csv_leds.setdefault(fermenter, [])
        if led not in leds:
            leds.append(led)

    def _co2f_csv_unregister_led(self, fermenter, led):
        leds = self._co2f_csv_leds.get(fermenter)
        if not leds:
            return
        try:
            leds.remove(led)
        except ValueError:
            pass
        if not leds:
            self._co2f_csv_leds.pop(fermenter, None)

    def _co2f_csv_state_led(self, fermenter, color):
        leds = self._co2f_csv_leds.get(fermenter, [])
        for led in list(leds):
            led.set_color(color)

    def co2f_pick_dir(self, fermenter):
        d = filedialog.askdirectory(title="Elegir carpeta de trabajo CSV CO2 FILTRADO")
        _restore_focus(self)
        if d:
            self.co2f_csv_dir[fermenter].set(d)
            os.makedirs(d, exist_ok=True)

    def co2f_csv_start(self, fermenter):
        self.co2f_csv_running[fermenter] = True
        self.co2f_csv_paused[fermenter] = False
        self.co2f_csv_last_export_ok[fermenter] = False
        self._co2f_csv_state_led(fermenter, "#22c55e")

    def co2f_csv_pause(self, fermenter):
        self.co2f_csv_running[fermenter] = False
        self.co2f_csv_paused[fermenter] = True
        self._co2f_csv_state_led(fermenter, "#eab308")

    def co2f_csv_export(self, fermenter):
        if self.co2f_csv_running[fermenter]:
            messagebox.showerror("Exportar", "Detén o pausa el CSV antes de exportar.")
            return
        src = self._co2f_csv_path(fermenter)
        if not os.path.exists(src):
            messagebox.showerror("Exportar", f"No existe {src}")
            return
        dst_dir = filedialog.askdirectory(title="Seleccionar carpeta de destino")
        _restore_focus(self)
        if not dst_dir:
            return
        try:
            dst = os.path.join(dst_dir, os.path.basename(src))
            with open(src, "r", encoding="utf-8") as fsrc, open(dst, "w", encoding="utf-8", newline="") as fdst:
                fdst.write(fsrc.read())
            self.co2f_csv_last_export_ok[fermenter] = True
            self._co2f_csv_state_led(fermenter, "#3b82f6")
            messagebox.showinfo("Exportar", f"Archivo exportado a:\n{dst}")
        except Exception as e:
            messagebox.showerror("Exportar", f"No se pudo exportar.\n{e}")

    def co2f_csv_restart(self, fermenter):
        self.co2f_csv_running[fermenter] = False
        self.co2f_csv_paused[fermenter] = False
        path = self._co2f_csv_path(fermenter)
        try:
            if os.path.exists(path):
                os.remove(path)
            self._co2f_csv_state_led(fermenter, "#ef4444")
            messagebox.showinfo("CSV CO2 FILTRADO", f"Archivo reiniciado:\n{path}")
        except Exception as e:
            messagebox.showerror("CSV CO2 FILTRADO", f"No se pudo reiniciar.\n{e}")

    def _co2f_csv_write_row(self, fermenter, ts, flow_filt, status, is_spike):
        if not self.co2f_csv_running.get(fermenter, False):
            return
        row = {
            "timestamp": ts.strftime("%Y-%m-%d %H:%M:%S"),
            "fermentador": fermenter,
            "flow_filt_sccm": f"{flow_filt:.4f}",
            "status": status,
            "is_spike": int(bool(is_spike)),
        }
        ipath = self._co2f_csv_path(fermenter)
        header = not os.path.exists(ipath)
        try:
            os.makedirs(os.path.dirname(ipath), exist_ok=True)
            with open(ipath, "a", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=list(row.keys()))
                if header:
                    w.writeheader()
                w.writerow(row)
        except Exception as e:
            messagebox.showerror("CSV CO2 FILTRADO", f"No se pudo escribir en {ipath}\n{e}")

    def _co2_backup_ensure_schema(self, path):
        if (not os.path.exists(path)) or os.path.getsize(path) == 0:
            return
        try:
            with open(path, "r", encoding="utf-8", newline="") as f:
                reader = csv.DictReader(f)
                fieldnames = list(reader.fieldnames or [])
                if "flow_filt_sccm" in fieldnames:
                    return
                rows = list(reader)
        except Exception:
            return

        new_fields = [
            "timestamp",
            "fermentador",
            "flow_sccm",
            "flow_filt_sccm",
            "current_ma",
            "voltage",
            "status",
        ]
        tmp_path = f"{path}.tmp"
        with open(tmp_path, "w", newline="", encoding="utf-8") as f:
            w = csv.DictWriter(f, fieldnames=new_fields)
            w.writeheader()
            for old in rows:
                flow_raw = (old.get("flow_sccm") or "").strip()
                flow_filt = (old.get("flow_filt_sccm") or "").strip() or flow_raw
                w.writerow(
                    {
                        "timestamp": (old.get("timestamp") or "").strip(),
                        "fermentador": (old.get("fermentador") or "").strip(),
                        "flow_sccm": flow_raw,
                        "flow_filt_sccm": flow_filt,
                        "current_ma": (old.get("current_ma") or "").strip(),
                        "voltage": (old.get("voltage") or "").strip(),
                        "status": (old.get("status") or "").strip(),
                    }
                )
        os.replace(tmp_path, path)

    def _co2_backup_write_row(self, fermenter, ts, flow, flow_filt, current_ma, voltage, status):
        path = self.get_co2_backup_path()
        row = {
            "timestamp": ts.strftime("%Y-%m-%d %H:%M:%S"),
            "fermentador": fermenter,
            "flow_sccm": f"{flow:.4f}",
            "flow_filt_sccm": f"{flow_filt:.4f}",
            "current_ma": f"{current_ma:.4f}",
            "voltage": f"{voltage:.4f}",
            "status": status,
        }
        header = not os.path.exists(path) or os.path.getsize(path) == 0
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            if not header:
                self._co2_backup_ensure_schema(path)
            with open(path, "a", newline="", encoding="utf-8") as f:
                w = csv.DictWriter(f, fieldnames=list(row.keys()))
                if header:
                    w.writeheader()
                w.writerow(row)
        except Exception as e:
            messagebox.showerror("Backup CO2", f"No se pudo escribir en {path}\n{e}")

    def _record_nut_sample(self, fermenter, ts, state):
        state_int = 1 if state else 0
        last_state = self.nut_last_state.get(fermenter)
        if last_state is None or state_int != last_state:
            self.nut_samples.setdefault(fermenter, []).append((ts, state_int))
            self.nut_last_state[fermenter] = state_int
        samples = self.nut_samples.get(fermenter, [])
        if not samples:
            return
        cutoff = ts - dt.timedelta(hours=MAX_FLOW_HISTORY_HOURS)
        if samples[0][0] < cutoff:
            self.nut_samples[fermenter] = [row for row in samples if row[0] >= cutoff]

    def _flow_take_sample(self, fermenter, ts=None):
        reader = self.flow_readers.get(fermenter)
        if reader is None:
            return
        if ts is None:
            ts = now()
        try:
            voltage = reader.read_voltage()
        except Exception as exc:
            print(f"[FLOW] Error leyendo {fermenter}: {exc}")
            next_ts = ts + dt.timedelta(seconds=self.flow_sample_period[fermenter])
            self.flow_next_sample[fermenter] = next_ts
            return

        current_ma = voltage_to_current_ma(voltage, reader.shunt_ohms)
        flow = current_to_flow_sccm(current_ma)
        flt = self.co2_filters.get(fermenter)
        if flt is None:
            flt = CO2RealtimeFilter(
                dt_seconds=float(self.flow_sample_period.get(fermenter, 1.0)),
                w_spike_seconds=W_SPIKE_SECONDS,
                k=K,
                min_abs_spike=MIN_ABS_SPIKE,
                tau_seconds=TAU_SECONDS,
                butter_order=BUTTER_ORDER,
            )
            self.co2_filters[fermenter] = flt
        flow_despike, flow_filt, is_spike = flt.update(flow)
        status = "OK"
        if current_ma < 3.8:
            status = "Bajo rango"
        elif current_ma > 20.5:
            status = "Alto rango"

        if FLOW_DEBUG or fermenter in FLOW_DEBUG_FERMS:
            ch_label = f"AIN{reader.channel}"
            addr = f"0x{reader.address:02X}"
            print(
                f"[FLOW] {fermenter} {addr} {ch_label} "
                f"V={voltage:.4f} I={current_ma:.2f}mA "
                f"Q={flow:.2f}SCCM Qf={flow_filt:.2f}SCCM ({status})"
            )

        samples = self.flow_samples.get(fermenter, [])
        samples.append((ts, flow, current_ma, voltage, status))
        samples_filt = self.flow_samples_filt.get(fermenter, [])
        samples_filt.append((ts, flow_filt, status, int(bool(is_spike))))
        cutoff = ts - dt.timedelta(hours=MAX_FLOW_HISTORY_HOURS)
        self.flow_samples[fermenter] = [row for row in samples if row[0] >= cutoff]
        self.flow_samples_filt[fermenter] = [row for row in samples_filt if row[0] >= cutoff]
        self._co2_csv_write_row(fermenter, ts, flow, current_ma, voltage, status)
        self._co2f_csv_write_row(fermenter, ts, flow_filt, status, is_spike)
        self._co2_backup_write_row(fermenter, ts, flow, flow_filt, current_ma, voltage, status)
        self.flow_next_sample[fermenter] = ts + dt.timedelta(seconds=self.flow_sample_period[fermenter])

    def _flow_tick(self):
        ts = now()
        for name in self.flow_readers:
            next_ts = self.flow_next_sample.get(name)
            if next_ts is None or ts >= next_ts:
                self._flow_take_sample(name, ts=ts)

    # ===== gráficos =====
    def open_flow_plot(self, fermenter):
        mpl_spec = importlib_util.find_spec("matplotlib")
        if not mpl_spec:
            messagebox.showerror("Gráfico", "Instala matplotlib para usar el gráfico en tiempo real.")
            return
        reader = self.flow_readers.get(fermenter)
        if reader is None:
            messagebox.showerror("Gráfico", f"No hay configuración de caudal para {fermenter}.")
            return
        existing = self._flow_plot_windows.get(fermenter)
        if existing is not None and existing.winfo_exists():
            try:
                existing.lift()
                existing.focus_force()
            except Exception:
                pass
            return

        window = FlowPlotWindow(self, fermenter)
        self._flow_plot_windows[fermenter] = window.top

    def open_flow_plot_filtered(self, fermenter):
        mpl_spec = importlib_util.find_spec("matplotlib")
        if not mpl_spec:
            messagebox.showerror("Gráfico", "Instala matplotlib para usar el gráfico en tiempo real.")
            return
        reader = self.flow_readers.get(fermenter)
        if reader is None:
            messagebox.showerror("Gráfico", f"No hay configuración de caudal para {fermenter}.")
            return
        existing = self._flow_plot_filtered_windows.get(fermenter)
        if existing is not None and existing.winfo_exists():
            try:
                existing.lift()
                existing.focus_force()
            except Exception:
                pass
            return

        window = FlowPlotFilteredWindow(self, fermenter)
        self._flow_plot_filtered_windows[fermenter] = window.top

    def open_realtime_plot(self, fermenter=None):
        mpl_spec = importlib_util.find_spec("matplotlib")
        if not mpl_spec:
            messagebox.showerror("Gráfico", "Instala matplotlib para usar el gráfico en tiempo real.")
            return
        RealTimePlotWindow(self, fermenter=fermenter)

    # ===== loop principal =====
    def _tick(self):
        if self._closing:
            return
        self.clock_var.set(now().strftime("%Y-%m-%d %H:%M:%S"))
        for f in self.ferms:
            f.update_process()
        self._flow_tick()
        self._tick_job = self.after(1000, self._tick)

    def cerrar_todo_global(self):
        for f in self.ferms:
            f.stop_all()
        messagebox.showinfo("Seguridad", "Se cerraron todas las válvulas y se detuvo el control automático.")

    def export_all(self):
        for f in self.ferms:
            f.csv_export()
        for name in self.co2_csv_name:
            self.co2_csv_export(name)
        for name in self.co2f_csv_name:
            self.co2f_csv_export(name)

    def on_close(self):
        self._closing = True
        if self._tick_job is not None:
            try:
                self.after_cancel(self._tick_job)
            except Exception:
                pass
            self._tick_job = None

        for top in list(self._plot_windows):
            if top.winfo_exists():
                try:
                    top.destroy()
                except Exception:
                    pass
        self._plot_windows.clear()
        self._flow_plot_windows.clear()
        self._flow_plot_filtered_windows.clear()

        try:
            for f in self.ferms:
                f.stop_all()
            for reader in self.flow_readers.values():
                try:
                    reader.close()
                except Exception:
                    pass
            self.hw.cleanup()
        finally:
            try:
                for job in self.after_info():
                    try:
                        self.after_cancel(job)
                    except Exception:
                        pass
            except Exception:
                pass
            try:
                self.quit()
            except Exception:
                pass
            self.destroy()


if __name__ == "__main__":
    app = App()
    app.mainloop()
