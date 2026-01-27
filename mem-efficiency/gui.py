import csv
import os
import threading
import time
import queue
from collections import deque
from datetime import datetime, timezone
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from tkinter.font import Font
import subprocess
import sys
import psutil
import platform

# ---------------- Optional: matplotlib for graphs ----------------
HAS_MPL = True
try:
    import matplotlib
    matplotlib.use("TkAgg")
    from matplotlib.figure import Figure
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
except Exception:
    HAS_MPL = False

IS_WIN = sys.platform.startswith("win")

def win_commit_info_gb():
    """Windows: Commit used/limit/% using GlobalMemoryStatusEx (best-effort)."""
    if not IS_WIN:
        return None
    try:
        import ctypes

        class MEMORYSTATUSEX(ctypes.Structure):
            _fields_ = [
                ("dwLength", ctypes.c_ulong),
                ("dwMemoryLoad", ctypes.c_ulong),
                ("ullTotalPhys", ctypes.c_ulonglong),
                ("ullAvailPhys", ctypes.c_ulonglong),
                ("ullTotalPageFile", ctypes.c_ulonglong),
                ("ullAvailPageFile", ctypes.c_ulonglong),
                ("ullTotalVirtual", ctypes.c_ulonglong),
                ("ullAvailVirtual", ctypes.c_ulonglong),
                ("ullAvailExtendedVirtual", ctypes.c_ulonglong),
            ]

        stat = MEMORYSTATUSEX()
        stat.dwLength = ctypes.sizeof(MEMORYSTATUSEX)
        if ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(stat)) == 0:
            return None

        limit = stat.ullTotalPageFile
        avail = stat.ullAvailPageFile
        used = max(0, limit - avail)

        def b2gb(x): return x / (1024 ** 3)

        limit_gb = b2gb(limit)
        used_gb = b2gb(used)
        pct = (used / limit * 100.0) if limit > 0 else 0.0
        return (round(used_gb, 4), round(limit_gb, 4), round(pct, 2))
    except Exception:
        return None

class WinPageFaultsPerSec:
    """Windows PDH counter: \\Memory\\Page Faults/sec (best-effort)."""
    def __init__(self):
        self.ok = False
        if not IS_WIN:
            return
        try:
            import ctypes
            self.ctypes = ctypes
            self.pdh = ctypes.windll.pdh
            self.PDH_FMT_DOUBLE = 0x00000200
            self.query = ctypes.c_void_p()
            self.counter = ctypes.c_void_p()

            if self.pdh.PdhOpenQueryW(None, 0, ctypes.byref(self.query)) != 0:
                return

            path = r"\Memory\Page Faults/sec"
            if self.pdh.PdhAddEnglishCounterW(self.query, path, 0, ctypes.byref(self.counter)) != 0:
                self.pdh.PdhCloseQuery(self.query)
                return

            self.pdh.PdhCollectQueryData(self.query)
            self.ok = True
        except Exception:
            self.ok = False

    def read(self):
        if not self.ok:
            return None
        try:
            ctypes = self.ctypes
            self.pdh.PdhCollectQueryData(self.query)

            class PDH_FMT_COUNTERVALUE(ctypes.Structure):
                _fields_ = [("CStatus", ctypes.c_ulong), ("doubleValue", ctypes.c_double)]

            val = PDH_FMT_COUNTERVALUE()
            r = self.pdh.PdhGetFormattedCounterValue(self.counter, self.PDH_FMT_DOUBLE, None, ctypes.byref(val))
            if r != 0:
                return None
            return float(val.doubleValue)
        except Exception:
            return None

    def close(self):
        if not self.ok:
            return
        try:
            self.pdh.PdhCloseQuery(self.query)
        except Exception:
            pass
        self.ok = False

# ---------------- Paths ----------------
BASE_DIR = os.path.dirname(os.path.abspath(__file__))

def resolve_path(p: str) -> str:
    p = (p or "").strip()
    if not p:
        return p
    if os.path.isabs(p):
        return os.path.normpath(p)
    return os.path.normpath(os.path.join(BASE_DIR, p))

def ensure_dir_for_file(file_path: str):
    d = os.path.dirname(file_path)
    if d:
        os.makedirs(d, exist_ok=True)

def ensure_dir(path_dir: str):
    os.makedirs(path_dir, exist_ok=True)

# ---------------- Helpers ----------------
def now_iso():
    return datetime.now(timezone.utc).isoformat()

def now_local_hms():
    return datetime.now().strftime("%H:%M:%S")

def bytes_to_gb(x: float) -> float:
    return x / (1024 ** 3)

def bytes_to_mb(x: float) -> float:
    return x / (1024 ** 2)

def beep():
    try:
        if sys.platform.startswith("win"):
            import winsound
            winsound.Beep(1200, 160)
        else:
            sys.stdout.write("\a")
            sys.stdout.flush()
    except Exception:
        pass

# ---------------- "Efficiency" scoring ----------------
PF_WARN = 200.0
PF_CRIT = 800.0

def clamp(x, lo, hi):
    return lo if x < lo else hi if x > hi else x

def memory_efficiency_score(used_pct, swap_pct, commit_pct, pf_per_sec, avail_gb, total_gb):
    """
    Efficiency = ability to operate without memory pressure.
    Returns (score:int 0..100, label:str, reasons:list[str])
    """
    reasons = []
    score = 100.0

    # RAM pressure
    if used_pct > 70:
        score -= (used_pct - 70) * 1.1
        reasons.append(f"RAM high ({used_pct:.1f}%)")

    # Swap usage (strong penalty)
    if swap_pct > 5:
        score -= (swap_pct - 5) * 2.2
        reasons.append(f"Swap used ({swap_pct:.1f}%)")

    # Commit pressure (if available)
    if commit_pct is not None:
        try:
            if commit_pct == commit_pct:  # not NaN
                if commit_pct > 75:
                    score -= (commit_pct - 75) * 0.9
                    reasons.append(f"Commit high ({commit_pct:.1f}%)")
        except Exception:
            pass

    # Page faults/sec (churn indicator)
    if pf_per_sec is not None:
        try:
            if pf_per_sec == pf_per_sec:  # not NaN
                if pf_per_sec > PF_WARN:
                    if pf_per_sec <= PF_CRIT:
                        score -= (pf_per_sec - PF_WARN) / 20.0
                    else:
                        score -= 30.0 + (pf_per_sec - PF_CRIT) / 40.0
                    reasons.append(f"Page faults high ({pf_per_sec:.0f}/s)")
        except Exception:
            pass

    # Low headroom penalty
    if total_gb > 0:
        avail_pct = (avail_gb / total_gb) * 100.0
        if avail_pct < 10:
            score -= (10 - avail_pct) * 1.5
            reasons.append(f"Low free RAM ({avail_gb:.2f} GB)")

    score = clamp(score, 0.0, 100.0)
    score_i = int(round(score))

    if score_i >= 80:
        label = "Good"
    elif score_i >= 60:
        label = "OK"
    elif score_i >= 40:
        label = "Warning"
    else:
        label = "Poor"

    return score_i, label, reasons[:3]

CSV_FIELDS = [
    "timestamp_utc",
    "total_gb",
    "available_gb",
    "used_gb",
    "used_percent",
    "swap_total_gb",
    "swap_used_gb",
    "swap_percent",
    "commit_used_gb",
    "commit_limit_gb",
    "commit_percent",
    "page_faults_per_sec",
    "efficiency_score",
    "efficiency_label",
]

def grouped_top_processes_by_rss(top_n: int):
    agg_rss = {}
    agg_pids = {}

    for p in psutil.process_iter(attrs=["pid", "name"], ad_value=None):
        try:
            name = p.info.get("name") or "<unknown>"
            pid = p.info.get("pid")
            rss = p.memory_info().rss
            agg_rss[name] = agg_rss.get(name, 0) + rss
            if pid is not None:
                agg_pids.setdefault(name, set()).add(pid)
        except Exception:
            continue

    items = sorted(agg_rss.items(), key=lambda kv: kv[1], reverse=True)[:top_n]
    top = []
    for name, rss in items:
        top.append((name, round(bytes_to_mb(rss), 2), sorted(list(agg_pids.get(name, set())))))

    while len(top) < top_n:
        top.append(("", 0.0, []))
    return top

class MemoryDashboard(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Windows Memory Utilization Dashboard")
        self.geometry("1260x800")
        self.minsize(1200, 740)

        self.monitor_running = False
        self.logger_running = False

        self.lock = threading.Lock()
        self.latest_sys = None
        self.latest_top = []
        self.last_top_err = ""

        self.collect_thread = None
        self.logger_thread = None

        self.log_fp = None
        self.log_writer = None
        self.log_queue = queue.Queue()
        self.last_written_csv = None

        self.interval_sec = 1.0
        self.zoom_minutes = 5
        self._rebuild_series_buffers()

        self.last_alert_level = "OK"
        self.alert_markers = deque(maxlen=200)

        self.data_dir = os.path.join(BASE_DIR, "data")
        ensure_dir(self.data_dir)

        self._top_pid_map = {}

        self.pf_counter = WinPageFaultsPerSec() if IS_WIN else None

        self._build_ui()
        self.after(200, self._refresh_ui)
        self.after(150, self._drain_log_queue)
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    def _rebuild_series_buffers(self):
        try:
            interval = max(0.2, float(self.interval_sec))
        except Exception:
            interval = 1.0
        self.graph_points = max(60, int((self.zoom_minutes * 60.0) / interval) + 5)

        self.ts_series = deque(maxlen=self.graph_points)
        self.ram_series = deque(maxlen=self.graph_points)
        self.swap_series = deque(maxlen=self.graph_points)
        self.avail_series = deque(maxlen=self.graph_points)
        self.commit_series = deque(maxlen=self.graph_points)
        self.pf_series = deque(maxlen=self.graph_points)

    def on_close(self):
        self.monitor_running = False
        self.logger_running = False
        try:
            if self.pf_counter:
                self.pf_counter.close()
        except Exception:
            pass
        try:
            if self.log_fp:
                self.log_fp.close()
        except Exception:
            pass
        self.destroy()

    def _system_info_text(self):
        try:
            cpu_count = psutil.cpu_count(logical=True) or 0
            freq = psutil.cpu_freq()
            freq_txt = f"{freq.current:.0f} MHz" if freq else "-"
            vm = psutil.virtual_memory()
            total_ram = bytes_to_gb(vm.total)
            swap = psutil.swap_memory()
            total_swap = bytes_to_gb(swap.total)
            return (
                f"OS: {platform.system()} {platform.release()} ({platform.version()})\n"
                f"CPU: {platform.processor() or 'Unknown'}\n"
                f"Cores (logical): {cpu_count} | Freq: {freq_txt}\n"
                f"RAM Total: {total_ram:.2f} GB | Swap Total: {total_swap:.2f} GB\n"
                f"Uptime: {self._uptime_str()}"
            )
        except Exception:
            return "System info unavailable."

    def _uptime_str(self):
        try:
            boot = psutil.boot_time()
            sec = int(time.time() - boot)
            h = sec // 3600
            m = (sec % 3600) // 60
            s = sec % 60
            return f"{h}h {m}m {s}s"
        except Exception:
            return "-"

    # ---------------- UI ----------------
    def _build_ui(self):
        self.f_big = Font(family="Segoe UI", size=18, weight="bold")
        self.f_mid = Font(family="Segoe UI", size=11)
        self.f_small = Font(family="Consolas", size=9)

        self.style = ttk.Style()
        try:
            self.style.theme_use("clam")
        except Exception:
            pass

        bar = ttk.Frame(self, padding=(10, 10, 10, 6))
        bar.pack(fill="x")

        ttk.Label(bar, text="Interval (s):").pack(side="left")
        self.interval_var = tk.StringVar(value="1.0")
        ttk.Entry(bar, textvariable=self.interval_var, width=6).pack(side="left", padx=(5, 12))

        ttk.Label(bar, text="Zoom:").pack(side="left")
        self.zoom_var = tk.StringVar(value="5 min")
        zooms = ["1 min", "5 min", "30 min"]
        self.zoom_combo = ttk.Combobox(bar, textvariable=self.zoom_var, values=zooms, width=7, state="readonly")
        self.zoom_combo.pack(side="left", padx=(5, 12))
        self.zoom_combo.bind("<<ComboboxSelected>>", self.on_zoom_change)

        ttk.Label(bar, text="Top N:").pack(side="left")
        self.topn_var = tk.StringVar(value="5")
        ttk.Entry(bar, textvariable=self.topn_var, width=4).pack(side="left", padx=(5, 12))

        ttk.Label(bar, text="Top refresh (s):").pack(side="left")
        self.top_refresh_var = tk.StringVar(value="10")
        ttk.Entry(bar, textvariable=self.top_refresh_var, width=4).pack(side="left", padx=(5, 12))

        self.enable_top_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(bar, text="Top Processes", variable=self.enable_top_var).pack(side="left", padx=(0, 14))

        ttk.Label(bar, text="CSV:").pack(side="left")
        self.out_var = tk.StringVar(value=os.path.join("data", "gui_log.csv"))
        ttk.Entry(bar, textvariable=self.out_var, width=22).pack(side="left", padx=(5, 8))
        ttk.Button(bar, text="Browse", command=self.browse_csv).pack(side="left", padx=(0, 10))

        self.btn_start = ttk.Button(bar, text="Start", command=self.start_monitor)
        self.btn_start.pack(side="left", padx=4)

        self.btn_stop = ttk.Button(bar, text="Stop", command=self.stop_monitor, state="disabled")
        self.btn_stop.pack(side="left", padx=4)

        self.btn_log = ttk.Button(bar, text="Start Logging", command=self.toggle_logging, state="disabled")
        self.btn_log.pack(side="left", padx=(10, 4))

        self.btn_open_csv = ttk.Button(bar, text="Open CSV", command=self.open_csv)
        self.btn_open_csv.pack(side="left", padx=(10, 4))

        main = ttk.Frame(self, padding=(10, 4, 10, 10))
        main.pack(fill="both", expand=True)

        left = ttk.Frame(main)
        left.pack(side="left", fill="both", expand=True, padx=(0, 10))

        right = ttk.Frame(main)
        right.pack(side="right", fill="both")

        dash = ttk.LabelFrame(left, text="Overview", padding=10)
        dash.pack(fill="x", pady=(0, 8))

        ram_row = ttk.Frame(dash)
        ram_row.pack(fill="x", pady=(0, 8))
        self.ram_big = ttk.Label(ram_row, text="RAM: - %", font=self.f_big)
        self.ram_big.pack(side="left")
        self.ram_small = ttk.Label(ram_row, text="Free: - GB   Used: - GB / - GB", font=self.f_mid)
        self.ram_small.pack(side="left", padx=(18, 0))
        self.ram_bar = ttk.Progressbar(dash, orient="horizontal", mode="determinate", maximum=100)
        self.ram_bar.pack(fill="x", pady=(0, 6))

        swap_row = ttk.Frame(dash)
        swap_row.pack(fill="x", pady=(2, 0))
        self.swap_big = ttk.Label(swap_row, text="Swap: - %", font=self.f_big)
        self.swap_big.pack(side="left")
        self.swap_small = ttk.Label(swap_row, text="Used: - GB / - GB", font=self.f_mid)
        self.swap_small.pack(side="left", padx=(18, 0))
        self.swap_bar = ttk.Progressbar(dash, orient="horizontal", mode="determinate", maximum=100)
        self.swap_bar.pack(fill="x", pady=(6, 0))

        extra_row = ttk.Frame(dash)
        extra_row.pack(fill="x", pady=(8, 0))
        self.extra_var = tk.StringVar(value="Commit: - | Page Faults/sec: -")
        ttk.Label(extra_row, textvariable=self.extra_var, font=self.f_mid).pack(side="left")

        eff_row = ttk.Frame(dash)
        eff_row.pack(fill="x", pady=(6, 0))
        self.eff_var = tk.StringVar(value="Efficiency: -")
        ttk.Label(eff_row, textvariable=self.eff_var, font=self.f_mid).pack(side="left")

        # -------- Graph Controls (checkboxes) --------
        graph_box = ttk.LabelFrame(left, text="Time-series Graphs", padding=8)
        graph_box.pack(fill="x", pady=(0, 8))

        ctrl = ttk.Frame(graph_box)
        ctrl.pack(fill="x", pady=(0, 6))

        self.show_ram = tk.BooleanVar(value=True)
        self.show_swap = tk.BooleanVar(value=True)
        self.show_commit = tk.BooleanVar(value=True)
        self.show_avail = tk.BooleanVar(value=True)
        self.show_pf = tk.BooleanVar(value=True)

        def mk_cb(text, var):
            ttk.Checkbutton(ctrl, text=text, variable=var, command=self._redraw_graph).pack(side="left", padx=(0, 10))

        mk_cb("RAM %", self.show_ram)
        mk_cb("Swap %", self.show_swap)
        mk_cb("Commit %", self.show_commit)
        mk_cb("Available GB", self.show_avail)
        mk_cb("PageFaults/sec", self.show_pf)

        if not HAS_MPL:
            ttk.Label(
                graph_box,
                text="Matplotlib not available. Install: pip install matplotlib",
                justify="left"
            ).pack(anchor="w")
            self.canvas = None
            self.fig = None
            self.axL = None
            self.axR = None
        else:
            self.fig = Figure(figsize=(8.6, 2.3), dpi=100)
            self.axL = self.fig.add_subplot(111)
            self.axR = self.axL.twinx()
            self.axL.set_title("Selected metrics over time")
            self.axL.set_xlabel("seconds (relative)")
            self.axL.set_ylabel("%")
            self.axR.set_ylabel("GB / PF/s")
            self.axL.grid(True, alpha=0.3)

            self.canvas = FigureCanvasTkAgg(self.fig, master=graph_box)
            self.canvas.get_tk_widget().pack(fill="x", expand=False)

        procbox = ttk.LabelFrame(left, text="Top Processes (Grouped) — double click for details", padding=8)
        procbox.pack(fill="both", expand=True)

        self.tree = ttk.Treeview(procbox, columns=("name", "rss"), show="headings", height=14)
        self.tree.heading("name", text="Process")
        self.tree.heading("rss", text="Total RSS (MB)")
        self.tree.column("name", width=560, anchor="w")
        self.tree.column("rss", width=170, anchor="e")
        self.tree.pack(fill="both", expand=True)
        self.tree.bind("<Double-1>", self.on_tree_double_click)

        sysbox = ttk.LabelFrame(right, text="System", padding=10)
        sysbox.pack(fill="x", pady=(0, 8))
        self.sys_var = tk.StringVar(value=self._system_info_text())
        ttk.Label(sysbox, textvariable=self.sys_var, justify="left", wraplength=420).pack(anchor="w")

        alertbox = ttk.LabelFrame(right, text="Alerts", padding=10)
        alertbox.pack(fill="x", pady=(0, 8))

        dot_row = ttk.Frame(alertbox)
        dot_row.pack(fill="x", pady=(0, 6))

        bg = self.style.lookup("TFrame", "background") or "#f0f0f0"
        self.dot = tk.Canvas(dot_row, width=14, height=14, highlightthickness=0, bg=bg)
        self.dot.pack(side="left", padx=(0, 8))
        self.dot_id = self.dot.create_oval(2, 2, 12, 12, fill="#2ecc71", outline="")

        self.alert_text_var = tk.StringVar(value="OK")
        ttk.Label(dot_row, textvariable=self.alert_text_var).pack(side="left")

        self.alert_beep_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(alertbox, text="Beep on state change", variable=self.alert_beep_var).pack(anchor="w", pady=(6, 0))

        status = ttk.LabelFrame(right, text="Status", padding=10)
        status.pack(fill="x", pady=(0, 8))
        self.status_var = tk.StringVar(value="Idle")
        ttk.Label(status, textvariable=self.status_var, wraplength=420).pack(anchor="w")

        logbox = ttk.LabelFrame(right, text="Live Logs", padding=10)
        logbox.pack(fill="both", expand=True)

        self.log_text = tk.Text(logbox, height=18, wrap="none", font=self.f_small)
        self.log_text.pack(side="left", fill="both", expand=True)

        scroll = ttk.Scrollbar(logbox, command=self.log_text.yview)
        scroll.pack(side="right", fill="y")
        self.log_text.configure(yscrollcommand=scroll.set)

        btns = ttk.Frame(right)
        btns.pack(fill="x", pady=(6, 0))
        ttk.Button(btns, text="Clear Logs", command=self._clear_logs).pack(side="left")

    # ---------------- Browse: selects OUTPUT CSV path ----------------
    def browse_csv(self):
        initial = resolve_path(self.out_var.get())
        init_dir = os.path.dirname(initial) if initial else BASE_DIR
        filename = filedialog.asksaveasfilename(
            initialdir=init_dir,
            defaultextension=".csv",
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
        )
        if filename:
            try:
                rel = os.path.relpath(filename, BASE_DIR)
                if not rel.startswith(".."):
                    self.out_var.set(rel)
                else:
                    self.out_var.set(filename)
            except Exception:
                self.out_var.set(filename)

    def on_zoom_change(self, event=None):
        txt = (self.zoom_var.get() or "").strip().lower()
        if txt.startswith("1"):
            self.zoom_minutes = 1
        elif txt.startswith("30"):
            self.zoom_minutes = 30
        else:
            self.zoom_minutes = 5
        self._rebuild_series_buffers()

    def _clear_logs(self):
        self.log_text.delete("1.0", "end")

    def _parse_float(self, s, default):
        try:
            return float(s)
        except Exception:
            return default

    def _parse_int(self, s, default):
        try:
            return int(s)
        except Exception:
            return default

    # ---------------- Tree double click ----------------
    def on_tree_double_click(self, event=None):
        sel = self.tree.selection()
        if not sel:
            return
        iid = sel[0]
        vals = self.tree.item(iid, "values")
        if not vals or len(vals) < 1:
            return

        proc_name = vals[0]
        pids = self._top_pid_map.get(proc_name, [])

        lines = [f"Process: {proc_name}"]
        if not pids:
            lines.append("PIDs: (not available)")
        else:
            lines.append(f"PIDs: {', '.join(map(str, pids[:40]))}" + (" ..." if len(pids) > 40 else ""))

        extra = []
        for pid in pids[:6]:
            try:
                p = psutil.Process(pid)
                rss_mb = bytes_to_mb(p.memory_info().rss)
                extra.append(f"  PID {pid}: {rss_mb:.2f} MB RSS | {p.status()}")
            except Exception:
                continue
        if extra:
            lines.append("")
            lines.append("Instances (first 6):")
            lines.extend(extra)

        win = tk.Toplevel(self)
        win.title("Process Details")
        win.geometry("520x320")
        win.transient(self)
        win.grab_set()

        txt = tk.Text(win, wrap="word", font=self.f_small)
        txt.pack(fill="both", expand=True, padx=10, pady=10)
        txt.insert("1.0", "\n".join(lines))
        txt.configure(state="disabled")

        btn_row = ttk.Frame(win)
        btn_row.pack(fill="x", padx=10, pady=(0, 10))

        def copy_name():
            try:
                self.clipboard_clear()
                self.clipboard_append(proc_name)
            except Exception:
                pass

        def kill_all():
            if not pids:
                messagebox.showinfo("Kill", "No PIDs found for this process group.")
                return
            if not messagebox.askyesno("Kill", f"Kill ALL instances of {proc_name}?\nThis may close apps."):
                return
            killed = 0
            for pid in pids:
                try:
                    psutil.Process(pid).kill()
                    killed += 1
                except Exception:
                    continue
            messagebox.showinfo("Kill", f"Killed {killed}/{len(pids)} processes.")
            win.destroy()

        ttk.Button(btn_row, text="Copy Process Name", command=copy_name).pack(side="left")
        ttk.Button(btn_row, text="Kill All (admin)", command=kill_all).pack(side="left", padx=8)
        ttk.Button(btn_row, text="Close", command=win.destroy).pack(side="right")

    # ---------------- monitor ----------------
    def start_monitor(self):
        if self.monitor_running:
            return

        interval = self._parse_float(self.interval_var.get(), 1.0)
        if interval <= 0:
            messagebox.showerror("Invalid input", "Interval must be > 0.")
            return

        self.monitor_running = True
        self.btn_start.config(state="disabled")
        self.btn_stop.config(state="normal")
        self.btn_log.config(state="normal")
        self.status_var.set("Monitoring...")

        self.interval_sec = interval
        self._rebuild_series_buffers()

        def collect_loop():
            last_top_time = 0.0
            while self.monitor_running:
                interval_local = self._parse_float(self.interval_var.get(), 1.0)
                topn_local = self._parse_int(self.topn_var.get(), 5)
                top_refresh = self._parse_int(self.top_refresh_var.get(), 10)
                enable_top = bool(self.enable_top_var.get())

                try:
                    vm = psutil.virtual_memory()
                    sm = psutil.swap_memory()

                    commit_used_gb = ""
                    commit_limit_gb = ""
                    commit_percent = ""
                    cinfo = win_commit_info_gb()
                    if cinfo is not None:
                        commit_used_gb, commit_limit_gb, commit_percent = cinfo

                    pf = ""
                    if self.pf_counter is not None:
                        v = self.pf_counter.read()
                        if v is not None:
                            pf = round(float(v), 3)

                    sys_snap = {
                        "timestamp_utc": now_iso(),
                        "total_gb": round(bytes_to_gb(vm.total), 4),
                        "available_gb": round(bytes_to_gb(vm.available), 4),
                        "used_gb": round(bytes_to_gb(vm.total - vm.available), 4),
                        "used_percent": round(vm.percent, 2),
                        "swap_total_gb": round(bytes_to_gb(sm.total), 4),
                        "swap_used_gb": round(bytes_to_gb(sm.used), 4),
                        "swap_percent": round(sm.percent, 2),
                        "commit_used_gb": commit_used_gb,
                        "commit_limit_gb": commit_limit_gb,
                        "commit_percent": commit_percent,
                        "page_faults_per_sec": pf,
                        "efficiency_score": "",
                        "efficiency_label": "",
                    }

                    with self.lock:
                        self.latest_sys = sys_snap

                    now_t = time.time()
                    if enable_top and topn_local > 0 and (now_t - last_top_time) >= max(3, top_refresh):
                        last_top_time = now_t
                        try:
                            top = grouped_top_processes_by_rss(topn_local)
                            with self.lock:
                                self.latest_top = top
                                self.last_top_err = ""
                        except Exception as te:
                            with self.lock:
                                self.latest_top = []
                                self.last_top_err = f"Top process error: {te}"

                except Exception as e:
                    with self.lock:
                        self.latest_sys = {"error": f"Collector error: {e}"}

                time.sleep(max(0.2, interval_local))

        self.collect_thread = threading.Thread(target=collect_loop, daemon=True)
        self.collect_thread.start()

    def stop_monitor(self):
        self.monitor_running = False
        if self.logger_running:
            self.toggle_logging()

        self.btn_start.config(state="normal")
        self.btn_stop.config(state="disabled")
        self.btn_log.config(state="disabled")
        self.status_var.set("Stopped.")

    # ---------------- logging ----------------
    def toggle_logging(self):
        if not self.monitor_running:
            return

        if not self.logger_running:
            out_raw = (self.out_var.get() or "").strip()
            if not out_raw:
                messagebox.showerror("Invalid input", "CSV output path is empty.")
                return

            out = resolve_path(out_raw)
            ensure_dir_for_file(out)

            try:
                self.log_fp = open(out, "w", newline="", encoding="utf-8")
                self.log_writer = csv.DictWriter(self.log_fp, fieldnames=CSV_FIELDS)
                self.log_writer.writeheader()
                self.log_fp.flush()
                self.last_written_csv = out
            except Exception as e:
                messagebox.showerror("Logging error", f"Cannot open CSV:\n{e}")
                return

            self.logger_running = True
            self.btn_log.config(text="Stop Logging")
            self.status_var.set(f"Logging to {out}")
            self.log_queue.put("[logger] started")

            def log_loop():
                last_ts = None
                while self.logger_running and self.monitor_running:
                    with self.lock:
                        sys_snap = self.latest_sys

                    if sys_snap and "error" not in sys_snap:
                        ts = sys_snap.get("timestamp_utc", now_iso())
                        if ts == last_ts:
                            time.sleep(0.6)
                            continue
                        last_ts = ts

                        row = {k: sys_snap.get(k, "") for k in CSV_FIELDS}
                        try:
                            self.log_writer.writerow(row)
                            self.log_fp.flush()
                        except Exception:
                            pass

                        msg = (
                            f"{now_local_hms()} | RAM {row['used_percent']}% | "
                            f"Free {row['available_gb']}GB | Swap {row['swap_percent']}% | "
                            f"Commit {row.get('commit_percent','')}% | PF/s {row.get('page_faults_per_sec','')} | "
                            f"Eff {row.get('efficiency_score','')}/100 {row.get('efficiency_label','')}"
                        )
                        try:
                            self.log_queue.put_nowait(msg)
                        except Exception:
                            pass

                    time.sleep(1.0)

                self.log_queue.put("[logger] stopped")

            self.logger_thread = threading.Thread(target=log_loop, daemon=True)
            self.logger_thread.start()

        else:
            self.logger_running = False
            self.btn_log.config(text="Start Logging")
            try:
                if self.log_fp:
                    self.log_fp.close()
            except Exception:
                pass
            self.log_fp = None
            self.log_writer = None
            if self.monitor_running:
                self.status_var.set("Monitoring (logging stopped).")

    # ---------------- Graph update ----------------
    def _update_graph_series(self, sys_snap):
        try:
            now_epoch = time.time()

            used_pct = float(sys_snap.get("used_percent", 0.0))
            swap_pct = float(sys_snap.get("swap_percent", 0.0))
            avail_gb = float(sys_snap.get("available_gb", 0.0))

            cp = sys_snap.get("commit_percent", "")
            commit_pct = float(cp) if cp != "" else float("nan")

            pf = sys_snap.get("page_faults_per_sec", "")
            pfv = float(pf) if pf != "" else float("nan")

            self.ts_series.append(now_epoch)
            self.ram_series.append(used_pct)
            self.swap_series.append(swap_pct)
            self.avail_series.append(avail_gb)
            self.commit_series.append(commit_pct)
            self.pf_series.append(pfv)
        except Exception:
            return

    def _redraw_graph(self):
        if not HAS_MPL or self.axL is None or self.axR is None:
            return

        if len(self.ts_series) < 2:
            self.axL.cla()
            self.axR.cla()
            try:
                self.canvas.draw_idle()
            except Exception:
                pass
            return

        t0 = self.ts_series[0]
        xs = [t - t0 for t in self.ts_series]

        self.axL.cla()
        self.axR.cla()

        # ---- labels / grid ----
        self.axL.set_title("Selected metrics over time", pad=20)
        self.axL.set_xlabel("seconds (relative)")
        self.axL.set_ylabel("%")
        self.axL.grid(True, alpha=0.3)

        # ✅ make sure the twin axis really lives on the RIGHT
        self.axR.set_ylabel("GB / PF/s")
        self.axR.yaxis.set_label_position("right")
        self.axR.yaxis.tick_right()

        handles = []
        labels = []

        # left axis (%)
        if self.show_ram.get():
            h, = self.axL.plot(xs, list(self.ram_series), label="RAM %")
            handles.append(h); labels.append("RAM %")
        if self.show_swap.get():
            h, = self.axL.plot(xs, list(self.swap_series), label="Swap %")
            handles.append(h); labels.append("Swap %")
        if self.show_commit.get():
            h, = self.axL.plot(xs, list(self.commit_series), label="Commit %")
            handles.append(h); labels.append("Commit %")

        # right axis (GB + PF/s)
        if self.show_avail.get():
            h, = self.axR.plot(xs, list(self.avail_series), label="Avail GB")
            handles.append(h); labels.append("Avail GB")
        if self.show_pf.get():
            h, = self.axR.plot(xs, list(self.pf_series), label="PageFaults/sec")
            handles.append(h); labels.append("PageFaults/sec")

        # markers
        for (epoch, level) in list(self.alert_markers):
            x = epoch - t0
            if x < 0:
                continue
            ls = "--" if level == "CRIT" else ":"
            self.axL.axvline(x=x, linestyle=ls, linewidth=1, alpha=0.6)

        self.axL.set_ylim(0, 100)

        # ✅ legend ABOVE plot (not inside)
        if handles:
            self.axL.legend(
                handles, labels,
                loc="lower left",
                bbox_to_anchor=(0, 1.02),
                borderaxespad=0.0,
                ncol=min(3, len(labels)),
                fontsize=8,
                frameon=True
            )

        # ✅ HARD fix for your screenshot: give left margin more room
        # then let matplotlib tighten safely
        try:
            self.fig.subplots_adjust(left=0.12, right=0.92, top=0.80, bottom=0.25)
            self.fig.tight_layout()
            self.canvas.draw_idle()
        except Exception:
            pass


    # ---------------- UI refresh ----------------
    def _refresh_ui(self):
        if self.monitor_running:
            with self.lock:
                sys_snap = self.latest_sys
                top = self.latest_top[:]
                top_err = self.last_top_err

            if sys_snap:
                if "error" in sys_snap:
                    self.status_var.set(sys_snap["error"])
                else:
                    used_pct = float(sys_snap["used_percent"])
                    total = float(sys_snap["total_gb"])
                    avail = float(sys_snap["available_gb"])
                    used = float(sys_snap["used_gb"])

                    swap_pct = float(sys_snap["swap_percent"])
                    swap_total = float(sys_snap["swap_total_gb"])
                    swap_used = float(sys_snap["swap_used_gb"])

                    self.ram_big.config(text=f"RAM: {used_pct:.1f} %")
                    self.ram_small.config(text=f"Free: {avail:.2f} GB   Used: {used:.2f} GB / {total:.2f} GB")
                    self.ram_bar["value"] = used_pct

                    self.swap_big.config(text=f"Swap: {swap_pct:.1f} %")
                    self.swap_small.config(text=f"Used: {swap_used:.2f} GB / {swap_total:.2f} GB")
                    self.swap_bar["value"] = swap_pct

                    commit_pct_raw = sys_snap.get("commit_percent", "")
                    pf_raw = sys_snap.get("page_faults_per_sec", "")

                    if commit_pct_raw == "":
                        commit_txt = "Commit: -"
                    else:
                        cu = sys_snap.get("commit_used_gb", "")
                        cl = sys_snap.get("commit_limit_gb", "")
                        if cu != "" and cl != "":
                            commit_txt = f"Commit: {commit_pct_raw}% ({cu} / {cl} GB)"
                        else:
                            commit_txt = f"Commit: {commit_pct_raw}%"

                    pf_txt = f"Page Faults/sec: {pf_raw}" if pf_raw != "" else "Page Faults/sec: -"
                    self.extra_var.set(commit_txt + " | " + pf_txt)

                    # Efficiency calculation
                    commit_pct = None
                    try:
                        if commit_pct_raw != "":
                            commit_pct = float(commit_pct_raw)
                    except Exception:
                        commit_pct = None

                    pf_val = None
                    try:
                        if pf_raw != "":
                            pf_val = float(pf_raw)
                    except Exception:
                        pf_val = None

                    score, label, reasons = memory_efficiency_score(
                        used_pct=used_pct,
                        swap_pct=swap_pct,
                        commit_pct=commit_pct,
                        pf_per_sec=pf_val,
                        avail_gb=avail,
                        total_gb=total
                    )

                    why = (" | " + ", ".join(reasons)) if reasons else ""
                    self.eff_var.set(f"Efficiency: {score}/100 ({label}){why}")

                    # store in snapshot for CSV/log
                    sys_snap["efficiency_score"] = score
                    sys_snap["efficiency_label"] = label

                    # Alerts
                    level = "OK"
                    msg = "OK"
                    if used_pct >= 92 or swap_pct >= 15:
                        level = "CRIT"
                        msg = "HIGH MEMORY PRESSURE: RAM/Swap critical!"
                        self.dot.itemconfig(self.dot_id, fill="#e74c3c")
                    elif used_pct >= 85 or swap_pct >= 10:
                        level = "WARN"
                        msg = "Warning: Memory usage is high."
                        self.dot.itemconfig(self.dot_id, fill="#f1c40f")
                    else:
                        self.dot.itemconfig(self.dot_id, fill="#2ecc71")

                    self.alert_text_var.set(msg)

                    if level != self.last_alert_level:
                        self.last_alert_level = level
                        self.alert_markers.append((time.time(), level))
                        if self.alert_beep_var.get():
                            beep()

                    self._update_graph_series(sys_snap)
                    self._redraw_graph()

            # update top table
            if bool(self.enable_top_var.get()):
                for item in self.tree.get_children():
                    self.tree.delete(item)

                self._top_pid_map = {}
                for name, rss, pids in top:
                    if name:
                        self._top_pid_map[name] = pids
                        self.tree.insert("", "end", values=(name, f"{rss:.2f}"))
            else:
                for item in self.tree.get_children():
                    self.tree.delete(item)
                self._top_pid_map = {}

            if top_err:
                self.status_var.set(top_err)

        self.after(200, self._refresh_ui)

    def _drain_log_queue(self):
        try:
            while True:
                msg = self.log_queue.get_nowait()
                self.log_text.insert("end", msg + "\n")
                self.log_text.see("end")
                lines = int(self.log_text.index("end-1c").split(".")[0])
                if lines > 140:
                    self.log_text.delete("1.0", "31.0")
        except queue.Empty:
            pass
        self.after(150, self._drain_log_queue)

    def open_csv(self):
        path = self.last_written_csv
        if not path:
            candidate = resolve_path(self.out_var.get())
            if os.path.exists(candidate):
                path = candidate

        if not path:
            messagebox.showinfo("CSV", "No CSV file has been created yet. Start logging first.")
            return

        path = resolve_path(path)
        if not os.path.exists(path):
            messagebox.showinfo("CSV", f"CSV file not found:\n{path}\n\nStart logging and wait 1–2 seconds.")
            return

        try:
            if sys.platform.startswith("win"):
                os.startfile(path)  # type: ignore
            elif sys.platform.startswith("darwin"):
                subprocess.Popen(["open", path])
            else:
                subprocess.Popen(["xdg-open", path])
        except Exception as e:
            messagebox.showerror("CSV", f"Cannot open file:\n{e}")

if __name__ == "__main__":
    ensure_dir(os.path.join(BASE_DIR, "data"))
    app = MemoryDashboard()
    app.mainloop()
