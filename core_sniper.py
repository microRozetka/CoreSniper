"""
CoreSniper - Крипто-ректальный анализатор процессора и оптимизатор привязки потоков для Process Lasso.
Оптимизировано для соревновательных игр (CS2, Dota 2) на процессорах AMD Ryzen и Intel Core.
"""

import sys
import os
import time
import math
import ctypes
from ctypes import wintypes
import statistics
import winreg
import csv
import platform
import psutil

if sys.platform == 'win32':
    try:
        ctypes.windll.kernel32.SetConsoleOutputCP(65001)
        ctypes.windll.kernel32.SetConsoleCP(65001)
    except Exception:
        pass
    os.system('')
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass

def get_app_dir() -> str:
    if getattr(sys, 'frozen', False):
        return os.path.dirname(sys.executable)
    return os.path.dirname(os.path.abspath(__file__))

# razukrashki
class Color:
    HEADER    = '\033[95m'
    BLUE      = '\033[94m'
    CYAN      = '\033[96m'
    GREEN     = '\033[92m'
    YELLOW    = '\033[93m'
    RED       = '\033[91m'
    BOLD      = '\033[1m'
    UNDERLINE = '\033[4m'
    DIM       = '\033[2m'
    RESET     = '\033[0m'

class GROUP_AFFINITY(ctypes.Structure):
    _fields_ = [
        ('Mask', ctypes.c_size_t),
        ('Group', wintypes.WORD),
        ('Reserved', wintypes.WORD * 3)
    ]

kernel32 = ctypes.WinDLL('kernel32', use_last_error=True)
kernel32.GetCurrentThread.restype = wintypes.HANDLE
kernel32.SetThreadGroupAffinity.restype = wintypes.BOOL
kernel32.SetThreadGroupAffinity.argtypes = [
    wintypes.HANDLE,
    ctypes.POINTER(GROUP_AFFINITY),
    ctypes.POINTER(GROUP_AFFINITY)
]

try:
    pdh = ctypes.WinDLL('pdh', use_last_error=True)
except Exception:
    pdh = None

class PDH_FMT_COUNTERVALUE(ctypes.Structure):
    class _FMT(ctypes.Union):
        _fields_ = [
            ('longValue', ctypes.c_long),
            ('doubleValue', ctypes.c_double),
            ('largeValue', ctypes.c_int64),
            ('AnsiStringValue', ctypes.c_char_p),
            ('WideStringValue', ctypes.c_wchar_p),
        ]
    _fields_ = [
        ('CStatus', wintypes.DWORD),
        ('fmt', _FMT),
    ]

PDH_FMT_DOUBLE = 0x00000200


def is_admin() -> bool:
    try:
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except Exception:
        return False


def get_cpu_model_name() -> str:
    try:
        key = winreg.OpenKey(
            winreg.HKEY_LOCAL_MACHINE,
            r'HARDWARE\DESCRIPTION\System\CentralProcessor\0'
        )
        val, _ = winreg.QueryValueEx(key, 'ProcessorNameString')
        winreg.CloseKey(key)
        return str(val).strip()
    except Exception:
        return platform.processor() or "Неизвестный процессор"


# =============================
# step 1: detect topology
# =============================
class CoreInfo:
    def __init__(self, core_id: int, threads: list[int], smt: bool, eff_class: int, mask: int, group: int):
        self.core_id = core_id            # Физический номер ядра (0..N-1)
        self.threads = sorted(threads)    # Логические потоки 0-based
        self.smt = smt                    # SMT/HyperThreading активен
        self.eff_class = eff_class        # 0 = стандарт/эффективное, 1+ = производительное
        self.core_type = "Core"           # P-Core / E-Core / Core
        self.mask = mask                  # Битовая маска ядра
        self.group = group                # Группа процессоров (обычно 0)
        self.ccx_id = 0                   # ID группы общего кэша L3 (CCX)

    @property
    def primary_thread(self) -> int:
        return self.threads[0] if self.threads else 0


class L3CacheInfo:
    def __init__(self, l3_id: int, size_kb: int, mask: int, group: int):
        self.l3_id = l3_id
        self.size_kb = size_kb
        self.mask = mask
        self.group = group
        self.core_ids: list[int] = []


class CpuTopology:
    def __init__(self):
        self.cpu_name = get_cpu_model_name()
        self.cores: list[CoreInfo] = []
        self.l3_caches: list[L3CacheInfo] = []
        self.total_logical_processors = 0
        self.is_hybrid = False
        self._detect_topology()

    def _detect_topology(self):
        length = wintypes.DWORD(0)
        kernel32.GetLogicalProcessorInformationEx(65535, None, ctypes.byref(length))
        if length.value == 0:
            raise RuntimeError("Не удалось получить размер буфера топологии процессора.")

        buf = (ctypes.c_ubyte * length.value)()
        if not kernel32.GetLogicalProcessorInformationEx(65535, buf, ctypes.byref(length)):
            raise ctypes.WinError(ctypes.get_last_error())

        raw_cores = []
        raw_l3 = []

        offset = 0
        while offset < length.value:
            rel = int.from_bytes(bytes(buf[offset:offset+4]), 'little')
            size = int.from_bytes(bytes(buf[offset+4:offset+8]), 'little')
            if size == 0:
                break
            data = bytes(buf[offset+8:offset+size])

            if rel == 0:  # RelationProcessorCore
                flags = data[0]
                eff_class = data[1]
                mask = int.from_bytes(data[24:32], 'little')
                grp = int.from_bytes(data[32:34], 'little')
                smt = bool(flags & 1)
                threads = [i for i in range(64) if (mask & (1 << i))]
                raw_cores.append((threads, smt, eff_class, mask, grp))

            elif rel == 2:  # RelationCache
                level = data[0]
                csize = int.from_bytes(data[4:8], 'little')
                if level == 3:  # L3 cache
                    mask = int.from_bytes(data[32:40], 'little')
                    grp = int.from_bytes(data[40:42], 'little')
                    raw_l3.append((csize // 1024, mask, grp))

            offset += size

        raw_cores.sort(key=lambda item: item[0][0] if item[0] else 0)

        for idx, (threads, smt, eff_class, mask, grp) in enumerate(raw_cores):
            core = CoreInfo(idx, threads, smt, eff_class, mask, grp)
            self.cores.append(core)

        raw_l3.sort(key=lambda item: item[1])
        for idx, (size_kb, mask, grp) in enumerate(raw_l3):
            l3 = L3CacheInfo(idx, size_kb, mask, grp)
            self.l3_caches.append(l3)

        if not self.l3_caches:
            all_mask = 0
            for c in self.cores:
                all_mask |= c.mask
            self.l3_caches.append(L3CacheInfo(0, 0, all_mask, 0))

        for core in self.cores:
            assigned_ccx = 0
            for l3 in self.l3_caches:
                if (core.mask & l3.mask) != 0 and core.group == l3.group:
                    assigned_ccx = l3.l3_id
                    l3.core_ids.append(core.core_id)
                    break
            core.ccx_id = assigned_ccx

        eff_classes = set(c.eff_class for c in self.cores)
        if len(eff_classes) > 1:
            self.is_hybrid = True
            max_eff = max(eff_classes)
            for c in self.cores:
                if c.eff_class == max_eff:
                    c.core_type = "P-Core (Perf)"
                else:
                    c.core_type = "E-Core (Eff)"
        else:
            for c in self.cores:
                c.core_type = "Standard Core"

        self.total_logical_processors = sum(len(c.threads) for c in self.cores)

    def print_topology_table(self):
        print(f"\n{Color.CYAN}{'='*75}{Color.RESET}")
        print(f"{Color.BOLD} ТОПОЛОГИЯ ПРОЦЕССОРА: {self.cpu_name}{Color.RESET}")
        print(f" Физических ядер: {Color.GREEN}{len(self.cores)}{Color.RESET} | "
              f"Логических потоков: {Color.GREEN}{self.total_logical_processors}{Color.RESET} | "
              f"Групп L3/CCX: {Color.GREEN}{len(self.l3_caches)}{Color.RESET}")
        if self.is_hybrid:
            print(f" {Color.YELLOW}[!] Обнаружена гибридная архитектура Intel (P-Core / E-Core){Color.RESET}")
        print(f"{Color.CYAN}{'='*75}{Color.RESET}")

        header = f"{'Ядро':^6} | {'Потоки (Lasso)':^16} | {'SMT/HT':^8} | {'Группа L3 / CCX':^17} | {'Тип ядра':^16}"
        print(f"{Color.BOLD}{header}{Color.RESET}")
        print("-" * 75)

        for c in self.cores:
            th_str = ", ".join(str(t) for t in c.threads)
            smt_str = "Да (2)" if c.smt and len(c.threads) > 1 else "Нет (1)"
            l3_info = self.l3_caches[c.ccx_id]
            l3_size_mb = f"{l3_info.size_kb // 1024}MB" if l3_info.size_kb > 0 else ""
            ccx_str = f"CCX {c.ccx_id} ({l3_size_mb})" if l3_size_mb else f"CCX {c.ccx_id}"

            color = Color.GREEN if "P-Core" in c.core_type or not self.is_hybrid else Color.YELLOW
            print(f" {c.core_id:^4} | {th_str:^16} | {smt_str:^8} | {ccx_str:^17} | {color}{c.core_type:^16}{Color.RESET}")

        print("-" * 75)
        print(f"{Color.DIM}* Примечание: нумерация логических потоков начинается с 0, полностью совпадая с Process Lasso.{Color.RESET}\n")


# ==============================================================================
# step 2: benchmarking cores
# ==============================================================================
class PdhMonitor:
    def __init__(self):
        self.available = pdh is not None
        self.h_query = wintypes.HANDLE()
        if self.available:
            res = pdh.PdhOpenQueryW(None, 0, ctypes.byref(self.h_query))
            if res != 0:
                self.available = False

    def add_counter(self, counter_path: str) -> wintypes.HANDLE | None:
        if not self.available:
            return None
        h_counter = wintypes.HANDLE()
        res = pdh.PdhAddEnglishCounterW(self.h_query, counter_path, 0, ctypes.byref(h_counter))
        if res == 0:
            return h_counter
        res2 = pdh.PdhAddCounterW(self.h_query, counter_path, 0, ctypes.byref(h_counter))
        if res2 == 0:
            return h_counter
        return None

    def collect(self) -> bool:
        if not self.available:
            return False
        return pdh.PdhCollectQueryData(self.h_query) == 0

    def get_double(self, h_counter: wintypes.HANDLE) -> float:
        if not self.available or not h_counter:
            return 0.0
        val = PDH_FMT_COUNTERVALUE()
        res = pdh.PdhGetFormattedCounterValue(h_counter, PDH_FMT_DOUBLE, None, ctypes.byref(val))
        if res == 0 and val.CStatus == 0:
            return float(val.fmt.doubleValue)
        return 0.0

    def close(self):
        if self.available and self.h_query:
            try:
                pdh.PdhCloseQuery(self.h_query)
            except Exception:
                pass
            self.available = False


class BenchmarkResult:
    def __init__(self, core_id: int, thread_id: int, runs: list[float], perf_pct: float, real_freq_mhz: float):
        self.core_id = core_id
        self.thread_id = thread_id
        self.runs = runs
        self.median_speed = statistics.median(runs) if runs else 0.0
        self.perf_pct = perf_pct                # % Processor Performance
        self.real_freq_mhz = real_freq_mhz      # Расчётная реальная частота в MHz
        self.rank = 0
        self.diff_from_best_pct = 0.0


def run_single_thread_workload(duration_sec: float) -> int:
    start_time = time.perf_counter()
    end_time = start_time + duration_sec
    iterations = 0
    chunk = 50000

    while time.perf_counter() < end_time:
        x = 123456789
        for _ in range(chunk):
            x = (x * 1103515245 + 12345) & 0x7FFFFFFF
            x ^= (x >> 13)
            x = (x * 16807) & 0x7FFFFFFF
        iterations += chunk

    return iterations


def benchmark_all_cores(topology: CpuTopology, duration_sec: float = 3.0, repeats: int = 3) -> dict[int, BenchmarkResult]:
    print(f"\n{Color.CYAN}{'='*75}{Color.RESET}")
    print(f"{Color.BOLD} ТЕСТ ПРОИЗВОДИТЕЛЬНОСТИ ФИЗИЧЕСКИХ ЯДЕР{Color.RESET}")
    print(f" Нагрузка: {duration_sec:.1f} сек на ядро, {repeats} повтора(ов), вычисление медианы.")
    print(f" Проверяются физические ядра по отдельности (SMT-побратим в простое).")
    print(f"{Color.CYAN}{'='*75}{Color.RESET}")

    current_thread = kernel32.GetCurrentThread()
    prev_affinity = GROUP_AFFINITY()

    results: dict[int, BenchmarkResult] = {}

    for c in topology.cores:
        target_thread = c.primary_thread
        print(f"\nТестирование Ядра {Color.BOLD}{c.core_id}{Color.RESET} (поток {target_thread}, CCX {c.ccx_id})...")

        target_affinity = GROUP_AFFINITY()
        target_affinity.Mask = (1 << (target_thread % 64))
        target_affinity.Group = c.group

        success = kernel32.SetThreadGroupAffinity(current_thread, ctypes.byref(target_affinity), ctypes.byref(prev_affinity))
        if not success:
            print(f"{Color.RED}[!] Ошибка привязки потока к ядру {c.core_id}. Пропуск.{Color.RESET}")
            continue

        runs = []
        perf_samples = []
        freq_samples = []

        try:
            for rep in range(1, repeats + 1):
                mon = PdhMonitor()
                h_perf = mon.add_counter(f'\\Processor Information({c.group},{target_thread % 64})\\% Processor Performance')
                h_freq = mon.add_counter(f'\\Processor Information({c.group},{target_thread % 64})\\Processor Frequency')
                mon.collect()

                t0 = time.perf_counter()
                iters = run_single_thread_workload(duration_sec)
                actual_dur = time.perf_counter() - t0
                speed = iters / actual_dur
                runs.append(speed)

                mon.collect()
                perf_val = mon.get_double(h_perf)
                freq_val = mon.get_double(h_freq)
                mon.close()

                if perf_val > 0:
                    perf_samples.append(perf_val)
                if freq_val > 0:
                    freq_samples.append(freq_val)

                freq_str = ""
                if perf_val > 0 and freq_val > 0:
                    real_mhz = freq_val * (perf_val / 100.0)
                    freq_str = f" | Частота: ~{real_mhz:.0f} MHz ({perf_val:.1f}%)"

                print(f"   Прогон {rep}/{repeats}: {Color.GREEN}{speed:,.0f}{Color.RESET} итер/сек{freq_str}")

        finally:
            kernel32.SetThreadGroupAffinity(current_thread, ctypes.byref(prev_affinity), None)

        avg_perf = statistics.mean(perf_samples) if perf_samples else 0.0
        avg_base_freq = statistics.mean(freq_samples) if freq_samples else 0.0
        real_freq = avg_base_freq * (avg_perf / 100.0) if avg_perf > 0 and avg_base_freq > 0 else 0.0

        res = BenchmarkResult(c.core_id, target_thread, runs, avg_perf, real_freq)
        results[c.core_id] = res

    sorted_res = sorted(results.values(), key=lambda r: r.median_speed, reverse=True)
    best_speed = sorted_res[0].median_speed if sorted_res else 1.0

    for rank, r in enumerate(sorted_res, 1):
        r.rank = rank
        r.diff_from_best_pct = ((best_speed - r.median_speed) / best_speed) * 100.0

    print_benchmark_table(topology, results)
    return results


def print_benchmark_table(topology: CpuTopology, results: dict[int, BenchmarkResult]):
    """Вывод рейтинга ядер по скорости."""
    print(f"\n{Color.CYAN}{'='*80}{Color.RESET}")
    print(f"{Color.BOLD} ИТОГОВЫЙ РЕЙТИНГ ЯДЕР ПО ЧИСТОЙ СКОРОСТИ (ОДНОПОТОК){Color.RESET}")
    print(f"{Color.CYAN}{'='*80}{Color.RESET}")

    header = f"{'Ранг':^6} | {'Ядро':^6} | {'CCX':^6} | {'Скорость (медиана)':^22} | {'Отставание':^12} | {'Частота (PDH)':^16}"
    print(f"{Color.BOLD}{header}{Color.RESET}")
    print("-" * 80)

    sorted_res = sorted(results.values(), key=lambda r: r.rank)
    for r in sorted_res:
        c = topology.cores[r.core_id]
        diff_str = "Лидер" if r.rank == 1 else f"-{r.diff_from_best_pct:.2f}%"
        freq_str = f"~{r.real_freq_mhz:.0f} MHz" if r.real_freq_mhz > 0 else "N/A"
        rank_color = Color.GREEN if r.rank <= 4 else (Color.YELLOW if r.rank <= 6 else Color.RESET)

        print(f" {rank_color}#{r.rank:<4}{Color.RESET} | "
              f"Core {r.core_id:<2} | "
              f"CCX {c.ccx_id:<2} | "
              f"{r.median_speed:15,.0f} it/s   | "
              f"{diff_str:^12} | "
              f"{freq_str:^16}")

    print("-" * 80)
    print(f"{Color.DIM}* Измерено на изолированном потоке без конкуренции SMT-потока.{Color.RESET}\n")


# =========
# step 3
# =========
class ThreadProfile:
    def __init__(self, thread_id: int):
        self.thread_id = thread_id
        self.cpu_samples: list[float] = []
        self.interrupt_samples: list[float] = []
        self.dpc_samples: list[float] = []

    @property
    def avg_cpu(self) -> float:
        return statistics.mean(self.cpu_samples) if self.cpu_samples else 0.0

    @property
    def p95_cpu(self) -> float:
        if not self.cpu_samples:
            return 0.0
        if len(self.cpu_samples) < 2:
            return self.cpu_samples[0]
        try:
            return float(statistics.quantiles(self.cpu_samples, n=100)[94])
        except Exception:
            s = sorted(self.cpu_samples)
            idx = int(0.95 * (len(s) - 1))
            return float(s[idx])

    @property
    def avg_interrupt(self) -> float:
        return statistics.mean(self.interrupt_samples) if self.interrupt_samples else 0.0

    @property
    def avg_dpc(self) -> float:
        return statistics.mean(self.dpc_samples) if self.dpc_samples else 0.0


def profile_background(topology: CpuTopology, duration_minutes: float = 5.0) -> dict[int, ThreadProfile]:
    total_seconds = max(5, int(duration_minutes * 60))
    num_threads = topology.total_logical_processors

    print(f"\n{Color.CYAN}{'='*80}{Color.RESET}")
    print(f"{Color.BOLD} СБОР ПРОФИЛЯ ФОНОВОЙ НАГРУЗКИ WINDOWS{Color.RESET}")
    print(f" Время мониторинга: {Color.YELLOW}{duration_minutes:.1f} мин ({total_seconds} сек){Color.RESET}")
    print(f" Отслеживаются: загрузка ядер, системные аппаратные прерывания (ISR) и вызовы DPC.")
    print(f"{Color.DIM} Нажмите Ctrl+C в любой момент для досрочного завершения с сохранением собранных данных.{Color.RESET}")
    print(f"{Color.CYAN}{'='*80}{Color.RESET}\n")

    profiles = {i: ThreadProfile(i) for i in range(num_threads)}

    mon = PdhMonitor()
    int_handles = {}
    dpc_handles = {}

    thread_to_group = {}
    for c in topology.cores:
        for t in c.threads:
            thread_to_group[t] = (c.group, t % 64)

    if mon.available:
        for i in range(num_threads):
            grp, rel_t = thread_to_group.get(i, (0, i % 64))
            h_int = mon.add_counter(f'\\Processor Information({grp},{rel_t})\\% Interrupt Time')
            if h_int:
                int_handles[i] = h_int
            h_dpc = mon.add_counter(f'\\Processor Information({grp},{rel_t})\\% DPC Time')
            if h_dpc:
                dpc_handles[i] = h_dpc
        mon.collect()

    psutil.cpu_percent(percpu=True)

    elapsed = 0
    try:
        while elapsed < total_seconds:
            time.sleep(1.0)
            elapsed += 1

            cpu_percents = psutil.cpu_percent(percpu=True)
            if mon.available:
                mon.collect()

            for i in range(min(num_threads, len(cpu_percents))):
                profiles[i].cpu_samples.append(cpu_percents[i])
                if i in int_handles:
                    profiles[i].interrupt_samples.append(mon.get_double(int_handles[i]))
                if i in dpc_handles:
                    profiles[i].dpc_samples.append(mon.get_double(dpc_handles[i]))

            pct = (elapsed / total_seconds) * 100.0
            bar_len = 30
            filled = int(bar_len * elapsed // total_seconds)
            bar = '█' * filled + '░' * (bar_len - filled)
            sys.stdout.write(f"\rПрогресс: [{Color.GREEN}{bar}{Color.RESET}] {pct:5.1f}% ({elapsed}/{total_seconds}с)")
            sys.stdout.flush()

    except KeyboardInterrupt:
        print(f"\n{Color.YELLOW}[!] Мониторинг прерван пользователем. Использовано {elapsed} сек собранных данных.{Color.RESET}")

    finally:
        mon.close()
        print("\n")

    print_profile_table(topology, profiles)
    return profiles


def print_profile_table(topology: CpuTopology, profiles: dict[int, ThreadProfile]):
    """Вывод собранного профиля фоновой нагрузки."""
    print(f"\n{Color.CYAN}{'='*80}{Color.RESET}")
    print(f"{Color.BOLD} РЕЗУЛЬТАТЫ ПРОФИЛИРОВАНИЯ ФОНОВОЙ НАГРУЗКИ ПО ПОТОКАМ{Color.RESET}")
    print(f"{Color.CYAN}{'='*80}{Color.RESET}")

    header = f"{'Поток':^7} | {'Ядро':^6} | {'CCX':^6} | {'Средняя CPU%':^14} | {'Пик CPU (95%)':^14} | {'Interrupt%':^12} | {'DPC%':^8}"
    print(f"{Color.BOLD}{header}{Color.RESET}")
    print("-" * 80)

    for c in topology.cores:
        for t in c.threads:
            prof = profiles.get(t)
            if not prof:
                continue
            avg_c = prof.avg_cpu
            p95_c = prof.p95_cpu
            avg_i = prof.avg_interrupt
            avg_d = prof.avg_dpc

            int_color = Color.RED if avg_i > 2.0 or avg_d > 1.0 else Color.RESET
            t_color = Color.YELLOW if t == 0 else Color.RESET

            print(f" {t_color}{t:^5}{Color.RESET} | "
                  f"Core {c.core_id:<2} | "
                  f"CCX {c.ccx_id:<2} | "
                  f"{avg_c:12.2f}% | "
                  f"{p95_c:12.2f}% | "
                  f"{int_color}{avg_i:10.2f}%{Color.RESET} | "
                  f"{int_color}{avg_d:6.2f}%{Color.RESET}")

    print("-" * 80)
    print(f"{Color.DIM}* Потоки с высокой долей Interrupt/DPC (особенно поток 0) вызывают микрофризы в CS2/Dota 2.{Color.RESET}\n")


# ==============================================================================
# step 4: strashnaya huina
# ==============================================================================
class CoreScoreDetails:
    def __init__(self, core_id: int):
        self.core_id = core_id
        self.norm_speed = 100.0
        self.penalty_bg = 0.0
        self.penalty_dpc_int = 0.0
        self.penalty_core0 = 0.0
        self.final_score = 0.0


class OptimizationResult:
    def __init__(self):
        self.selected_ccx = 0
        self.selected_core_ids: list[int] = []
        self.threads_smt: list[int] = []
        self.threads_nosmt: list[int] = []
        self.mask_smt = 0
        self.mask_nosmt = 0
        self.core_scores: dict[int, CoreScoreDetails] = {}
        self.k = 4


def calculate_scores_and_recommend(
    topology: CpuTopology,
    benchmarks: dict[int, BenchmarkResult] | None,
    profiles: dict[int, ThreadProfile] | None,
    k_cores: int = 4
) -> OptimizationResult:
    res = OptimizationResult()
    res.k = k_cores

    max_speed = 1.0
    if benchmarks:
        max_speed = max(b.median_speed for b in benchmarks.values()) if benchmarks else 1.0

    for c in topology.cores:
        sc = CoreScoreDetails(c.core_id)

        if benchmarks and c.core_id in benchmarks:
            speed = benchmarks[c.core_id].median_speed
            sc.norm_speed = (speed / max_speed) * 100.0
        else:
            sc.norm_speed = 100.0

        if profiles:
            thread_avgs = [profiles[t].avg_cpu for t in c.threads if t in profiles]
            thread_p95s = [profiles[t].p95_cpu for t in c.threads if t in profiles]
            thread_ints = [profiles[t].avg_interrupt for t in c.threads if t in profiles]
            thread_dpcs = [profiles[t].avg_dpc for t in c.threads if t in profiles]

            avg_cpu = statistics.mean(thread_avgs) if thread_avgs else 0.0
            p95_cpu = max(thread_p95s) if thread_p95s else 0.0
            sum_int = sum(thread_ints) if thread_ints else 0.0
            sum_dpc = sum(thread_dpcs) if thread_dpcs else 0.0

            sc.penalty_bg = (avg_cpu * 1.5) + (p95_cpu * 0.5)

            sc.penalty_dpc_int = (sum_int * 2.5) + (sum_dpc * 5.0)

        if 0 in c.threads:
            sc.penalty_core0 = 20.0

        if topology.is_hybrid and "E-Core" in c.core_type:
            sc.penalty_core0 += 150.0

        sc.final_score = sc.norm_speed - sc.penalty_bg - sc.penalty_dpc_int - sc.penalty_core0
        res.core_scores[c.core_id] = sc

    best_ccx = 0
    best_ccx_score = -999999.0
    best_ccx_selected_cores: list[int] = []

    for l3 in topology.l3_caches:
        ccx_cores = [c for c in topology.cores if c.core_id in l3.core_ids]
        if topology.is_hybrid:
            p_cores = [c for c in ccx_cores if "P-Core" in c.core_type]
            if p_cores:
                ccx_cores = p_cores

        if not ccx_cores:
            continue

        sorted_cores = sorted(ccx_cores, key=lambda c: res.core_scores[c.core_id].final_score, reverse=True)

        take_count = min(k_cores, len(sorted_cores))
        chosen = sorted_cores[:take_count]
        chosen_ids = [c.core_id for c in chosen]

        total_score = sum(res.core_scores[cid].final_score for cid in chosen_ids)

        if total_score > best_ccx_score:
            best_ccx_score = total_score
            best_ccx = l3.l3_id
            best_ccx_selected_cores = chosen_ids

    res.selected_ccx = best_ccx
    res.selected_core_ids = sorted(best_ccx_selected_cores)

    all_smt_threads = []
    all_nosmt_threads = []

    for cid in res.selected_core_ids:
        c = topology.cores[cid]
        all_smt_threads.extend(c.threads)

        if profiles:
            best_th = min(c.threads, key=lambda t: (profiles[t].avg_interrupt + profiles[t].avg_dpc, profiles[t].avg_cpu))
        else:
            best_th = c.primary_thread
        all_nosmt_threads.append(best_th)

    res.threads_smt = sorted(all_smt_threads)
    res.threads_nosmt = sorted(all_nosmt_threads)

    res.mask_smt = sum(1 << t for t in res.threads_smt)
    res.mask_nosmt = sum(1 << t for t in res.threads_nosmt)

    return res


def print_recommendation_report(topology: CpuTopology, opt: OptimizationResult):
    print(f"\n{Color.CYAN}{'='*80}{Color.RESET}")
    print(f"{Color.BOLD} ИТОГОВЫЙ СКОРИНГ И ВЫБОР ОПТИМАЛЬНОЙ ГРУППЫ ЯДЕР{Color.RESET}")
    print(f"{Color.CYAN}{'='*80}{Color.RESET}")

    header = f"{'Ядро':^6} | {'CCX':^6} | {'Скорость':^10} | {'Штраф фона':^12} | {'Штраф DPC/Int':^14} | {'Штраф Ядра 0':^13} | {'ИТОГОВЫЙ СКОР':^14}"
    print(f"{Color.BOLD}{header}{Color.RESET}")
    print("-" * 80)

    for c in topology.cores:
        sc = opt.core_scores.get(c.core_id)
        if not sc:
            continue
        selected_mark = f"{Color.GREEN}★ {Color.RESET}" if c.core_id in opt.selected_core_ids else "  "
        print(f"{selected_mark}Core {c.core_id:<2} | "
              f"CCX {c.ccx_id:<2} | "
              f"{sc.norm_speed:8.1f}   | "
              f"-{sc.penalty_bg:10.2f}  | "
              f"-{sc.penalty_dpc_int:12.2f}  | "
              f"-{sc.penalty_core0:11.2f}  | "
              f"{Color.BOLD}{sc.final_score:12.2f}{Color.RESET}")

    print("-" * 80)
    print(f"{Color.GREEN}★ Отмечены ядра, вошедшие в оптимальный пул для игр.{Color.RESET}")

    print(f"\n{Color.YELLOW}{'='*80}{Color.RESET}")
    print(f"{Color.BOLD} НАСТРОЙКА ДЛЯ PROCESS LASSO (CS2 / Dota 2 / Cyberpunk и др.){Color.RESET}")
    print(f"{Color.YELLOW}{'='*80}{Color.RESET}")

    print(f"Выбран лучший блок: {Color.BOLD}CCX {opt.selected_ccx}{Color.RESET} (Физические ядра: {opt.selected_core_ids})")
    if len(opt.selected_core_ids) < opt.k:
        print(f"{Color.YELLOW}[i] Запрошено ядер: {opt.k}, но в одном CCX доступно {len(opt.selected_core_ids)} ядер. Выбраны все доступные ядра одного блока для исключения Cross-CCX задержек.{Color.RESET}")
    print(f"{Color.DIM}Привязка исключительно внутри одного CCX исключает межъядерные задержки кэша L3 (Cross-CCX penalty).{Color.RESET}\n")

    smt_list_str = ",".join(str(t) for t in opt.threads_smt)
    nosmt_list_str = ",".join(str(t) for t in opt.threads_nosmt)

    print(f"{Color.BOLD}1. ВАРИАНТ «С SMT» (Максимальная производительность для многопоточных сцен):{Color.RESET}")
    print(f"   Потоки (CPU List) : {Color.GREEN}{smt_list_str}{Color.RESET}")
    print(f"   Hex-маска аффинити: {Color.GREEN}0x{opt.mask_smt:04X}{Color.RESET}  ({len(opt.threads_smt)} логических потоков)")
    print(f"   Подходит для      : CS2, Dota 2, Cyberpunk 2077, стриминга и записи видео.")

    print(f"\n{Color.BOLD}2. ВАРИАНТ «БЕЗ SMT» (Минимальный инпут-лаг и максимальная стабильность 1% Low FPS):{Color.RESET}")
    print(f"   Потоки (CPU List) : {Color.CYAN}{nosmt_list_str}{Color.RESET}")
    print(f"   Hex-маска аффинити: {Color.CYAN}0x{opt.mask_nosmt:04X}{Color.RESET}  ({len(opt.threads_nosmt)} физических ядер, 1 поток на ядро)")
    print(f"   Подходит для      : Киберспортивных настроек, устранения микростаттеров и очередей SMT.")

    print(f"\n{Color.CYAN}{'='*80}{Color.RESET}")
    print(f"{Color.BOLD} ПОШАГОВАЯ ИНСТРУКЦИЯ ПО ВНЕСЕНИЮ В PROCESS LASSO:{Color.RESET}")
    print(f"{Color.CYAN}{'='*80}{Color.RESET}")
    print(f"1. Откройте {Color.BOLD}Process Lasso{Color.RESET} (желательно с правами Администратора).")
    print(f"2. Запустите игру ({Color.BOLD}cs2.exe{Color.RESET} или {Color.BOLD}dota2.exe{Color.RESET}).")
    print(f"3. В списке процессов Process Lasso найдите процесс игры и нажмите по нему {Color.BOLD}ПКМ{Color.RESET}:")
    print(f"   -> {Color.BOLD}Соответствие ЦП (CPU Affinity){Color.RESET}")
    print(f"   -> {Color.BOLD}Всегда (Always){Color.RESET}")
    print(f"   -> {Color.BOLD}Выбрать соответствие ЦП... (Select CPU Affinity...){Color.RESET}")
    print(f"4. Снимите галочки со всех потоков и отметьте:")
    print(f"   - Для варианта «С SMT»   : потоки {Color.GREEN}{smt_list_str}{Color.RESET}")
    print(f"   - Для варианта «Без SMT» : потоки {Color.CYAN}{nosmt_list_str}{Color.RESET}")
    print(f"   (Либо введите Hex-маску: {Color.GREEN}0x{opt.mask_smt:04X}{Color.RESET} / {Color.CYAN}0x{opt.mask_nosmt:04X}{Color.RESET})")
    print(f"5. Нажмите {Color.BOLD}OK{Color.RESET}. Настройка применится навсегда при каждом запуске игры.")
    print(f"{Color.CYAN}{'='*80}{Color.RESET}\n")


# ==============================================================================
# step 5: сейв отчета report.txt/.csv
# ==============================================================================
def save_reports(
    topology: CpuTopology,
    benchmarks: dict[int, BenchmarkResult] | None,
    profiles: dict[int, ThreadProfile] | None,
    opt: OptimizationResult
):
    app_dir = get_app_dir()
    txt_path = os.path.join(app_dir, "report.txt")
    csv_path = os.path.join(app_dir, "report.csv")

    with open(txt_path, "w", encoding="utf-8") as f:
        f.write("=" * 80 + "\n")
        f.write(f"ОТЧЁТ АНАЛИЗА ПРОЦЕССОРА И РЕКОМЕНДАЦИЙ ДЛЯ PROCESS LASSO\n")
        f.write(f"Процессор: {topology.cpu_name}\n")
        f.write(f"Дата создания: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write("=" * 80 + "\n\n")

        f.write("1. ТОПОЛОГИЯ ЯДЕР И КЭША L3 (CCX):\n")
        f.write(f"{'Ядро':^6} | {'Потоки':^16} | {'SMT':^8} | {'CCX (L3)':^16} | {'Тип':^16}\n")
        f.write("-" * 75 + "\n")
        for c in topology.cores:
            th_str = ", ".join(str(t) for t in c.threads)
            smt_str = "Да" if c.smt else "Нет"
            f.write(f"Core {c.core_id:^2} | {th_str:^16} | {smt_str:^8} | CCX {c.ccx_id:^12} | {c.core_type:^16}\n")
        f.write("\n")

        f.write("2. РЕЗУЛЬТАТЫ СКОРОСТИ И ФОНОВОЙ НАГРУЗКИ:\n")
        f.write(f"{'Ядро':^6} | {'Поток':^6} | {'Скорость (it/s)':^16} | {'Частота':^12} | {'Avg CPU%':^10} | {'P95 CPU%':^10} | {'Int%':^8} | {'DPC%':^8}\n")
        f.write("-" * 90 + "\n")
        for c in topology.cores:
            b = benchmarks.get(c.core_id) if benchmarks else None
            speed_str = f"{b.median_speed:,.0f}" if b else "N/A"
            freq_str = f"{b.real_freq_mhz:.0f}MHz" if b and b.real_freq_mhz > 0 else "N/A"

            for t in c.threads:
                p = profiles.get(t) if profiles else None
                avg_c = f"{p.avg_cpu:.2f}%" if p else "N/A"
                p95_c = f"{p.p95_cpu:.2f}%" if p else "N/A"
                avg_i = f"{p.avg_interrupt:.2f}%" if p else "N/A"
                avg_d = f"{p.avg_dpc:.2f}%" if p else "N/A"
                f.write(f"Core {c.core_id:^2} | {t:^6} | {speed_str:^16} | {freq_str:^12} | {avg_c:^10} | {p95_c:^10} | {avg_i:^8} | {avg_d:^8}\n")
        f.write("\n")

        f.write("3. СКОРИНГ И ВЫБОР:\n")
        f.write(f"Выбран лучший CCX: {opt.selected_ccx}\n")
        f.write(f"Выбранные физические ядра: {opt.selected_core_ids}\n\n")

        smt_str = ",".join(str(t) for t in opt.threads_smt)
        nosmt_str = ",".join(str(t) for t in opt.threads_nosmt)

        f.write(f"ВАРИАНТ «С SMT»:\n")
        f.write(f"  Потоки: {smt_str}\n")
        f.write(f"  Hex-маска: 0x{opt.mask_smt:04X}\n\n")

        f.write(f"ВАРИАНТ «БЕЗ SMT»:\n")
        f.write(f"  Потоки: {nosmt_str}\n")
        f.write(f"  Hex-маска: 0x{opt.mask_nosmt:04X}\n\n")

        f.write("4. ИНСТРУКЦИЯ ДЛЯ PROCESS LASSO:\n")
        f.write("  ПКМ по cs2.exe / dota2.exe -> CPU Affinity -> Always -> Выбрать маску ЦП...\n")
        f.write(f"  Отметить потоки {smt_str} (с SMT) или {nosmt_str} (без SMT).\n")

    with open(csv_path, "w", newline="", encoding="utf-8-sig") as f:
        writer = csv.writer(f, delimiter=";")
        writer.writerow([
            "Core_ID", "CCX_ID", "Core_Type", "Logical_Threads", "SMT",
            "Speed_IterSec", "Real_Freq_MHz",
            "Avg_CPU_Pct", "P95_CPU_Pct", "Interrupt_Pct", "DPC_Pct",
            "Norm_Speed", "Penalty_BG", "Penalty_DPC_Int", "Penalty_Core0", "Final_Score",
            "Selected_SMT", "Selected_NoSMT"
        ])

        for c in topology.cores:
            b = benchmarks.get(c.core_id) if benchmarks else None
            sc = opt.core_scores.get(c.core_id)

            speed = b.median_speed if b else 0.0
            freq = b.real_freq_mhz if b else 0.0

            if profiles:
                t_avgs = [profiles[t].avg_cpu for t in c.threads if t in profiles]
                t_p95s = [profiles[t].p95_cpu for t in c.threads if t in profiles]
                t_ints = [profiles[t].avg_interrupt for t in c.threads if t in profiles]
                t_dpcs = [profiles[t].avg_dpc for t in c.threads if t in profiles]
                avg_c = statistics.mean(t_avgs) if t_avgs else 0.0
                p95_c = max(t_p95s) if t_p95s else 0.0
                avg_i = statistics.mean(t_ints) if t_ints else 0.0
                avg_d = statistics.mean(t_dpcs) if t_dpcs else 0.0
            else:
                avg_c = p95_c = avg_i = avg_d = 0.0

            sel_smt = "1" if c.core_id in opt.selected_core_ids else "0"
            sel_nosmt = "1" if c.core_id in opt.selected_core_ids else "0"

            writer.writerow([
                c.core_id,
                c.ccx_id,
                c.core_type,
                " ".join(str(t) for t in c.threads),
                1 if c.smt else 0,
                f"{speed:.0f}",
                f"{freq:.1f}",
                f"{avg_c:.2f}",
                f"{p95_c:.2f}",
                f"{avg_i:.2f}",
                f"{avg_d:.2f}",
                f"{sc.norm_speed:.2f}" if sc else "",
                f"{sc.penalty_bg:.2f}" if sc else "",
                f"{sc.penalty_dpc_int:.2f}" if sc else "",
                f"{sc.penalty_core0:.2f}" if sc else "",
                f"{sc.final_score:.2f}" if sc else "",
                sel_smt,
                sel_nosmt
            ])

    print(f"{Color.GREEN}[✓] Полный отчёт сохранён в файлы:{Color.RESET}")
    print(f"    - {os.path.abspath(txt_path)}")
    print(f"    - {os.path.abspath(csv_path)}")


# =====================================
# step 6 main entry point
# =====================================
def main():
    print(f"{Color.HEADER}{'='*80}{Color.RESET}")
    print(f"{Color.BOLD}   CoreSniper v1.0 - Оптимизатор привязки потоков CPU для Process Lasso{Color.RESET}")
    print(f"   Специально для соревновательных игр: CS2, Dota 2, Valorant, Apex Legends")
    print(f"{Color.HEADER}{'='*80}{Color.RESET}")

    # checkking for admin rights
    admin_state = is_admin()
    if admin_state:
        print(f"Права администратора: {Color.GREEN}Обнаружены (Администратор){Color.RESET}")
    else:
        print(f"Права администратора: {Color.YELLOW}Обычный пользователь{Color.RESET}")
        print(f"{Color.DIM}[i] Для полного доступа к счетчикам ядра Windows рекомендуется запускать от имени Администратора.{Color.RESET}")

    try:
        topology = CpuTopology()
    except Exception as e:
        print(f"{Color.RED}[!] Критическая ошибка при получении топологии процессора: {e}{Color.RESET}")
        sys.exit(1)

    print(f"Процессор: {Color.BOLD}{topology.cpu_name}{Color.RESET}")
    print(f"Ядер: {len(topology.cores)} | Потоков: {topology.total_logical_processors} | CCX/L3 групп: {len(topology.l3_caches)}")

    benchmarks: dict[int, BenchmarkResult] | None = None
    profiles: dict[int, ThreadProfile] | None = None
    last_opt_result: OptimizationResult | None = None

    while True:
        print(f"\n{Color.CYAN}{'='*45}{Color.RESET}")
        print(f"{Color.BOLD}            ГЛАВНОЕ МЕНЮ{Color.RESET}")
        print(f"{Color.CYAN}{'='*45}{Color.RESET}")
        print(" 1. Топология процессора (Ядра, SMT, CCX/L3, P/E)")
        print(" 2. Тест скорости ядер (Однопоточный бенчмарк + частота)")
        print(" 3. Профиль фона (Загрузка, прерывания ISR и DPC)")
        print(" 4. Итоговая рекомендация и генерация маски для Lasso")
        print(f" {Color.GREEN}5. Всё сразу (Полный автоматический прогон 1->2->3->4){Color.RESET}")
        print(" 0. Выход")
        print(f"{Color.CYAN}{'='*45}{Color.RESET}")

        try:
            choice = input(f"{Color.BOLD}Выберите действие [0-5]: {Color.RESET}").strip()
        except (KeyboardInterrupt, EOFError):
            print("\nВыход.")
            break

        if choice == '1':
            topology.print_topology_table()

        elif choice == '2':
            try:
                raw_dur = input("Длительность прогона на ядро в секундах (Enter для 3.0): ").strip()
                dur = float(raw_dur) if raw_dur else 3.0
            except ValueError:
                dur = 3.0
            benchmarks = benchmark_all_cores(topology, duration_sec=dur, repeats=3)

        elif choice == '3':
            try:
                raw_min = input("Время сбора профиля фона в минутах (Enter для 5.0, тест: 0.2): ").strip()
                mins = float(raw_min) if raw_min else 5.0
            except ValueError:
                mins = 5.0
            profiles = profile_background(topology, duration_minutes=mins)

        elif choice == '4':
            if benchmarks is None or profiles is None:
                missing = []
                if benchmarks is None:
                    missing.append("тест скорости (пункт 2)")
                if profiles is None:
                    missing.append("профиль фона (пункт 3)")
                print(f"{Color.YELLOW}[i] Обратите внимание: {' и '.join(missing)} еще не запускались.")
                print(f"    Расчёт будет произведён на основе топологии и штрафа Ядра 0.")
                print(f"    Для максимальной точности рекомендуется также пройти шаги 2 и 3 (или выбрать пункт 5).{Color.RESET}")

            try:
                raw_k = input("Сколько физических ядер выделить для игры (K) [Enter для 4]: ").strip()
                k_val = int(raw_k) if raw_k else 4
            except ValueError:
                k_val = 4

            last_opt_result = calculate_scores_and_recommend(topology, benchmarks, profiles, k_cores=k_val)
            print_recommendation_report(topology, last_opt_result)
            save_reports(topology, benchmarks, profiles, last_opt_result)

        elif choice == '5':
            print(f"\n{Color.BOLD}>>> ЗАПУСК ПОЛНОГО АВТОМАТИЧЕСКОГО ЦИКЛА <<<{Color.RESET}")

            topology.print_topology_table()

            benchmarks = benchmark_all_cores(topology, duration_sec=3.0, repeats=3)

            try:
                raw_min = input("\nВремя мониторинга фона в минутах [Enter для 5.0, для быстрого теста введите 0.2]: ").strip()
                mins = float(raw_min) if raw_min else 5.0
            except ValueError:
                mins = 5.0
            profiles = profile_background(topology, duration_minutes=mins)

            try:
                raw_k = input("Сколько физических ядер выделить для игры [Enter для 4]: ").strip()
                k_val = int(raw_k) if raw_k else 4
            except ValueError:
                k_val = 4

            last_opt_result = calculate_scores_and_recommend(topology, benchmarks, profiles, k_cores=k_val)
            print_recommendation_report(topology, last_opt_result)
            save_reports(topology, benchmarks, profiles, last_opt_result)

        elif choice == '0':
            print("Завершение работы программы.")
            break
        else:
            print(f"{Color.YELLOW}Неверный ввод. Введите число от 0 до 5.{Color.RESET}")


if __name__ == '__main__':
    main()
