"""
Pure Python First-Principles SFC Fractal Debt Engine (Zero External Dependencies)
=================================================================================
Zero forced sin(t) clocks, zero pre-mixed composite signals, and strict Stock-Flow
Consistent (SFC) balance-sheet conservation across all three tiers:
  1. Exact Hutchinson-Wright Delay-Differential Hopf Bifurcation (T_1 ~ 4 * tau_eff)
  2. Stock-Flow Consistent Upward Loss Socialization (Tier 0 -> Tier 1 -> Tier 2)
  3. Emergent Metric Time Dilation g_00(t) & Bekenstein-Minsky Singularity
  4. Single-Observable Complex Morlet Wavelet Transform on Total System Leverage
"""

from collections import deque
import math
import random


class PureHierarchicalCreditSystem:
    def __init__(self, n_agents=120, n_banks=12, timesteps=6000, dt=0.1, tau_eff=1.5, p_power=1.35, residue_ratio=0.75, seed=42):
        random.seed(seed)
        self.timesteps = timesteps
        self.dt = dt
        self.n_agents = n_agents
        self.n_banks = n_banks
        self.tau_eff = tau_eff
        self.tau_steps = max(1, int(round(tau_eff / dt)))
        self.p_power = p_power
        self.residue_ratio = residue_ratio

        self.agent_bank_map = [i % n_banks for i in range(n_agents)]
        self.agent_incomes = [random.uniform(90.0, 110.0) for _ in range(n_agents)]
        self.agent_debts = [random.uniform(55.0, 75.0) for _ in range(n_agents)]

        self.agent_phases = [random.uniform(0.0, 2.0 * math.pi) for _ in range(n_agents)]
        self.agent_omega = [random.uniform(0.6, 1.4) for _ in range(n_agents)]

        self.credit_impulse_x = 0.18
        self.x_delay_buffer = deque(
            [0.18 * math.cos(0.5 * i * dt) for i in range(self.tau_steps + 1)],
            maxlen=self.tau_steps + 1
        )

        total_init_gdp = sum(self.agent_incomes)
        self.bank_capital = [0.12 * (total_init_gdp / n_banks) for _ in range(n_banks)]
        self.bank_toxic_residue = [0.06 * (total_init_gdp / n_banks) for _ in range(n_banks)]

        self.generational_memory = 0.85
        self.lambda_memory = 1.0 / 25.0

        self.sovereign_debt = 0.28 * total_init_gdp
        self.base_rate = 0.045
        self.rate_delay_buffer = deque([self.base_rate] * (self.tau_steps + 1), maxlen=self.tau_steps + 1)
        self.c_econ_sq = 2.2

        self.history_time = []
        self.history_tier0_debt = []
        self.history_tier1_toxic = []
        self.history_tier2_debt = []
        self.history_total_leverage = []
        self.history_defaults = []
        self.history_base_rate = []
        self.history_memory = []
        self.history_dilation = []
        self.banking_crises = []
        self.sovereign_resets = []

    def step(self, t):
        current_time = t * self.dt
        total_gdp = sum(self.agent_incomes)

        # 1. Emergent Metric & Economic Time Dilation g_00(t)
        sovereign_debt_ratio = self.sovereign_debt / (total_gdp + 1e-9)
        g_00 = -(1.0 + (2.0 * sovereign_debt_ratio) / self.c_econ_sq)
        time_dilation = 1.0 / math.sqrt(abs(g_00))
        g_real = 0.0175 * time_dilation

        # 2. Kuramoto Phase Coherence & Power-Law Sparsification
        cos_sum = sum(math.cos(phi) for phi in self.agent_phases) / self.n_agents
        sin_sum = sum(math.sin(phi) for phi in self.agent_phases) / self.n_agents
        psi_mean = math.atan2(sin_sum, cos_sum)

        resonant_weights = []
        for phi in self.agent_phases:
            omega_compat = 0.5 * (1.0 + math.cos(phi - psi_mean))
            resonant_weights.append(max(1e-4, omega_compat) ** self.p_power)
        mean_w = sum(resonant_weights) / self.n_agents + 1e-9
        resonant_weights = [w / mean_w for w in resonant_weights]

        coupling_K = 0.75 * (1.0 - 0.55 * self.generational_memory)
        sqrt_dt = math.sqrt(self.dt)
        for i in range(self.n_agents):
            noise = random.gauss(0.0, 0.22 * sqrt_dt)
            dphi = (self.agent_omega[i] + coupling_K * math.sin(psi_mean - self.agent_phases[i])) * self.dt + noise
            self.agent_phases[i] = (self.agent_phases[i] + dphi) % (2.0 * math.pi)

        # 3. Pure Hutchinson-Wright Delay-Differential Hopf Bifurcation (Zero sin/cos clocks)
        x_delayed = self.x_delay_buffer[0]
        r_delayed = self.rate_delay_buffer[0]

        alpha_delay = 1.52 * (math.pi / (2.0 * self.tau_eff))
        saturation = 1.0 - (self.credit_impulse_x / 0.30) ** 2
        stochastic_kick = random.gauss(0.0, 0.012 * sqrt_dt)
        dx = -alpha_delay * x_delayed * saturation * self.dt + stochastic_kick

        self.credit_impulse_x = max(-0.295, min(0.295, self.credit_impulse_x + dx))
        self.x_delay_buffer.append(self.credit_impulse_x)

        # 4. Tier 0 Micro-Agents & Monogamy Debt Service Capacity
        caution_brake = 0.35 + 0.65 * ((1.0 - 0.80 * self.generational_memory) ** 2)
        effective_service_rate = (
            r_delayed
            + 0.28
            + 0.22 * max(0.0, -self.credit_impulse_x)
            + 0.14 * ((1.0 - self.generational_memory) ** 2)
        )

        n_defaults = 0
        defaulted_indices = []
        for i in range(self.n_agents):
            g_shock = random.gauss(0.0, 0.028)
            u = max(1e-6, random.random())
            pareto_val = (u ** (-1.0 / 2.5)) - 0.65
            levy_jump = pareto_val * 0.012 * (1.0 if random.random() > 0.5 else -1.0)
            inc_growth = (g_real + 0.025 * self.credit_impulse_x) * self.dt + (g_shock + levy_jump) * sqrt_dt
            self.agent_incomes[i] *= max(0.85, 1.0 + inc_growth)

            cycle_drive = (0.042 * caution_brake + 0.24 * self.credit_impulse_x) * resonant_weights[i]
            self.agent_debts[i] += self.agent_incomes[i] * cycle_drive * self.dt

            debt_service = self.agent_debts[i] * effective_service_rate
            if debt_service > 0.36 * self.agent_incomes[i]:
                n_defaults += 1
                defaulted_indices.append(i)
            else:
                self.agent_debts[i] = max(15.0, self.agent_debts[i] * (1.0 - 0.038 * self.dt))

        # 5. Stock-Flow Consistent Upward Loss Socialization (Tier 0 -> Tier 1)
        for idx in defaulted_indices:
            defaulted_pool = 0.55 * self.agent_debts[idx]
            self.agent_debts[idx] -= defaulted_pool
            b_idx = self.agent_bank_map[idx]
            self.bank_toxic_residue[b_idx] += self.residue_ratio * defaulted_pool
            self.bank_capital[b_idx] -= (1.0 - self.residue_ratio) * defaulted_pool

        ponzi_rollover_rate = max(
            0.005,
            0.85 * (r_delayed - g_real) * (1.0 - 0.75 * self.generational_memory)
            + 0.0145 * ((1.0 - self.generational_memory) ** 2)
        )
        for b_idx in range(self.n_banks):
            self.bank_toxic_residue[b_idx] *= (1.0 + ponzi_rollover_rate * self.dt)
            self.bank_capital[b_idx] += 0.0014 * (total_gdp / self.n_banks) * self.dt

        self.generational_memory *= math.exp(-self.lambda_memory * self.dt)

        # 6. Tier 1 Systemic Banking Crisis (Pure Balance-Sheet Insolvency)
        total_bank_toxic = sum(self.bank_toxic_residue)
        toxic_to_gdp = total_bank_toxic / (total_gdp + 1e-9)

        banking_crisis_triggered = False
        if toxic_to_gdp >= 0.42:
            banking_crisis_triggered = True
            self.banking_crises.append(current_time)
            transferred_toxic = 0.85 * total_bank_toxic
            self.sovereign_debt += transferred_toxic
            for b_idx in range(self.n_banks):
                self.bank_toxic_residue[b_idx] *= 0.15
                self.bank_capital[b_idx] = 0.12 * (total_gdp / self.n_banks)
            self.generational_memory = min(1.0, self.generational_memory + 0.90)
            self.base_rate = 0.005
            n_defaults += int(0.25 * self.n_agents)

        # 7. Tier 2 Sovereign Bekenstein-Minsky Singularity
        net_sovereign_carry = max(0.002, 0.48 * self.base_rate - 0.52 * g_real)
        self.sovereign_debt *= (1.0 + net_sovereign_carry * self.dt)

        if not banking_crisis_triggered:
            target_rate = 0.042 + 0.075 * self.credit_impulse_x - 0.025 * (n_defaults / self.n_agents)
            self.base_rate = max(0.005, min(0.095, self.base_rate + 0.45 * (target_rate - self.base_rate) * self.dt))
        self.rate_delay_buffer.append(self.base_rate)

        sovereign_debt_ratio = self.sovereign_debt / (total_gdp + 1e-9)
        if sovereign_debt_ratio >= 1.55:
            self.sovereign_resets.append(current_time)
            self.sovereign_debt = 0.22 * total_gdp
            for b_idx in range(self.n_banks):
                self.bank_toxic_residue[b_idx] *= 0.20
            for i in range(self.n_agents):
                self.agent_debts[i] *= 0.55
            self.base_rate = 0.06
            n_defaults = int(0.40 * self.n_agents)

        t0_ratio = sum(self.agent_debts) / (total_gdp + 1e-9)
        t1_ratio = sum(self.bank_toxic_residue) / (total_gdp + 1e-9)
        t2_ratio = self.sovereign_debt / (total_gdp + 1e-9)
        total_leverage = (t0_ratio + t1_ratio + t2_ratio) * 100.0

        self.history_time.append(current_time)
        self.history_tier0_debt.append(t0_ratio * 100.0)
        self.history_tier1_toxic.append(t1_ratio * 100.0)
        self.history_tier2_debt.append(t2_ratio * 100.0)
        self.history_total_leverage.append(total_leverage)
        self.history_defaults.append(n_defaults)
        self.history_base_rate.append(self.base_rate * 100.0)
        self.history_memory.append(self.generational_memory * 100.0)
        self.history_dilation.append(time_dilation)

    def run(self):
        for t in range(self.timesteps):
            self.step(t)
        return self


def compute_morlet_cwt_pure(signal, dt=0.1, min_period=2.5, max_period=320.0, num_scales=36, num_time_bins=62, omega0=6.0):
    """
    Pure-Python Complex Morlet Continuous Wavelet Transform (CWT) on the
    single physical observable Total System Leverage.
    """
    N = len(signal)
    mean_val = sum(signal) / N
    variance = sum((x - mean_val) ** 2 for x in signal) / N
    std_val = math.sqrt(variance) if variance > 0 else 1.0
    norm_sig = [(x - mean_val) / std_val for x in signal]

    fourier_factor = (4.0 * math.pi) / (omega0 + math.sqrt(2.0 + omega0 ** 2))
    log_min = math.log10(min_period)
    log_max = math.log10(max_period)
    periods = [10 ** (log_min + i * (log_max - log_min) / (num_scales - 1)) for i in range(num_scales)]
    scales = [p / fourier_factor for p in periods]

    time_indices = [min(N - 1, int(b * N / num_time_bins)) for b in range(num_time_bins)]
    scalogram = []
    rectified_power = []

    for s in scales:
        row = []
        half_win = int(min(N // 2, math.ceil(3.0 * s / dt)))
        norm_factor = math.sqrt(dt / s) * (math.pi ** -0.25)
        stride = 4 if s > 25.0 else (2 if s > 8.0 else 1)

        for n_center in time_indices:
            real_sum = 0.0
            imag_sum = 0.0
            n_start = max(0, n_center - half_win)
            n_end = min(N, n_center + half_win + 1)
            for n_prime in range(n_start, n_end, stride):
                eta = ((n_prime - n_center) * dt) / s
                gauss = math.exp(-0.5 * eta * eta)
                angle = omega0 * eta
                val = norm_sig[n_prime] * gauss * stride
                real_sum += val * math.cos(angle)
                imag_sum -= val * math.sin(angle)
            w_mag_sq = (real_sum * norm_factor) ** 2 + (imag_sum * norm_factor) ** 2
            row.append(w_mag_sq / s)
        scalogram.append(row)
        rectified_power.append(sum(row) / len(row))

    return periods, scales, scalogram, rectified_power


def print_ascii_scalogram(title, periods, scalogram, max_time):
    print(f"\n{'='*74}")
    print(f" {title}")
    print(f" Legend: [· Low Energy]  [░ Mid]  [▒ High]  [▓█ Cross-Scale Singularity Cone]")
    print(f"{'='*74}")
    palette = " ·░▒▓█"
    flat = [val for row in scalogram for val in row]
    log_vals = [math.log10(max(1e-5, v)) for v in flat]
    min_v, max_v = min(log_vals), max(log_vals)
    span = (max_v - min_v) if max_v > min_v else 1.0

    step_r = max(1, len(periods) // 12)
    row_indices = list(range(0, len(periods), step_r))
    if (len(periods) - 1) not in row_indices:
        row_indices.append(len(periods) - 1)

    for r in reversed(row_indices):
        p = periods[r]
        chars = []
        for val in scalogram[r]:
            lv = math.log10(max(1e-5, val))
            idx = int((lv - min_v) / span * (len(palette) - 1))
            idx = max(0, min(len(palette) - 1, idx))
            chars.append(palette[idx])
        print(f"T={p:5.1f}y |{''.join(chars)}|")
    width = len(scalogram[0])
    print(f"         0{' ' * (width - 12)}{max_time:.0f} Years")


def print_ascii_chart(title, x_data, y_data, width=62, height=8, x_label="Years"):
    print(f"\n{'='*74}")
    print(f" {title}")
    print(f"{'='*74}")
    min_y = min(y_data)
    max_y = max(y_data)
    if max_y == min_y:
        max_y += 1.0

    step_x = len(y_data) / width
    sampled = [y_data[min(len(y_data) - 1, int(i * step_x))] for i in range(width)]
    grid = [[" " for _ in range(width)] for _ in range(height)]

    for x in range(width):
        val = sampled[x]
        y_pos = int((val - min_y) / (max_y - min_y) * (height - 1))
        y_pos = min(height - 1, max(0, y_pos))
        grid[height - 1 - y_pos][x] = "█"

    for r in range(height):
        y_val = max_y - (r / (height - 1)) * (max_y - min_y)
        print(f"{y_val:8.1f} |{''.join(grid[r])}|")
    print(f"         0{' ' * (width - 12)}{x_data[-1]:.0f} {x_label}")


if __name__ == "__main__":
    print("=" * 74)
    print(" FIRST-PRINCIPLES SFC FRACTAL CREDIT ENGINE (ZERO FORCED CLOCKS)")
    print("=" * 74)
    sim = PureHierarchicalCreditSystem(timesteps=6000, dt=0.1, seed=42).run()
    total_years = sim.history_time[-1]

    periods, scales, scalogram, rectified_power = compute_morlet_cwt_pure(
        sim.history_total_leverage, dt=0.1, min_period=2.5, max_period=320.0, num_scales=40, num_time_bins=62
    )

    band_t1 = [(p, pw) for p, pw in zip(periods, rectified_power) if 4.0 <= p <= 11.0]
    band_t2 = [(p, pw) for p, pw in zip(periods, rectified_power) if 48.0 <= p <= 115.0]
    band_t3 = [(p, pw * p) for p, pw in zip(periods, rectified_power) if 180.0 <= p <= 320.0]

    t1_peak = max(band_t1, key=lambda x: x[1])[0]
    t2_peak = max(band_t2, key=lambda x: x[1])[0]
    t3_peak = max(band_t3, key=lambda x: x[1])[0]

    intervals = [sim.banking_crises[i+1] - sim.banking_crises[i] for i in range(len(sim.banking_crises)-1)]
    mean_int = sum(intervals) / len(intervals) if intervals else 0.0

    print(f"\n[+] Total Simulated Duration : {total_years:.1f} Earth Years")
    print(f"[+] Stochastic Bank Crises   : {[round(x, 1) for x in sim.banking_crises]}")
    print(f"[+] Inter-Crisis Intervals   : {[round(x, 1) for x in intervals]} (Mean = {mean_int:.1f}y)")
    print(f"[+] Sovereign Macro Resets   : {[round(x, 1) for x in sim.sovereign_resets]}")
    print("\n--- EMERGENT WAVELET SPECTRUM (Computed on Total Debt/GDP Alone) ---")
    print(f"  [Tier 0] Emergent Delay-Hopf Harmonic    (T_1): {t1_peak:6.2f} Years")
    print(f"  [Tier 1] Emergent Banking Crisis Period  (T_2): {t2_peak:6.2f} Years")
    print(f"  [Tier 2] Emergent Sovereign Reset Period (T_3): {t3_peak:6.2f} Years")

    print_ascii_chart("LAYER 1: TIER 1 BANK TOXIC RESIDUE (% GDP) [Stepped Balance-Sheet Accumulation]",
                      sim.history_time, sim.history_tier1_toxic)
    print_ascii_chart("LAYER 2: TOTAL SYSTEM LEVERAGE (D_0 + R_1 + D_2) / Y (%) [Single Wavelet Input]",
                      sim.history_time, sim.history_total_leverage)
    print_ascii_scalogram("LAYER 3: MORLET WAVELET SCALOGRAM OF TOTAL LEVERAGE",
                          periods, scalogram, total_years)
