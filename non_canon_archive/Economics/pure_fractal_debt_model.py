"""
Pure Python Fractal Debt Model (Zero External Dependencies)
============================================================
Runs directly on standard Python.
Implements:
  1. Hierarchical Credit Network (Tier 0 Agents -> Tier 1 Banks -> Tier 2 Sovereign)
  2. Loss Socialization / Residue Debt Accumulation
  3. Pure Python Discrete Fourier Transform (DFT) Spectral Analyzer
  4. ASCII Time-Series & Power Spectrum Visualizer
"""

import math
import random

class PureHierarchicalCreditSystem:
    def __init__(self, n_agents=120, n_banks=12, timesteps=3000, dt=0.1, seed=42):
        random.seed(seed)
        self.timesteps = timesteps
        self.dt = dt
        self.n_agents = n_agents
        self.n_banks = n_banks
        
        # Agent to Bank mapping
        self.agent_bank_map = [random.randint(0, n_banks - 1) for _ in range(n_agents)]
        
        # Tier 0: Agents (Households & Firms)
        self.agent_incomes = [random.uniform(80, 120) for _ in range(n_agents)]
        self.agent_debts = [random.uniform(20, 50) for _ in range(n_agents)]
        
        # Tier 1: Commercial Banks
        self.bank_capital = [100.0 for _ in range(n_banks)]
        self.bank_bad_debt_buffer = [0.0 for _ in range(n_banks)]
        
        # Tier 2: Sovereign / Central Bank
        self.sovereign_debt = 500.0
        self.base_rate = 0.05
        
        # Logs
        self.history_time = []
        self.history_tier0_debt = []
        self.history_tier2_debt = []
        self.history_defaults = []
        self.history_base_rate = []

    def step(self, t):
        effective_rate = max(0.005, self.base_rate)
        
        # 1. Tier 0 Dynamics (Micro borrowing & income)
        n_defaults = 0
        defaulted_indices = []
        
        for i in range(self.n_agents):
            # Productivity drift + stochastic shock
            shock = random.gauss(1.0, 0.07)
            self.agent_incomes[i] = max(10.0, min(600.0, self.agent_incomes[i] * (1.0 + 0.015 * self.dt) * shock))
            
            # Borrow impulse: High when base rate is low
            borrow = max(0.0, random.gauss(2.5, 1.0)) * (1.0 / (1.0 + 8.0 * effective_rate))
            self.agent_debts[i] += borrow * self.dt
            
            # Debt service cost (interest + principal amortization)
            service = self.agent_debts[i] * (effective_rate + 0.05) * self.dt
            capacity = 0.40 * self.agent_incomes[i] * self.dt
            
            if service > capacity:
                n_defaults += 1
                defaulted_indices.append(i)

        # 2. Residue Rule: Upward Debt Absorption
        for idx in defaulted_indices:
            debt = self.agent_debts[idx]
            absorbed = 0.70 * debt  # 70% absorbed by bank as toxic asset / bad debt
            self.agent_debts[idx] -= debt * 0.75  # borrower is partially written off
            
            b_idx = self.agent_bank_map[idx]
            self.bank_bad_debt_buffer[b_idx] += absorbed
            self.bank_capital[b_idx] -= absorbed * 0.5

        # 3. Tier 1: Bank Solvency & Sovereign Bailouts
        bank_failures = 0
        for b_idx in range(self.n_banks):
            if self.bank_capital[b_idx] < 20.0 or self.bank_bad_debt_buffer[b_idx] > 80.0:
                bank_failures += 1
                bailout = self.bank_bad_debt_buffer[b_idx] + (50.0 - self.bank_capital[b_idx])
                
                # Sovereign absorbs residue debt to prevent systemic freeze
                self.sovereign_debt += bailout
                self.bank_capital[b_idx] = 60.0
                self.bank_bad_debt_buffer[b_idx] = 0.0
                # Central bank rate cut
                self.base_rate = max(0.005, self.base_rate - 0.015)
            else:
                self.bank_capital[b_idx] += 1.0 * self.dt

        # 4. Tier 2: Sovereign Dynamics & Hegemonic Reset
        self.sovereign_debt += self.sovereign_debt * effective_rate * self.dt
        
        # Rate hike in quiet times (setting up the next short cycle)
        if n_defaults < (0.05 * self.n_agents) and bank_failures == 0:
            self.base_rate = min(0.08, self.base_rate + 0.002 * self.dt)
            
        # Sovereign Macro Reset (When debt capacity is exhausted)
        if self.sovereign_debt > 5000.0:
            self.sovereign_debt *= 0.35  # Debt monetization / currency debasement
            self.base_rate = 0.06
            for i in range(self.n_agents):
                self.agent_debts[i] *= 0.50
                self.agent_incomes[i] *= 0.80

        # Log metrics
        current_time = t * self.dt
        self.history_time.append(current_time)
        self.history_tier0_debt.append(sum(self.agent_debts))
        self.history_tier2_debt.append(self.sovereign_debt)
        self.history_defaults.append(n_defaults)
        self.history_base_rate.append(self.base_rate * 100)

    def run(self):
        for t in range(self.timesteps):
            self.step(t)
        return self

def compute_dft_spectrum(signal, dt=0.1, max_period=100.0, min_period=2.0, num_bins=80):
    """Computes Fourier power spectral density across period bins."""
    N = len(signal)
    mean_val = sum(signal) / N
    detrended = [x - mean_val for x in signal]
    
    # Generate logarithmically spaced test periods
    log_min = math.log10(min_period)
    log_max = math.log10(max_period)
    periods = [10 ** (log_min + i * (log_max - log_min) / (num_bins - 1)) for i in range(num_bins)]
    
    powers = []
    for T in periods:
        omega = 2.0 * math.pi / T
        real_sum = sum(detrended[n] * math.cos(omega * (n * dt)) for n in range(N))
        imag_sum = sum(detrended[n] * math.sin(omega * (n * dt)) for n in range(N))
        power = (real_sum**2 + imag_sum**2) / N
        powers.append(power)
        
    return periods, powers

def print_ascii_chart(title, x_data, y_data, width=65, height=10, x_label="Years", y_label=""):
    print(f"\n{'='*70}")
    print(f" {title}")
    print(f"{'='*70}")
    min_y = min(y_data)
    max_y = max(y_data)
    if max_y == min_y:
        max_y += 1.0
        
    step_x = len(y_data) / width
    sampled = [y_data[min(len(y_data)-1, int(i * step_x))] for i in range(width)]
    
    grid = [[" " for _ in range(width)] for _ in range(height)]
    
    for x in range(width):
        val = sampled[x]
        y_pos = int((val - min_y) / (max_y - min_y) * (height - 1))
        y_pos = min(height - 1, max(0, y_pos))
        grid[height - 1 - y_pos][x] = "█"
        
    for r in range(height):
        y_val = max_y - (r / (height - 1)) * (max_y - min_y)
        row_str = "".join(grid[r])
        print(f"{y_val:8.1f} |{row_str}|")
    print(f"         0{' ' * (width - 12)}{x_data[-1]:.0f} {x_label}")

if __name__ == "__main__":
    print("="*70)
    print(" HIERARCHICAL FRACTAL DEBT SIMULATION (PURE PYTHON ENGINE)")
    print("="*70)
    sim = PureHierarchicalCreditSystem(timesteps=3000, dt=0.1, seed=42)
    sim.run()
    
    total_years = sim.history_time[-1]
    
    # 1. Fourier Spectral Analysis on Default Waves
    periods, powers = compute_dft_spectrum(sim.history_defaults, dt=0.1, min_period=2.0, max_period=120.0, num_bins=60)
    
    # Find spectral power peaks
    sorted_peaks = sorted(zip(periods, powers), key=lambda x: x[1], reverse=True)
    
    print(f"\n[+] Total Simulated Duration: {total_years:.1f} Earth Years")
    print(f"[+] Total Micro-Agents: {sim.n_agents} | Banks: {sim.n_banks} | Sovereign: 1")
    print("\n--- DOMINANT SPECTRAL HARMONICS (Emergent without hardcoding) ---")
    for rank, (period, power) in enumerate(sorted_peaks[:4], 1):
        print(f"  Peak #{rank}: Harmonic Resonant Cycle = {period:6.2f} Years | Spectral Density = {power:9.1f}")
    
    # 2. Render ASCII Visualizers
    print_ascii_chart("LAYER 1: TIER 0 PRIVATE SECTOR DEBT (Short-Cycle Oscillations)", 
                      sim.history_time, sim.history_tier0_debt, width=62, height=8, x_label="Years")
                      
    print_ascii_chart("LAYER 2: TIER 2 SOVEREIGN RESIDUE DEBT (Secular Debt Super-Cycles)", 
                      sim.history_time, sim.history_tier2_debt, width=62, height=8, x_label="Years")
                      
    print_ascii_chart("LAYER 3: CENTRAL BANK BASE RATE (% REACTING TO CRISES)", 
                      sim.history_time, sim.history_base_rate, width=62, height=7, x_label="Years")

    # Render Power Spectrum (Log Scale)
    log_powers = [math.log10(max(1e-3, p)) for p in powers]
    print_ascii_chart("FOURIER POWER SPECTRUM (Log Spectral Power vs Cycle Period in Years)", 
                      periods, log_powers, width=62, height=8, x_label="Period (Yrs)")
