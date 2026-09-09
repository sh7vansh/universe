"""
Fractal Debt Cycles Simulation
==============================
This simulation implements an agnostic, hierarchical credit-sandpile model.
It does NOT hardcode 7, 75, or 250 years. Instead, it defines agnostic local rules
for borrowing, debt servicing, and upward residue-debt absorption across a 3-tier hierarchy:

  - Tier 0: Micro-Agents (Firms & Households) -> High frequency adjustments
  - Tier 1: Commercial Banks (Intermediaries)  -> Medium frequency aggregation & bailouts
  - Tier 2: Sovereign / Central Bank           -> Low frequency debt monetization & resets

Mathematical Properties:
  - Self-Organized Criticality (SOC)
  - Scale Invariance & Power-Law Avalanche Distribution
  - Residue-Debt Upward Transfer (Loss Socialization)
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.signal import welch

class HierarchicalCreditSystem:
    def __init__(self, 
                 n_agents=100, 
                 n_banks=10, 
                 timesteps=3000, 
                 dt=0.1,  # 1 step = 0.1 years (approx 1.2 months)
                 seed=42):
        np.random.seed(seed)
        self.timesteps = timesteps
        self.dt = dt
        self.n_agents = n_agents
        self.n_banks = n_banks
        
        # Agent to bank mapping
        self.agent_bank_map = np.random.randint(0, n_banks, size=n_agents)
        
        # Initial states
        # Tier 0: Micro-Agents
        self.agent_incomes = np.random.uniform(80, 120, size=n_agents)
        self.agent_debts = np.random.uniform(20, 50, size=n_agents)
        self.agent_productivity = np.random.uniform(0.9, 1.1, size=n_agents)
        
        # Tier 1: Banks
        self.bank_capital = np.full(n_banks, 100.0)
        self.bank_bad_debt_buffer = np.zeros(n_banks)
        
        # Tier 2: Sovereign / Central Bank
        self.sovereign_debt = 500.0
        self.base_rate = 0.05
        self.money_supply = 2000.0
        
        # Metric logs
        self.history = {
            'time': [],
            'tier0_total_debt': [],
            'tier0_defaults': [],
            'tier1_total_debt_absorbed': [],
            'tier1_bank_failures': [],
            'tier2_sovereign_debt': [],
            'systemic_stress': [],
            'base_rate': []
        }
        
    def step(self, t):
        # 1. Macro environment / Base Rate influence
        effective_rate = max(0.005, self.base_rate)
        
        # 2. Tier 0: Agents produce income, pay debt, and borrow more
        # Shocks: productivity drift + stochastic noise
        shocks = np.random.normal(1.0, 0.08, size=self.n_agents)
        self.agent_incomes = self.agent_incomes * (1 + 0.015 * self.dt) * shocks
        self.agent_incomes = np.clip(self.agent_incomes, 10.0, 500.0)
        
        # Growth impulse: Agents borrow to leverage positive returns
        borrow_impulse = np.maximum(0, np.random.normal(2.0, 1.0, size=self.n_agents)) * (1.0 / (1.0 + 10.0 * effective_rate))
        self.agent_debts += borrow_impulse * self.dt
        
        # Debt service costs
        debt_service = self.agent_debts * (effective_rate + 0.04) * self.dt
        
        # Capacity check: Can agents service debt?
        # Threshold: Debt service exceeds 40% of income
        agent_capacity = 0.40 * self.agent_incomes * self.dt
        distressed_agents = debt_service > agent_capacity
        n_defaults = np.sum(distressed_agents)
        
        # 3. Residue Rule: Default & Upward Debt Absorption
        if n_defaults > 0:
            defaulted_debt = self.agent_debts[distressed_agents]
            # 30% written off (pure destruction / liquidation)
            # 70% absorbed by their respective banks (residue debt)
            write_off = 0.30 * defaulted_debt
            absorbed_by_banks = 0.70 * defaulted_debt
            
            # Reset distressed agents (partial haircut)
            self.agent_debts[distressed_agents] -= defaulted_debt * 0.75
            
            # Transfer residue to Tier 1 Banks
            for b_idx in range(self.n_banks):
                mask = (self.agent_bank_map[distressed_agents] == b_idx)
                if np.any(mask):
                    self.bank_bad_debt_buffer[b_idx] += np.sum(absorbed_by_banks[mask])
                    self.bank_capital[b_idx] -= np.sum(absorbed_by_banks[mask]) * 0.5
        
        # 4. Tier 1: Bank Solvency & Sovereign Bailout
        bank_failures = 0
        for b_idx in range(self.n_banks):
            # If bank capital drops below threshold, sovereign bails it out (absorbs residue)
            if self.bank_capital[b_idx] < 20.0 or self.bank_bad_debt_buffer[b_idx] > 80.0:
                bank_failures += 1
                bailout_amount = self.bank_bad_debt_buffer[b_idx] + (50.0 - self.bank_capital[b_idx])
                
                # Sovereign absorbs the debt (Tier 2 transfer)
                self.sovereign_debt += bailout_amount
                
                # Bank recapitalization
                self.bank_capital[b_idx] = 60.0
                self.bank_bad_debt_buffer[b_idx] = 0.0
                
                # Central bank responds by cutting rates to ease liquidity
                self.base_rate = max(0.005, self.base_rate - 0.015)
            else:
                # Slowly rebuild capital in good times
                self.bank_capital[b_idx] += 1.0 * self.dt
        
        # 5. Tier 2: Sovereign Dynamics & Secular Reset
        # Sovereign debt compounds at interest rate
        self.sovereign_debt += self.sovereign_debt * effective_rate * self.dt
        
        # If systemic defaults are low, Central Bank slowly hikes rates (causing next short cycle)
        if n_defaults < (0.05 * self.n_agents) and bank_failures == 0:
            self.base_rate = min(0.09, self.base_rate + 0.002 * self.dt)
            
        # Sovereign Critical Threshold (Hegemonic Reset / Currency Debasement)
        # When sovereign debt hits extreme saturation, a macro currency reset occurs
        if self.sovereign_debt > 4500.0:
            # Phase transition: Hyper-monetization / Currency reset
            # 65% of sovereign debt is debased / liquidated
            self.sovereign_debt *= 0.35
            self.base_rate = 0.06
            # Spillover inflation shock to agents
            self.agent_debts *= 0.50
            self.agent_incomes *= 0.80
            
        # Log history
        current_time = t * self.dt
        self.history['time'].append(current_time)
        self.history['tier0_total_debt'].append(np.sum(self.agent_debts))
        self.history['tier0_defaults'].append(n_defaults)
        self.history['tier1_total_debt_absorbed'].append(np.sum(self.bank_bad_debt_buffer))
        self.history['tier1_bank_failures'].append(bank_failures)
        self.history['tier2_sovereign_debt'].append(self.sovereign_debt)
        self.history['base_rate'].append(self.base_rate * 100)

    def run(self):
        print(f"Running simulation for {self.timesteps} steps ({self.timesteps * self.dt:.1f} simulated years)...")
        for t in range(self.timesteps):
            self.step(t)
        print("Simulation complete. Analyzing emergent spectral harmonics...")
        return self.history

def analyze_and_plot(history, dt=0.1, filename="fractal_debt_cycles.png"):
    time = np.array(history['time'])
    tier0_debt = np.array(history['tier0_total_debt'])
    tier2_debt = np.array(history['tier2_sovereign_debt'])
    defaults = np.array(history['tier0_defaults'])
    base_rate = np.array(history['base_rate'])
    
    # 1. Spectral Analysis (FFT / Welch Periodogram) on Default Cascades
    detrended_defaults = defaults - np.mean(defaults)
    sampling_freq = 1.0 / dt  # samples per year
    freqs, psd = welch(detrended_defaults, fs=sampling_freq, nperseg=min(len(defaults), 1024))
    
    # Filter out zero frequency
    valid = freqs > 0
    freqs = freqs[valid]
    psd = psd[valid]
    periods = 1.0 / freqs  # Period in years
    
    # Sort by dominant powers
    top_indices = np.argsort(psd)[::-1][:5]
    print("\n" + "="*60)
    print("EMERGENT SPECTRAL HARMONICS (Extracted via Fourier Power Spectrum)")
    print("="*60)
    for i, idx in enumerate(top_indices, 1):
        print(f" Harmonic #{i}: Peak Period = {periods[idx]:.2f} years | Spectral Power Density = {psd[idx]:.3e}")
    print("="*60 + "\n")
    
    # 2. Plotting Dashboard
    fig, axes = plt.subplots(4, 1, figsize=(14, 12), sharex=False)
    
    # Plot 1: Tier 0 Micro-Debt & Rate Cycles (Short Waves)
    ax1 = axes[0]
    ax1.plot(time, tier0_debt, color='#2563eb', label='Tier 0 (Private Sector Debt)', lw=1.2)
    ax1.set_ylabel('Private Debt', color='#2563eb', fontweight='bold')
    ax1.set_title('Hierarchical Fractal Debt Model: Emergent Multi-Scale Cycles (Agnostic Rules)', fontsize=13, fontweight='bold', pad=10)
    ax1.grid(True, alpha=0.3)
    
    ax1_twin = ax1.twinx()
    ax1_twin.plot(time, base_rate, color='#dc2626', linestyle='--', alpha=0.7, label='Central Bank Base Rate (%)', lw=1.0)
    ax1_twin.set_ylabel('Base Rate (%)', color='#dc2626', fontweight='bold')
    
    # Plot 2: Tier 1 & 2 Residue Debt Accumulation (Medium & Secular Waves)
    ax2 = axes[1]
    ax2.plot(time, tier2_debt, color='#7c3aed', label='Tier 2: Sovereign Debt (Absorbed Residue Ledger)', lw=1.8)
    ax2.set_ylabel('Sovereign Debt', color='#7c3aed', fontweight='bold')
    ax2.grid(True, alpha=0.3)
    ax2.legend(loc='upper left')
    
    # Plot 3: Avalanche / Default Cascades across Time
    ax3 = axes[2]
    ax3.bar(time, defaults, width=dt*0.8, color='#ea580c', alpha=0.7, label='Defaults / Liquidation Avalanches')
    ax3.set_ylabel('Defaults / Step', color='#ea580c', fontweight='bold')
    ax3.grid(True, alpha=0.3)
    ax3.legend(loc='upper right')
    
    # Plot 4: Power Spectrum (Log-Log) Showing 1/f Fractal Scaling
    ax4 = axes[3]
    ax4.loglog(periods, psd, color='#059669', lw=2)
    ax4.set_xlabel('Cycle Period in Earth Years [Log Scale]', fontweight='bold')
    ax4.set_ylabel('Spectral Power [Log Scale]', fontweight='bold')
    ax4.set_title('Fourier Power Spectrum of Default Cascades: Scale Invariance ($1/f^{\\alpha}$)', fontsize=11, fontweight='bold')
    ax4.grid(True, which="both", ls="--", alpha=0.3)
    
    # Highlight identified harmonic peaks
    for idx in top_indices[:3]:
        ax4.axvline(periods[idx], color='red', linestyle=':', alpha=0.6)
        ax4.annotate(f"T ≈ {periods[idx]:.1f} yrs", 
                     xy=(periods[idx], psd[idx]), 
                     xytext=(periods[idx]*1.1, psd[idx]*1.5),
                     arrowprops=dict(facecolor='black', arrowstyle='->', lw=0.8),
                     fontsize=9, fontweight='bold')
        
    plt.tight_layout()
    plt.savefig(filename, dpi=200)
    print(f"[SUCCESS] Saved high-resolution analysis chart to: {filename}")

if __name__ == "__main__":
    sim = HierarchicalCreditSystem(timesteps=3000, dt=0.1, seed=42)
    history = sim.run()
    analyze_and_plot(history, dt=0.1, filename="fractal_debt_cycles.png")
