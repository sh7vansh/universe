"""
Steve Keen / Minsky Non-Linear Dynamical System Simulation
==========================================================
Simulates the continuous differential equations of the Financial Instability Hypothesis.
Uses a pure Python 4th-Order Runge-Kutta (RK4) integrator.

State Variables:
  lambda (λ): Employment rate
  omega  (ω): Wage share of GDP
  d:          Private debt to GDP ratio
"""

import math

class KeenMinskyModel:
    def __init__(self, 
                 alpha=0.025,   # Productivity growth rate
                 beta=0.015,    # Population growth rate
                 nu=3.0,        # Capital-to-output ratio
                 r=0.04,        # Real interest rate on debt
                 years=60.0,
                 dt=0.01):
        self.alpha = alpha
        self.beta = beta
        self.nu = nu
        self.r = r
        self.years = years
        self.dt = dt
        
        # Nonlinear investment function: phi(pi) where profit share pi = 1 - omega - r*d
        # Entrepreneurs invest heavily when profits are high (accelerator effect)
        self.phi_0 = -0.06
        self.phi_1 = 0.05
        
    def investment_function(self, profit_share):
        # Nonlinear sigmoid / exponential investment response
        return 0.04 + 0.30 * (math.exp(3.0 * (profit_share - 0.16)) - 1.0) / (math.exp(3.0 * (profit_share - 0.16)) + 1.0)
        
    def phillips_curve(self, employment):
        # Wage bargaining power rises exponentially as employment nears full capacity
        return -0.04 + 0.04 / ((1.0 - employment)**1.5 + 0.01)

    def derivatives(self, state):
        lam, omega, d = state
        
        # Profit share: Output minus wages minus interest payments
        pi = 1.0 - omega - self.r * d
        
        # Investment rate
        i_rate = self.investment_function(pi)
        
        # Economic growth rate g = i_rate / nu
        g = i_rate / self.nu
        
        # 1. d(lambda)/dt = lambda * (g - alpha - beta)
        d_lam = lam * (g - self.alpha - self.beta)
        
        # 2. d(omega)/dt = omega * (Phillips(lambda) - alpha)
        d_omega = omega * (self.phillips_curve(lam) - self.alpha)
        
        # 3. d(d)/dt = Investment - Profit - d * g
        d_debt = i_rate - pi - d * g
        
        return [d_lam, d_omega, d_debt]

    def rk4_step(self, state):
        k1 = self.derivatives(state)
        s2 = [state[i] + 0.5 * self.dt * k1[i] for i in range(3)]
        k2 = self.derivatives(s2)
        s3 = [state[i] + 0.5 * self.dt * k2[i] for i in range(3)]
        k3 = self.derivatives(s3)
        s4 = [state[i] + self.dt * k3[i] for i in range(3)]
        k4 = self.derivatives(s4)
        
        new_state = [state[i] + (self.dt / 6.0) * (k1[i] + 2*k2[i] + 2*k3[i] + k4[i]) for i in range(3)]
        return new_state

    def simulate(self, init_state=[0.88, 0.70, 0.50]):
        steps = int(self.years / self.dt)
        time_hist = [0.0]
        lam_hist = [init_state[0]]
        omega_hist = [init_state[1]]
        debt_hist = [init_state[2]]
        
        state = list(init_state)
        for step in range(steps):
            state = self.rk4_step(state)
            
            # Boundary checks
            state[0] = max(0.01, min(0.99, state[0]))
            state[1] = max(0.01, min(0.99, state[1]))
            state[2] = max(0.0, min(10.0, state[2]))
            
            time_hist.append((step + 1) * self.dt)
            lam_hist.append(state[0])
            omega_hist.append(state[1])
            debt_hist.append(state[2])
            
            # Debt singularity threshold
            if state[2] >= 3.5:
                # System enters insolvency collapse
                pass
                
        return time_hist, lam_hist, omega_hist, debt_hist

def print_ascii_chart(title, x_data, y_data, width=65, height=9, y_unit=""):
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
        print(f"{y_val:8.2f} {y_unit} |{row_str}|")
    print(f"         0{' ' * (width - 12)}{x_data[-1]:.0f} Years")

if __name__ == "__main__":
    print("="*70)
    print(" STEVE KEEN / MINSKY FINANCIAL INSTABILITY ODE SIMULATION")
    print("="*70)
    model = KeenMinskyModel(years=70.0, dt=0.01)
    t, lam, omega, debt = model.simulate()
    
    print_ascii_chart("EMPLOYMENT RATE (λ) - Stable Short Cycles Before Debt Singularity", 
                      t, [x * 100 for x in lam], width=62, height=8, y_unit="%")
                      
    print_ascii_chart("PRIVATE DEBT TO GDP RATIO (d) - Secular Upward Drift into Singularity", 
                      t, debt, width=62, height=9, y_unit="xGDP")
