import sys
import os
import math

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine, GrothendieckObject, ExtensionClass

class UnifiedCollapseMachine(CategoricalMachine):
    def __init__(self):
        super().__init__()
        
        # --- THE ONLY FUNDAMENTAL INPUTS ---
        self.m_u = 2.2        # Bare Up Quark (MeV)
        self.m_d = 4.7        # Bare Down Quark (MeV)
        self.f_pi = 93.0      # Pion Decay Constant (MeV)
        self.chiral_condensate = -(284.0)**3  # Vacuum Scale
        self.g_A = 1.27       # Axial vector coupling (dimensionless)
        self.hbar_c = 197.3   # Conversion factor
        
        # --- DYNAMIC DERIVATIONS ---
        
        # 1. Derive Pion Mass (Confinement Scale) via GMOR
        self.m_pi = math.sqrt(- ((self.m_u + self.m_d) * self.chiral_condensate) / (self.f_pi**2))
        self.kappa_confinement = self.m_pi
        
        # Note: Residual scale requires the emergent Nucleon mass (m_N), 
        # which we can only calculate after the engine builds a Proton.
        self.kappa_residual = None 

    def is_color_singlet(self, obj: GrothendieckObject) -> bool:
        net = {'red': 0, 'green': 0, 'blue': 0}
        for f in obj.factors:
            if f.color:
                base_color = f.color.split('_')[0]
                val = -1 if f.is_anti else 1
                if 'red' in base_color: net['red'] += val
                elif 'green' in base_color: net['green'] += val
                elif 'blue' in base_color: net['blue'] += val
        return (len(obj.factors) > 0) and (net['red'] == net['green'] == net['blue'])

    def calculate_friction(self, A: GrothendieckObject, B: GrothendieckObject) -> int:
        def get_virtual_count(obj):
            if self.is_color_singlet(obj): return 0 
            return sum(len(ext.virtual_nodes) for ext in obj.extensions)
        optimal = len(A.factors) + len(B.factors)
        return (optimal + get_virtual_count(A) + get_virtual_count(B) + optimal) - optimal

    def confinement_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str) -> GrothendieckObject:
        delta_L = self.calculate_friction(A, B)
        ext = ExtensionClass(name, binding_energy=(delta_L * self.kappa_confinement))
        ext.virtual_nodes = list(A.factors) + list(B.factors)
        return self.exact_sequence_reconstruction(A, B, ext)

    def calculate_residual_scale(self, emergent_nucleon_mass: float):
        # 2. Derive Coupling Constant via Goldberger-Treiman Relation
        g_pi_nn = (self.g_A * emergent_nucleon_mass) / self.f_pi
        g_sq_over_4pi = (g_pi_nn**2) / (4 * math.pi)
        
        # 3. Derive Interaction Radius from Pion Compton Wavelength
        r_0 = self.hbar_c / self.m_pi
        r_fm = 1.6 * r_0  # Effective overlap distance
        
        # 4. Derive Yukawa Mass Defect
        x = r_fm / r_0
        yukawa_potential = - g_sq_over_4pi * self.m_pi * (math.exp(-x) / x)
        
        # Scale to our categorical nodes (27 nodes for He-4 geometry)
        self.kappa_residual = yukawa_potential / 27.0 
        print(f"Dynamically Calculated g_pi_NN: {g_pi_nn:.2f}")
        print(f"Dynamically Calculated g^2/4pi: {g_sq_over_4pi:.2f}")

    def nuclear_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str) -> GrothendieckObject:
        if self.kappa_residual is None:
            raise ValueError("Must calculate residual scale from a bound nucleon first.")
        delta_L = self.calculate_friction(A, B)
        ext = ExtensionClass(name, binding_energy=(delta_L * self.kappa_residual))
        ext.virtual_nodes = list(A.factors) + list(B.factors)
        return self.exact_sequence_reconstruction(A, B, ext)

def build_nucleon(machine, q1_id, q2_id, q3_id, name, prefix):
    q1 = machine.get_simple(q1_id, color=f"red_{prefix}")
    q2 = machine.get_simple(q2_id, color=f"blue_{prefix}")
    q3 = machine.get_simple(q3_id, color=f"green_{prefix}")
    diquark = machine.confinement_bind(q1, q2, f"{name} Diquark")
    return machine.confinement_bind(diquark, q3, name)

def run_test():
    machine = UnifiedCollapseMachine()
    
    # STEP 1: Build the first Proton to derive the emergent mass
    p1 = build_nucleon(machine, 3, 3, 5, "Proton 1", "p1")
    print(f"Emergent Proton Mass: {p1.mass:.2f} MeV")
    
    # STEP 2: Engine dynamically calculates nuclear forces based on the new Proton mass!
    machine.calculate_residual_scale(p1.mass)
    
    print(f"\nGMOR Scale (m_pi): {machine.kappa_confinement:.2f} MeV")
    print(f"Yukawa Residual Scale: {machine.kappa_residual:.2f} MeV\n")
    
    # STEP 3: Build the rest of the atoms using the dynamically linked scales
    p2 = build_nucleon(machine, 3, 3, 5, "Proton 2", "p2")
    n1 = build_nucleon(machine, 3, 5, 5, "Neutron 1", "n1")
    n2 = build_nucleon(machine, 3, 5, 5, "Neutron 2", "n2")
    
    he2 = machine.nuclear_bind(p1, p2, "He-2")
    he3 = machine.nuclear_bind(he2, n1, "He-3")
    he4 = machine.nuclear_bind(he3, n2, "Helium-4")
    
    print(f"Helium-4 Mass: {he4.mass:.2f} MeV")
    print(f"Total Helium-4 Mass Defect: {he4.mass - (2*p1.mass + 2*n1.mass):.2f} MeV")
    
if __name__ == "__main__":
    run_test()
