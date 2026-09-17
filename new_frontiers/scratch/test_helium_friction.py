import sys
import os
import math

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../src')))
from unified_categorical_engine import CategoricalMachine, GrothendieckObject, ExtensionClass

class FirstPrinciplesMachine(CategoricalMachine):
    def __init__(self):
        super().__init__()
        
        # 1. GMOR CONFINEMENT EQUATION
        self.m_u = 2.2  
        self.m_d = 4.7  
        self.f_pi = 93.0  
        self.chiral_condensate = -(284.0)**3 
        self.kappa_confinement = math.sqrt(- ((self.m_u + self.m_d) * self.chiral_condensate) / (self.f_pi**2))
        
        # 2. YUKAWA PION EXCHANGE EQUATION
        g_pi_nn = 14.0  
        hbar_c = 197.3  
        m_pi = 135.0    
        r_fm = 2.45     
        
        x = r_fm / (hbar_c / m_pi) 
        yukawa_potential = - g_pi_nn * m_pi * (math.exp(-x) / x)
        
        self.kappa_residual = yukawa_potential / 27.0 

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
            if self.is_color_singlet(obj):
                return 0 
            return sum(len(ext.virtual_nodes) for ext in obj.extensions)

        optimal_length = len(A.factors) + len(B.factors)
        accumulated_virtual = get_virtual_count(A) + get_virtual_count(B)
        new_virtual = len(A.factors) + len(B.factors)
        
        return (optimal_length + accumulated_virtual + new_virtual) - optimal_length

    def confinement_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str) -> GrothendieckObject:
        delta_L = self.calculate_friction(A, B)
        ext = ExtensionClass(name, binding_energy=(delta_L * self.kappa_confinement))
        ext.virtual_nodes = list(A.factors) + list(B.factors)
        return self.exact_sequence_reconstruction(A, B, ext)

    def nuclear_bind(self, A: GrothendieckObject, B: GrothendieckObject, name: str) -> GrothendieckObject:
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
    machine = FirstPrinciplesMachine()
    print(f"GMOR Confinement Scale:  {machine.kappa_confinement:.2f} MeV")
    print(f"Yukawa Residual Scale:  {machine.kappa_residual:.2f} MeV (r = 2.45 fm)\n")
    
    p1 = build_nucleon(machine, 3, 3, 5, "Proton 1", "p1")
    p2 = build_nucleon(machine, 3, 3, 5, "Proton 2", "p2")
    p3 = build_nucleon(machine, 3, 3, 5, "Proton 3", "p3")
    n1 = build_nucleon(machine, 3, 5, 5, "Neutron 1", "n1")
    n2 = build_nucleon(machine, 3, 5, 5, "Neutron 2", "n2")
    n3 = build_nucleon(machine, 3, 5, 5, "Neutron 3", "n3")
    n4 = build_nucleon(machine, 3, 5, 5, "Neutron 4", "n4")
    
    he2 = machine.nuclear_bind(p1, p2, "He-2")
    he3 = machine.nuclear_bind(he2, n1, "He-3")
    he4 = machine.nuclear_bind(he3, n2, "He-4")
    
    print(f"He-4 Mass: {he4.mass:.2f} MeV (Defect: {he4.mass - (2*p1.mass+2*n1.mass):.2f} MeV)\n")
    
    # Build Lithium-6 (3 protons, 3 neutrons)
    li5 = machine.nuclear_bind(he4, p3, "Li-5")
    li6 = machine.nuclear_bind(li5, n3, "Li-6")
    
    print(f"Li-5 Mass: {li5.mass:.2f} MeV (Defect: {li5.mass - (he4.mass + p3.mass):.2f} MeV)")
    print(f"Li-6 Mass: {li6.mass:.2f} MeV (Defect: {li6.mass - (li5.mass + n3.mass):.2f} MeV)")
    print(f"Total Li-6 Mass Defect: {li6.mass - (3*p1.mass + 3*n1.mass):.2f} MeV\n")
    
    # Build Lithium-7 (3 protons, 4 neutrons)
    li7 = machine.nuclear_bind(li6, n4, "Li-7")
    print(f"Li-7 Mass: {li7.mass:.2f} MeV (Defect: {li7.mass - (li6.mass + n4.mass):.2f} MeV)")
    print(f"Total Li-7 Mass Defect: {li7.mass - (3*p1.mass + 4*n1.mass):.2f} MeV")
    
if __name__ == "__main__":
    run_test()
