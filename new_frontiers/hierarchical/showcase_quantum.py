import math
from fractions import Fraction
from quantum_engine import CategoricalMachine, GrothendieckObject, SimpleObject, ExtensionClass, ALPHA_INV

def discover_particles():
    machine = CategoricalMachine()
    
    print("=========================================")
    print("   QUANTUM ENGINE SHOWCASE (LAYER 1)")
    print("=========================================")
    
    void = machine.get_simple(0)
    photon = machine.get_simple(1)
    
    print(f"\n[+] Vacuum State (Bosons):")
    print(f"    Void: {void}")
    print(f"    Photon: {photon}")
    
    print("\n[+] Leptons (Generation 1, 2, 3):")
    electron = machine.get_simple(2)
    muon = machine.get_simple(11)
    tau = machine.get_simple(17)
    print(f"    Electron: {electron}")
    print(f"    Muon: {muon}")
    print(f"    Tau: {tau}")

    print("\n[+] Quarks (Generation 1, 2, 3):")
    up_red = machine.get_simple(3, color="red")
    down_green = machine.get_simple(5, color="green")
    strange = machine.get_simple(7)
    charm = machine.get_simple(13)
    bottom = machine.get_simple(19)
    top = machine.get_simple(23)
    
    print(f"    Up Quark (Red): {up_red}")
    print(f"    Down Quark (Green): {down_green}")
    print(f"    Strange Quark: {strange}")
    print(f"    Charm Quark: {charm}")
    print(f"    Bottom Quark: {bottom}")
    print(f"    Top Quark: {top}")
    
    print("\n[+] Neutrinos (Topological Cancellation):")
    anti_down = machine.get_simple(5, is_anti=True, color="green")
    ext_mass_cancel_e = ExtensionClass("Neutrino Mass Cancellation", -(electron.mass + up_red.mass + anti_down.mass))
    comp1 = machine.exact_sequence_reconstruction(electron, up_red)
    e_neutrino = machine.exact_sequence_reconstruction(comp1, anti_down, ext=ext_mass_cancel_e)
    print(f"    Electron Neutrino: {e_neutrino}")

    anti_strange = machine.get_simple(7, is_anti=True, color="green")
    charm_red = machine.get_simple(13, color="red")
    ext_mass_cancel_mu = ExtensionClass("Muon Neutrino Mass Cancellation", -(muon.mass + charm_red.mass + anti_strange.mass))
    comp2 = machine.exact_sequence_reconstruction(muon, charm_red)
    mu_neutrino = machine.exact_sequence_reconstruction(comp2, anti_strange, ext=ext_mass_cancel_mu)
    print(f"    Muon Neutrino: {mu_neutrino}")

    anti_bottom = machine.get_simple(19, is_anti=True, color="green")
    top_red = machine.get_simple(23, color="red")
    ext_mass_cancel_tau = ExtensionClass("Tau Neutrino Mass Cancellation", -(tau.mass + top_red.mass + anti_bottom.mass))
    comp3 = machine.exact_sequence_reconstruction(tau, top_red)
    tau_neutrino = machine.exact_sequence_reconstruction(comp3, anti_bottom, ext=ext_mass_cancel_tau)
    print(f"    Tau Neutrino: {tau_neutrino}")

    print("\n[+] W & Z Bosons (Transition Morphisms):")
    w_minus_sig = Fraction(5, 3)
    print(f"    W- Boson Morphism Signature: {w_minus_sig} (Down -> Up decay)")
    w_plus_sig = Fraction(3, 5)
    print(f"    W+ Boson Morphism Signature: {w_plus_sig} (Up -> Down decay)")
    
    sin_sq_theta = 2.0 / 9.0
    cos_theta = math.sqrt(1.0 - sin_sq_theta) # sqrt(7)/3
    m_W = 80.377
    m_Z = m_W / cos_theta
    print(f"    Geometric Weinberg Angle: sin^2(θ) = 2/9")
    print(f"    Z Boson Mass (Predicted): {m_Z:.3f} GeV")

    print("\n[+] Gluons (SU(3) Color Permutations):")
    gluon_matrix = [
        [complex(0, 0), complex(1, 0), complex(0, 0)],
        [complex(0, 0), complex(0, 0), complex(0, 0)],
        [complex(0, 0), complex(0, 0), complex(0, 0)]
    ]
    print(f"    Gluon Operator (Red-AntiBlue): {gluon_matrix[0]}")
    print(f"                                   {gluon_matrix[1]}")
    print(f"                                   {gluon_matrix[2]}")

    print("\n[+] Higgs Boson (Geometric Weak Coupling):")
    alpha = 1.0 / ALPHA_INV
    g = 3.0 * math.sqrt(2.0 * math.pi * alpha)
    m_H = m_W / g
    print(f"    Geometric Weak Coupling (g): {g:.4f}")
    print(f"    Higgs Boson Mass (Predicted): {m_H:.3f} GeV")
    print(f"    Higgs Self-Coupling (λ): 1/8")

    print("=========================================\n")

if __name__ == "__main__":
    discover_particles()
