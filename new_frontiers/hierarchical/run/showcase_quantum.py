from mpmath import mp
mp.dps = 100
from fractions import Fraction
from core.quantum_engine import CategoricalMachine, ExtensionClass, CONFIG

def discover_particles():
    machine = CategoricalMachine()

    print("=========================================")
    print("   QUANTUM ENGINE SHOWCASE (LAYER 1)")
    print("=========================================")

    void = machine.get_simple(0)
    photon = machine.get_simple(1)

    print(f"\n[+] Vacuum State (Bosons):\n    Void: {void}\n    Photon: {photon}")

    electron = machine.get_simple(2)
    muon = machine.get_simple(11)
    tau = machine.get_simple(17)
    print(f"\n[+] Leptons (Gen 1-3):\n    Electron: {electron}\n    Muon: {muon}\n    Tau: {tau}")

    up_red = machine.get_simple(3, color="red")
    down_green = machine.get_simple(5, color="green")
    strange = machine.get_simple(7)
    charm = machine.get_simple(13)
    bottom = machine.get_simple(19)
    top = machine.get_simple(23)
    print(f"\n[+] Quarks (Gen 1-3):\n    Up: {up_red}\n    Down: {down_green}\n    Strange: {strange}\n    Charm: {charm}\n    Bottom: {bottom}\n    Top: {top}")

    anti_down = machine.get_simple(5, is_anti=True, color="green")
    ext_mass_cancel_e = ExtensionClass("Neutrino Mass Cancellation", -(electron.mass + up_red.mass + anti_down.mass))
    comp1 = machine.exact_sequence_reconstruction(electron, up_red)
    e_neutrino = machine.exact_sequence_reconstruction(comp1, anti_down, ext=ext_mass_cancel_e)

    anti_strange = machine.get_simple(7, is_anti=True, color="green")
    charm_red = machine.get_simple(13, color="red")
    ext_mass_cancel_mu = ExtensionClass("Muon Neutrino Mass Cancellation", -(muon.mass + charm_red.mass + anti_strange.mass))
    comp2 = machine.exact_sequence_reconstruction(muon, charm_red)
    mu_neutrino = machine.exact_sequence_reconstruction(comp2, anti_strange, ext=ext_mass_cancel_mu)

    anti_bottom = machine.get_simple(19, is_anti=True, color="green")
    top_red = machine.get_simple(23, color="red")
    ext_mass_cancel_tau = ExtensionClass("Tau Neutrino Mass Cancellation", -(tau.mass + top_red.mass + anti_bottom.mass))
    comp3 = machine.exact_sequence_reconstruction(tau, top_red)
    tau_neutrino = machine.exact_sequence_reconstruction(comp3, anti_bottom, ext=ext_mass_cancel_tau)
    print(f"\n[+] Neutrinos:\n    e_nu: {e_neutrino}\n    mu_nu: {mu_neutrino}\n    tau_nu: {tau_neutrino}")

    sin_sq_theta = 2.0 / 9.0
    cos_theta = mp.sqrt(1.0 - sin_sq_theta)
    m_W = 80.377
    m_Z = m_W / cos_theta
    print(f"\n[+] Electroweak Bosons:\n    W- sig: {Fraction(5, 3)}, W+ sig: {Fraction(3, 5)}\n    Z Boson Mass: {m_Z:.3f} GeV")

    alpha = 1.0 / CONFIG.alpha_inv
    g = 3.0 * mp.sqrt(2.0 * mp.pi * alpha)
    m_H = m_W / g
    print(f"\n[+] Higgs Boson:\n    Weak Coupling (g): {g:.4f}\n    Higgs Mass: {m_H:.3f} GeV")
    print("=========================================\n")

if __name__ == "__main__":
    discover_particles()
