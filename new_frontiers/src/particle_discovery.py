from unified_categorical_engine import CategoricalMachine, GrothendieckObject, SimpleObject, ExtensionClass
from fractions import Fraction

def discover_particles():
    machine = CategoricalMachine()
    
    print("--- PARTICLE ONTOLOGY DISCOVERY ---")
    
    void = machine.get_simple(0)
    photon = machine.get_simple(1)
    
    print(f"Void: {void}")
    print(f"Photon: {photon}")
    
    print("\n--- Massive Fermions (Primes) ---")
    electron = machine.get_simple(2)
    # Instantiate quarks with explicit colors to avoid Pauli Exclusion crashes
    up_red = machine.get_simple(3, color="red")
    up_blue = machine.get_simple(3, color="blue")
    down_green = machine.get_simple(5, color="green")
    
    print(f"Electron: {electron}")
    print(f"Up Quark Red: {up_red}")
    print(f"Up Quark Blue: {up_blue}")
    print(f"Down Quark Green: {down_green}")

    print("\n--- Heavy Quarks (Geometrically Derived Frictions) ---")
    strange = machine.get_simple(7)
    charm = machine.get_simple(13)
    bottom = machine.get_simple(19)
    top = machine.get_simple(23)
    
    print(f"Strange Quark (f_pi anchor): {strange}")
    print(f"Charm Quark (SU(3) root exponent): {charm}")
    print(f"Bottom Quark (alpha^-1 / N_c scaled): {bottom}")
    print(f"Top Quark (Generation 2/1 exponent): {top}")
    
    print("\n--- Neutrinos (Rational Fractions) ---")
    anti_down = machine.get_simple(5, is_anti=True, color="green")
    # Neutrinos have zero mass, forcing mass cancellation via Ext1 topological boundary
    ext_mass_cancel = ExtensionClass("Neutrino Mass Cancellation", -(electron.mass + up_red.mass + anti_down.mass))
    
    comp1 = machine.exact_sequence_reconstruction(electron, up_red)
    neutrino = machine.exact_sequence_reconstruction(comp1, anti_down, ext=ext_mass_cancel)
    print(f"Electron Neutrino: {neutrino}")

    print("\n--- Geometric Nucleosynthesis (Liquid Drop Model) ---")
    diquark = machine.confinement_bind(up_red, up_blue, "Diquark")
    proton = machine.confinement_bind(diquark, down_green, "Proton")
    
    # Needs a baseline residual scale anchored from a single nucleon
    machine.calculate_residual_scale(proton.mass)
    
    # We must synthesize a neutron for Helium
    up_green = machine.get_simple(3, color="green")
    down_red = machine.get_simple(5, color="red")
    down_blue = machine.get_simple(5, color="blue")
    neutron = machine.confinement_bind(machine.confinement_bind(up_green, down_red, "DiQ"), down_blue, "Neutron")
    
    print(f"Proton (Singlet): {proton}")
    print(f"Neutron (Singlet): {neutron}")
    
    # Synthesize Deuteron Nucleus (Proton + Neutron)
    deuteron = machine.nuclear_bind(proton, neutron, "Deuteron")
    print(f"Deuteron Nucleus: {deuteron}")
    
    print("\n--- Electroweak Binding (Atoms) ---")
    hydrogen = machine.electroweak_bind(proton, electron, "Hydrogen")
    print(f"Hydrogen Atom: {hydrogen}")

    print("\n--- Ext1 Virtual Memory and CP Violation ---")
    charm_red = machine.get_simple(13, color="red")
    anti_charm_red = machine.get_simple(13, is_anti=True, color="red")
    
    # Define CKM matrix for CP violation
    ckm_matrix = [
        [complex(0.974, 0), complex(0.225, 0)],
        [complex(-0.225, 0), complex(0.974, 0)]
    ]
    weak_force = ExtensionClass("Weak Force W-Boson", 0.0, matrix=ckm_matrix)
    
    j_psi = machine.exact_sequence_reconstruction(charm_red, anti_charm_red, ext=weak_force)
    print(f"J/Psi (Charm + Anti-Charm): {j_psi}")
    
    virtual_memory = [n.name for n in j_psi.extensions[-1].virtual_nodes]
    print(f"Virtual State Memory logged in Extension: {virtual_memory}")

if __name__ == "__main__":
    discover_particles()
