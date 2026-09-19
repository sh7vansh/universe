from mpmath import mp
mp.dps = 100

import copy
import re
import readline
import sys
import os

from quantum_engine import CategoricalMachine, ExtensionClass, round_complex, GrothendieckObject, M_E, ALPHA_INV
from atomic_engine import synthesize_element_core, machine

class CategoricalChemistryEngine(CategoricalMachine):
    def __init__(self):
        super().__init__()
        # Using the globally initialized machine residual scale instead of calculating it again
        self.kappa_confinement = machine.kappa_confinement
        self.kappa_residual = machine.kappa_residual
        self.m_pi = machine.m_pi
        
        # Geometrically derived Rydberg Energy (using imported Electron Mass and Alpha)
        alpha = 1.0 / ALPHA_INV
        self.rydberg_energy = 0.5 * M_E * (alpha ** 2)

    def atomic_engine(self, symbol, tag):
        from atomic_engine import get_atom_by_symbol
        return get_atom_by_symbol(symbol, tag)

    def molecular_bind(self, atoms_list, name: str) -> GrothendieckObject:
        def bind_silent(A, B, pair_name):
            A_copy = copy.deepcopy(A)
            B_copy = copy.deepcopy(B)
            ext = ExtensionClass(pair_name, binding_energy=0.0)
            ext.virtual_nodes = list(A_copy.factors) + list(B_copy.factors)
            return self.exact_sequence_reconstruction(A_copy, B_copy, ext)

        res = atoms_list[0]
        for i in range(1, len(atoms_list)):
            res = bind_silent(res, atoms_list[i], f"silent_{i}")
            
        nodes = {f"atom_{i}": atom.factors for i, atom in enumerate(atoms_list)}
            
        def get_Z(factors):
            u = sum(1 for f in factors if f.identifier == 3)
            d = sum(1 for f in factors if f.identifier == 5)
            return round((2*u - d)/3.0)
            
        def get_A(factors):
            u = sum(1 for f in factors if f.identifier == 3)
            d = sum(1 for f in factors if f.identifier == 5)
            return round((u + d)/3.0)
            
        def get_valence(Z):
            if Z <= 2: return Z
            elif Z <= 10: return Z - 2
            elif Z <= 18: return Z - 10
            elif Z <= 36: return Z - 18
            elif Z <= 54: return Z - 36
            return Z - 54
            
        def get_magic_baseline(Z):
            return 2 if Z <= 2 else 8
            
        def get_magic_expanded(Z):
            if Z > 10 and Z <= 18: return 18
            if Z > 18 and Z <= 36: return 18
            if Z > 36: return 32
            return get_magic_baseline(Z)

        def calculate_topology_defect(use_hypervalency=False):
            sum_magic = 0
            sum_valence = 0
            sum_A = 0
            node_stats = []
            
            for tag, factors in nodes.items():
                Z = get_Z(factors)
                A = get_A(factors)
                V = get_valence(Z)
                M = get_magic_expanded(Z) if use_hypervalency and Z > 10 else get_magic_baseline(Z)
                sum_magic += M
                sum_valence += V
                sum_A += A
                node_stats.append({'tag': tag, 'Z': Z, 'A': A, 'V': V, 'M': M})
                
            total_shared = max(0.0, sum_magic - sum_valence)
            if total_shared > sum_valence: 
                return float('inf')
            
            total_bonds = total_shared / 2.0
            
            if len(node_stats) == 2:
                max_possible = min(node_stats[0]['V'], node_stats[1]['V'])
                if total_bonds > max_possible:
                    total_bonds = max_possible
                    
            kappa_mol = self.rydberg_energy / 3.0 
            
            sigma_bonds = min(total_bonds, len(node_stats) - 1.0) if len(node_stats) > 1 else total_bonds
            pi_bonds = total_bonds - sigma_bonds
            
            pi_1 = min(1.0, pi_bonds)
            pi_2 = max(0.0, pi_bonds - 1.0)
            
            attractive_defect = -(sigma_bonds * kappa_mol) - (pi_1 * kappa_mol * (mp.pi / 4.0)) - (pi_2 * kappa_mol * ((mp.pi / 4.0) ** 2))
            
            if use_hypervalency:
                attractive_defect *= 0.5
                
            magic_bonus = 0.0
            if total_bonds > len(node_stats) and len(node_stats) >= 3:
                magic_bonus = -(mp.pi / 4.0) * kappa_mol
            
            total_repulsion = 0.0
            volumetric_dampener = (sum_A / 2.0) ** (1.0 / 3.0) if sum_A > 0 else 1.0
            avg_bond = total_shared / len(node_stats) if len(node_stats) > 0 else 0
            
            avg_degree = 2.0 * total_bonds / len(node_stats) if len(node_stats) > 0 else 0
            if avg_degree <= 1.5:
                kissing_number = 2.0  
            elif avg_degree <= 2.5:
                kissing_number = 4.0  
            else:
                kissing_number = 6.0  
            
            N_nodes = len(node_stats)
            possible_edges = N_nodes * (N_nodes - 1) / 2.0 if N_nodes > 1 else 1.0
            adjacency_prob = min(1.0, total_bonds / possible_edges) if possible_edges > 0 else 1.0
            
            hub_index = max(range(N_nodes), key=lambda idx: node_stats[idx]['V']) if N_nodes > 0 else 0
            hub = node_stats[hub_index] if N_nodes > 0 else None
            
            if hub and hub['V'] <= 2:
                geometry_mult = 2.0
            elif hub and hub['V'] == 3:
                geometry_mult = mp.sqrt(3.0)
            else:
                geometry_mult = mp.sqrt(8.0/3.0)
            
            for i in range(len(node_stats)):
                for j in range(i + 1, len(node_stats)):
                    n1 = node_stats[i]
                    n2 = node_stats[j]
                    
                    cloud_shrinkage = (n1['V'] * n2['V']) / 16.0
                    
                    lone_pairs_1 = max(0.0, (n1['V'] - avg_bond) / 2.0)
                    lone_pairs_2 = max(0.0, (n2['V'] - avg_bond) / 2.0)
                    
                    repulsive_friction = ((lone_pairs_1 * lone_pairs_2) * adjacency_prob) / cloud_shrinkage
                    
                    is_n1_hub = (i == hub_index)
                    is_n2_hub = (j == hub_index)
                    
                    if N_nodes == 2 or is_n1_hub or is_n2_hub:
                        dist = 1.0
                    else:
                        dist = geometry_mult
                        
                    if use_hypervalency:
                        dist *= 1.5  
                        
                    rep = (repulsive_friction * kappa_mol) / (volumetric_dampener * dist)
                    
                    ionic_defect = float('inf')
                    if abs(n1['V'] - n2['V']) >= 4:
                        alpha = 1.0 / ALPHA_INV
                        dipole_cost = self.rydberg_energy * alpha * (max(n1['V'], n2['V']) / max(1, min(n1['V'], n2['V'])))
                        
                        ionic_dist = dist * 1.5874
                        coulomb_attraction = -2.0 * self.rydberg_energy / (volumetric_dampener * ionic_dist)
                        ionic_defect = coulomb_attraction + dipole_cost
                    
                    if ionic_defect < (attractive_defect + rep) and N_nodes == 2:
                        is_metal_1 = (n1['A'] / n1['V'] > 10.0) if n1['V'] > 0 else False
                        is_metal_2 = (n2['A'] / n2['V'] > 10.0) if n2['V'] > 0 else False
                        
                        if is_metal_1 != is_metal_2:
                            polar_mixing = 1.0 
                        else:
                            mass_asym = abs(n1['A'] - n2['A']) / (n1['A'] + n2['A'])
                            polar_mixing = 1.0 - (mass_asym ** 2)
                            
                        return (ionic_defect * polar_mixing) + ((attractive_defect + rep) * (1.0 - polar_mixing))
                        
                    if repulsive_friction == 0.0 and N_nodes > 2:
                        alpha = 1.0 / ALPHA_INV
                        Z_axis_1 = max(1.0, n1['V'] - avg_bond)
                        Z_axis_2 = max(1.0, n2['V'] - avg_bond)
                        rep = self.rydberg_energy * (kissing_number * alpha) * (Z_axis_1 * Z_axis_2) / (volumetric_dampener * dist)
                        
                    total_repulsion += rep
                    
            return attractive_defect + total_repulsion + magic_bonus

        defect_standard = calculate_topology_defect(use_hypervalency=False)
        defect_hypervalent = calculate_topology_defect(use_hypervalency=True)
        total_defect = min(defect_standard, defect_hypervalent)
        
        all_electrons = [f for f in res.factors if f.identifier == 2]
        for i, e in enumerate(all_electrons):
            e.color = f"mol_orb_{i//2}" 
            e.spin = 0.5 if i % 2 == 0 else -0.5 
            
        def recalc_sig(obj):
            sig = complex(1, 0)
            for f in obj.factors:
                val = float(f.identifier) if not f.is_anti else 1.0/float(f.identifier)
                sig *= round_complex((val * mp.exp(1j * mp.pi * f.spin)))
            obj.signature = sig
            return obj
            
        recalc_sig(res)
        
        res.mass += total_defect
        res.extensions.append(ExtensionClass(name, binding_energy=total_defect, virtual_nodes=res.factors))
        return res

import json
json_path_mol = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'assets', 'molecular_targets.json')
with open(json_path_mol, 'r') as f:
    MOLECULAR_TARGETS = json.load(f)


def parse_formula(formula):
    matches = re.findall(r'([A-Z][a-z]*)(\d*)', formula)
    components = []
    for sym, count_str in matches:
        count = int(count_str) if count_str else 1
        components.append((sym.lower(), count))
    return components

def main():
    print("=========================================")
    print(" Categorical Molecule Synthesizer (v2 Hierarchical)")
    print("=========================================")
    
    engine = CategoricalChemistryEngine()
    
    def synthesize_target(formula):
        comps = parse_formula(formula)
        if not comps:
            print("Invalid formula format. Try 'H2O' or 'CO2'.")
            return
            
        print(f"\n[+] Synthesizing {formula}...")
        
        atoms_list = []
        isolated_mass = 0.0
        
        for sym, count in comps:
            for i in range(count):
                tag = f"{sym.upper()}{i+1}"
                try:
                    atom = engine.atomic_engine(sym, tag)
                except ValueError as e:
                    print(f"Error: {e}")
                    return
                atoms_list.append(atom)
                isolated_mass += atom.mass
                
        if len(atoms_list) < 2:
            print("A molecule requires at least 2 atoms.")
            return
            
        print(f"[+] Executing Geometric Molecular Bind...")
        molecule = engine.molecular_bind(atoms_list, formula)
        
        bond_defect = molecule.mass - isolated_mass
        bond_defect_ev = bond_defect * 1_000_000
        
        total_quarks = sum(1 for f in molecule.factors if f.identifier in (3,5))
        total_electrons = sum(1 for f in molecule.factors if f.identifier == 2)
        
        print("\n=========================================")
        print(f" Synthesis Complete: {formula}")
        print("=========================================")
        print(f" [ Mass Analysis ]")
        print(f"   Theoretical Mass : {molecule.mass:,.3f} MeV")
        print(f"   Isolated Parts   : {isolated_mass:,.3f} MeV")
        print(f"   Bond Defect (BE) : {bond_defect:,.6f} MeV ({bond_defect_ev:,.2f} eV)")
        
        target = MOLECULAR_TARGETS.get(formula.lower())
        if target:
            error = abs(bond_defect_ev - target)
            print(f"\n [ Accuracy & Error ]")
            print(f"   True Bond Energy : {target:.2f} eV")
            print(f"   Model Error      : {error:.2f} eV")
            
        print(f"\n [ Categorical Composition ]")
        print(f"   Total Particles  : {len(molecule.factors)}")
        print(f"   Quarks           : {total_quarks}")
        print(f"   Electrons        : {total_electrons}")
        
        phase = mp.phase(molecule.signature)
        print(f"\n [ Quantum State ]")
        print(f"   Net Spin         : {molecule.spin}")
        print(f"   Float Magnitude  : {abs(molecule.signature):.3e}")
        print(f"   Signature Phase  : {phase:.3f} rad")
        print("=========================================\n")

    while True:
        print("Type a chemical formula (e.g. 'H2O', 'CO2'). Type 'batch' for all targets. ('q' to quit)")
        query = input("> ").strip()
        
        if query.lower() in ('q', 'quit', 'exit'):
            break
        elif query.lower() == 'batch':
            print("\n[+] Running batch synthesis on all known molecular targets...\n")
            print(f"{'Molecule':<10} | {'Pred BE (eV)':<12} | {'True BE (eV)':<12} | {'Error (eV)':<10}")
            print("-" * 55)
            
            total_err = 0.0
            count = 0
            for formula, target_ev in MOLECULAR_TARGETS.items():
                comps = parse_formula(formula.upper())
                atoms_list = []
                isolated_mass = 0.0
                
                # We need to build a new engine instance for the batch scope or just use the global scope
                engine = CategoricalChemistryEngine()
                
                for sym, c in comps:
                    for i in range(c):
                        tag = f"{sym.upper()}{i+1}"
                        atom = engine.atomic_engine(sym, tag)
                        atoms_list.append(atom)
                        isolated_mass += atom.mass
                        
                molecule = engine.molecular_bind(atoms_list, formula.upper())
                pred_ev = (molecule.mass - isolated_mass) * 1_000_000
                err = abs(pred_ev - target_ev)
                
                total_err += err
                count += 1
                
                print(f"{formula.upper():<10} | {pred_ev:<12.2f} | {target_ev:<12.2f} | {err:<10.2f}")
                
            print("-" * 55)
            print(f"Average Accuracy Error across {count} molecules: {total_err/count:.3f} eV\n")
        elif query:
            synthesize_target(query)

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nExiting...")
        sys.exit(0)
