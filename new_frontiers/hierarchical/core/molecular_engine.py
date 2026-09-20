from mpmath import mp
mp.dps = 100

import copy
import re
import json
from pathlib import Path
from typing import List

from core.quantum_engine import CategoricalMachine, ExtensionClass, GrothendieckObject, M_E, CONFIG
from core.atomic_engine import get_atom_by_symbol, machine

JSON_PATH_MOL = Path(__file__).resolve().parents[1] / "assets" / "molecular_targets.json"
with open(JSON_PATH_MOL, "r") as f:
    MOLECULAR_TARGETS = json.load(f)

RYDBERG_ENERGY = 0.5 * M_E * ((1.0 / CONFIG.alpha_inv) ** 2)

def parse_formula(formula: str) -> List[tuple]:
    return [(sym.lower(), int(c) if c else 1) for sym, c in re.findall(r'([A-Z][a-z]*)(\d*)', formula)]

def molecular_bind(atoms_list: List[GrothendieckObject], name: str) -> GrothendieckObject:
    def bind_silent(A, B, pair_name):
        A_copy = copy.deepcopy(A)
        B_copy = copy.deepcopy(B)
        ext = ExtensionClass(pair_name, binding_energy=0.0, virtual_nodes=list(A_copy.factors) + list(B_copy.factors))
        return machine.exact_sequence_reconstruction(A_copy, B_copy, ext)

    res = atoms_list[0]
    for i in range(1, len(atoms_list)):
        res = bind_silent(res, atoms_list[i], f"silent_{i}")

    nodes = {f"atom_{i}": atom.factors for i, atom in enumerate(atoms_list)}

    def get_Z(factors):
        u = sum(1 for f in factors if f.identifier == 3)
        d = sum(1 for f in factors if f.identifier == 5)
        return round((2 * u - d) / 3.0)

    def get_A(factors):
        u = sum(1 for f in factors if f.identifier == 3)
        d = sum(1 for f in factors if f.identifier == 5)
        return round((u + d) / 3.0)

    def get_valence(Z):
        if Z <= 2: return Z
        if Z <= 10: return Z - 2
        if Z <= 18: return Z - 10
        if Z <= 36: return Z - 18
        if Z <= 54: return Z - 36
        return Z - 54

    def get_magic_baseline(Z):
        return 2 if Z <= 2 else 8

    def get_magic_expanded(Z):
        if 10 < Z <= 36: return 18
        if Z > 36: return 32
        return get_magic_baseline(Z)

    def calculate_topology_defect(use_hypervalency=False):
        sum_magic, sum_valence, sum_A = 0, 0, 0
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
            total_bonds = min(total_bonds, node_stats[0]['V'], node_stats[1]['V'])

        kappa_mol = RYDBERG_ENERGY / 3.0 
        sigma_bonds = min(total_bonds, len(node_stats) - 1.0) if len(node_stats) > 1 else total_bonds
        pi_bonds = total_bonds - sigma_bonds

        pi_1 = min(1.0, pi_bonds)
        pi_2 = max(0.0, pi_bonds - 1.0)

        attractive_defect = -(sigma_bonds * kappa_mol) - (pi_1 * kappa_mol * (mp.pi / 4.0)) - (pi_2 * kappa_mol * ((mp.pi / 4.0) ** 2))
        if use_hypervalency:
            attractive_defect *= 0.5

        magic_bonus = -(mp.pi / 4.0) * kappa_mol if (total_bonds > len(node_stats) and len(node_stats) >= 3) else 0.0

        total_repulsion = 0.0
        volumetric_dampener = (sum_A / 2.0) ** (1.0 / 3.0) if sum_A > 0 else 1.0
        avg_bond = total_shared / len(node_stats) if len(node_stats) > 0 else 0

        avg_degree = 2.0 * total_bonds / len(node_stats) if len(node_stats) > 0 else 0
        kissing_number = 2.0 if avg_degree <= 1.5 else (4.0 if avg_degree <= 2.5 else 6.0)

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
            geometry_mult = mp.sqrt(8.0 / 3.0)

        for i in range(len(node_stats)):
            for j in range(i + 1, len(node_stats)):
                n1, n2 = node_stats[i], node_stats[j]
                cloud_shrinkage = (n1['V'] * n2['V']) / 16.0
                lone_pairs_1 = max(0.0, (n1['V'] - avg_bond) / 2.0)
                lone_pairs_2 = max(0.0, (n2['V'] - avg_bond) / 2.0)

                repulsive_friction = ((lone_pairs_1 * lone_pairs_2) * adjacency_prob) / cloud_shrinkage
                dist = 1.0 if (N_nodes == 2 or i == hub_index or j == hub_index) else geometry_mult
                if use_hypervalency:
                    dist *= 1.5  

                rep = (repulsive_friction * kappa_mol) / (volumetric_dampener * dist)

                ionic_defect = float('inf')
                if abs(n1['V'] - n2['V']) >= 4:
                    alpha = 1.0 / CONFIG.alpha_inv
                    dipole_cost = RYDBERG_ENERGY * alpha * (max(n1['V'], n2['V']) / max(1, min(n1['V'], n2['V'])))
                    coulomb_attraction = -2.0 * RYDBERG_ENERGY / (volumetric_dampener * (dist * 1.5874))
                    ionic_defect = coulomb_attraction + dipole_cost

                if ionic_defect < (attractive_defect + rep) and N_nodes == 2:
                    is_metal_1 = (n1['A'] / n1['V'] > 10.0) if n1['V'] > 0 else False
                    is_metal_2 = (n2['A'] / n2['V'] > 10.0) if n2['V'] > 0 else False
                    if is_metal_1 != is_metal_2:
                        polar_mixing = 1.0 
                    else:
                        polar_mixing = 1.0 - ((abs(n1['A'] - n2['A']) / (n1['A'] + n2['A'])) ** 2)
                    return (ionic_defect * polar_mixing) + ((attractive_defect + rep) * (1.0 - polar_mixing))

                if repulsive_friction == 0.0 and N_nodes > 2:
                    alpha = 1.0 / CONFIG.alpha_inv
                    rep = RYDBERG_ENERGY * (kissing_number * alpha) * max(1.0, n1['V'] - avg_bond) * max(1.0, n2['V'] - avg_bond) / (volumetric_dampener * dist)

                total_repulsion += rep

        return attractive_defect + total_repulsion + magic_bonus

    defect_standard = calculate_topology_defect(use_hypervalency=False)
    defect_hypervalent = calculate_topology_defect(use_hypervalency=True)
    total_defect = min(defect_standard, defect_hypervalent)

    for i, e in enumerate(f for f in res.factors if f.identifier == 2):
        e.color = f"mol_orb_{i // 2}" 
        e.spin = 0.5 if i % 2 == 0 else -0.5 

    sig = complex(1, 0)
    for f in res.factors:
        val = float(f.identifier) if not f.is_anti else 1.0 / float(f.identifier)
        sig *= (val * mp.exp(1j * mp.pi * f.spin))
    res.signature = sig
    res.mass += total_defect
    res.extensions.append(ExtensionClass(name, binding_energy=total_defect, virtual_nodes=res.factors))
    return res

class CategoricalChemistryEngine:
    """Convenience wrapper for backwards compatibility."""
    def atomic_engine(self, symbol: str, tag: str = None) -> GrothendieckObject:
        return get_atom_by_symbol(symbol, tag)

    def molecular_bind(self, atoms_list: List[GrothendieckObject], name: str) -> GrothendieckObject:
        return molecular_bind(atoms_list, name)
