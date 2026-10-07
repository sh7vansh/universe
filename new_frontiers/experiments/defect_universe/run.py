"""Exact exploration of defect-as-mass, with explicitly added quantum dynamics.

Run with Python 3.10+: python3 -m new_frontiers.experiments.defect_universe.run
Optional artifacts: --output-dir /tmp/defect-universe

No particle data, physical units, floating-point simulation, or dependencies.
Floats are used only for displaying exact probabilities in the HTML explorer.
This is an experiment, not an implementation of established gravitational laws.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from itertools import permutations, product
import json
from pathlib import Path

from .._shared.exact import QComplex, ZERO, ONE, dagger, apply, check_unitary, diagonal
from .._shared.k4_graph import EDGES, STATES, mass, defect


# The phase law is an EXTRA assumption. This rational unit phase avoids a
# forced finite period such as i**mass; no measured coupling is fitted here.
PHASE = QComplex(F(3, 5), F(4, 5))
# Exactly balanced and unitary, despite all entries being Gaussian rationals.
P, Q = QComplex(F(1, 2), F(1, 2)), QComplex(F(1, 2), F(-1, 2))
BEAM = ((P, Q), (Q, P))


def verify_lattice():
    for a, b in product(STATES, repeat=2):
        assert defect(a, b) >= 0
        assert defect(a, b) == mass(a | b) + mass(a & b) - mass(a) - mass(b)
        if a & b == a:
            assert defect(a, b) == 0

    histories = 0
    for target in STATES:
        present = [i for i in range(6) if target & (1 << i)]
        for order in permutations(present):
            current, action, phase = 0, 0, ONE
            for index in order:
                singleton = 1 << index
                increment = defect(current, singleton)
                assert increment == mass(current | singleton) - mass(current)
                current |= singleton
                action += increment
                phase *= PHASE ** increment
            assert current == target
            assert action == mass(target)
            assert phase == PHASE ** mass(target)
            histories += 1

    # Invariance under every vertex relabelling of K4.
    for perm in permutations(range(4)):
        edge_map = [EDGES.index(tuple(sorted((perm[a], perm[b])))) for a, b in EDGES]
        for mask in STATES:
            mapped = sum(1 << edge_map[i] for i in range(6) if mask & (1 << i))
            assert mass(mapped) == mass(mask)

    circuits = [mask for mask in STATES if mass(mask) > 0 and
                all(mass(mask ^ (1 << i)) == 0 for i in range(6) if mask & (1 << i))]
    assert len(circuits) == 7
    assert all(mass(mask) == 1 for mask in circuits)
    return {"configurations": 64, "pairs_checked": 4096,
            "construction_histories_checked": histories,
            "mass_histogram": dict(sorted(Counter(mass(s) for s in STATES).items())),
            "minimal_circuits": len(circuits), "every_circuit_mass": 1}


def interferometer(source_mass):
    """Split, give arm 1 a defect-dependent phase, recombine with inverse splitter."""
    arms = apply(BEAM, (ONE, ZERO))
    output = apply(dagger(BEAM), (arms[0], PHASE ** source_mass * arms[1]))
    probabilities = tuple(z.norm2() for z in output)
    assert sum(probabilities) == 1
    assert probabilities[1] == (1 - (PHASE ** source_mass).real) / 2
    return {"mass": source_mass, "phase": str(PHASE ** source_mass),
            "probabilities": [str(p) for p in probabilities]}


def associahedron_rank_obstruction():
    """The usual face rank of K4 (a pentagon) is NOT submodular.

    Include the empty face to obtain a lattice. Two nonadjacent vertices have
    meet empty and join the whole polygon: defect = 1+1-3-0 = -1.
    """
    vertices = [1 << i for i in range(5)]
    edges = [(1 << i) | (1 << ((i + 1) % 5)) for i in range(5)]
    faces = [0, *vertices, *edges, 31]
    rank = {0: 0, **dict.fromkeys(vertices, 1), **dict.fromkeys(edges, 2), 31: 3}
    negative = []
    for a, b in product(faces, repeat=2):
        join = min((f for f in faces if (a | b) & f == a | b), key=int.bit_count)
        value = rank[a] + rank[b] - rank[join] - rank[a & b]
        if value < 0:
            negative.append(value)
    assert len(negative) == 10 and set(negative) == {-1}
    return {"face_pairs_checked": 144, "negative_defect_pairs": 10,
            "nonadjacent_vertex_defect": -1,
            "conclusion": "Ordinary associahedral face rank cannot be used as SubmodularRank."}


def quantum_source():
    """A coherent superposition of a forest and a one-cycle source.

    Source and probe each start in BEAM|0>. The source is deliberately static:
    its occupation probabilities are conserved by the controlled phase gate.
    Nonzero coefficient determinant certifies source/probe entanglement.
    """
    split = apply(BEAM, (ONE, ZERO))
    initial = tuple(a * b for a in split for b in split)
    gate = diagonal((ONE, ONE, ONE, PHASE))
    check_unitary(gate)
    state = apply(gate, initial)
    assert sum(z.norm2() for z in state) == 1
    determinant = state[0] * state[3] - state[1] * state[2]
    assert determinant.norm2() > 0
    purity = 1 - 2 * determinant.norm2()
    assert purity == F(9, 10)
    assert sum(state[i].norm2() for i in (0, 1)) == F(1, 2)
    return {"determinant_norm_squared": str(determinant.norm2()),
            "reduced_purity": str(purity), "source_populations": ["1/2", "1/2"],
            "caveat": "Source persistence is imposed by the block-diagonal gate."}


def bound_mode():
    """Exact recurrence certificate for a normalizable infinite-line eigenmode.

    For the one-cycle field at x=0:
      lambda = (9+2i)/sqrt(85), rho = 5/sqrt(85), A = (7+6i)/sqrt(85).
      psi(0) = C*(1,1), psi(x) = C*(A*rho**(x-1), rho**x) for x>=1.
      psi(-x) swaps the two components; C**2=3/17.

    The identities below verify the boundary and bulk recurrences after
    clearing sqrt(85). The geometric series proves infinite norm exactly 1.
    This is an analytic mode of the ADDED walk, not a self-generated source.
    """
    eigen_num, right_num = QComplex(9, 2), QComplex(7, 6)
    assert eigen_num.norm2() == right_num.norm2() == 85
    # lambda*A = PHASE: the outgoing edge from the defect.
    assert eigen_num * right_num == 85 * PHASE
    # lambda = b*A + a*rho: the incoming edge at the origin.
    assert Q * right_num + 5 * P == eigen_num
    # lambda*rho*A = a*A + b*rho: every right-moving bulk recurrence.
    assert (F(1, 17) * eigen_num) * right_num == P * right_num + 5 * Q
    # The left-moving recurrence follows by multiplying the incoming one by rho;
    # reflection swaps the components, proving the equations for x<0 as well.
    ratio, coefficient_squared = F(5, 17), F(3, 17)
    assert 0 < ratio < 1
    assert 2 * coefficient_squared + 2 * coefficient_squared * (1 + ratio) / (1 - ratio) == 1
    # Staggering by (-1)**x gives eigenvalue -lambda, with zero overlap.
    assert 2 * coefficient_squared - 2 * coefficient_squared * (1 + ratio) / (1 + ratio) == 0
    # Vacuum specialization has |rho|^2=1 in this ansatz, hence no normalization.
    assert P.norm2() / (ONE - Q).norm2() == 1
    return {"eigenvalues": ["(9+2i)/sqrt(85)", "-(9+2i)/sqrt(85)"],
            "tail_probability_ratio": str(ratio),
            "normalizing_coefficient_squared": str(coefficient_squared),
            "probability_at_origin": str(2 * coefficient_squared),
            "initial_probe_projection_on_two_modes": str(2 * coefficient_squared),
            "status": "Exact analytic eigenmodes of the infinite discrete line with a fixed one-cycle source."}


def walk_step(state, field, reverse=False):
    """U = conditional_shift * BEAM * local_phase on a discrete line.

    Dictionary keys are (position, direction). The underlying infinite-line
    operator is unitary; a finite number of steps has an exactly finite causal
    cone. No truncation, absorbing boundary, or wraparound is used.
    """
    if reverse:
        unshifted = {(x - (1 if direction == 0 else -1), direction): value
                     for (x, direction), value in state.items()}
        result = {}
        for x in {x for x, _ in unshifted}:
            value = apply(dagger(BEAM), tuple(unshifted.get((x, d), ZERO) for d in (0, 1)))
            for direction in (0, 1):
                result[x, direction] = PHASE ** -field(x) * value[direction]
    else:
        result = {}
        for x in {x for x, _ in state}:
            value = apply(BEAM, tuple(PHASE ** field(x) * state.get((x, d), ZERO)
                                      for d in (0, 1)))
            result[x + 1, 0] = value[0]
            result[x - 1, 1] = value[1]
    return {key: value for key, value in result.items() if value != ZERO}


def snapshot(state, step):
    positions = sorted({x for x, _ in state})
    probabilities = {x: sum(state.get((x, d), ZERO).norm2() for d in (0, 1)) for x in positions}
    assert sum(probabilities.values()) == 1
    return {"step": step, "norm": "1",
            "near_source_exact": str(sum(p for x, p in probabilities.items() if abs(x) <= 4)),
            "positions": [{"x": x, "p": float(p), "exact": str(p)} for x, p in probabilities.items()]}


def walk_experiment(steps):
    # These masses are computed from graph configurations, not particle tables.
    triangle = sum(1 << EDGES.index(edge) for edge in ((0, 1), (0, 2), (1, 2)))
    double_cycle = 31
    assert mass(triangle) == 1 and mass(double_cycle) == 2
    fields = {
        "vacuum": lambda x: 0,
        "one_cycle": lambda x: mass(triangle) if x == 0 else 0,
        "two_cycles": lambda x: mass(double_cycle) if x == 0 else 0,
        "uniform_control": lambda x: mass(triangle),
    }
    initial = {(0, 0): ONE}
    runs = {}
    for name, field in fields.items():
        state = initial
        history = [snapshot(state, 0)]
        for step in range(1, steps + 1):
            state = walk_step(state, field)
            history.append(snapshot(state, step))
        restored = state
        for _ in range(steps):
            restored = walk_step(restored, field, reverse=True)
        assert restored == initial
        runs[name] = history
    # A spatially uniform field adds only a global phase, so it cannot reroute
    # probabilities. This distinguishes an actual relative-phase effect.
    assert runs["uniform_control"] == runs["vacuum"]
    assert runs["one_cycle"][-1]["positions"] != runs["vacuum"][-1]["positions"]
    return runs


def explorer_html(results):
    payload = json.dumps(results)
    return r"""<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Defect universe — exact exploration</title>
<style>
body{max-width:1100px;margin:40px auto;padding:0 22px;background:#f8f7f3;color:#262622;font:16px/1.6 system-ui}
h1{font-size:32px;line-height:1.2}p{max-width:85ch}button,select,input{font:inherit}select{padding:6px}
.note{border-left:3px solid #847d5c;padding-left:15px}.controls{display:flex;align-items:center;gap:16px;flex-wrap:wrap}
#bars{display:flex;height:240px;align-items:end;gap:2px;border-bottom:1px solid #888;margin-top:26px}
.bar{background:#597765;min-width:2px;flex:1;border:0;padding:0;cursor:pointer}
.bar:hover{background:#243f32}.axis{display:flex;justify-content:space-between;color:#666;font-size:13px}
pre{white-space:pre-wrap;overflow-wrap:anywhere;background:#eeeae0;padding:15px}table{border-collapse:collapse}
td,th{text-align:left;border-bottom:1px solid #ccc;padding:8px 20px 8px 0}small{color:#666}
</style>
<h1>Can structural defect affect quantum travel?</h1>
<p>Mass is the cycle count of a finite graph configuration. A passing probe acquires the exact phase
ζ<sup>mass</sup>, with ζ = (3 + 4i)/5. A balanced quantum walk splits and recombines histories.</p>
<p class="note"><b>Result:</b> the added phase coupling changes interference while preserving probability;
an exact localized eigenmode also exists. The source graph is held fixed.
This does not demonstrate a self-generated particle, attraction,
time dilation, or a law of gravity. All simulation arithmetic is exact; bar heights are decimal display values.</p>
<div class="controls"><label>Environment <select id="scenario">
<option value="vacuum">No source</option><option value="one_cycle" selected>One-cycle source at x = 0</option>
<option value="two_cycles">Two-cycle source at x = 0</option>
<option value="uniform_control">Uniform phase control (same probabilities as no source)</option>
</select></label><label>Step <input id="step" type="range" min="0" value="16"><output id="stepValue"></output></label></div>
<p id="summary"></p><div id="bars" aria-label="Position probability distribution"></div>
<div class="axis"><span id="left"></span><span>position 0 · fixed source</span><span id="right"></span></div>
<small>Vertical scale: 100% is the full height. Select a bar to inspect the exact fraction.</small>
<pre id="detail">Select a probability bar.</pre>
<h2>Interferometer: exact output probabilities</h2><table><thead><tr><th>Source mass</th><th>Port 0</th><th>Port 1</th></tr></thead><tbody id="ports"></tbody></table>
<p>Increasing the integer mass does not give a monotone detector response. Interference depends on phase.
A common phase on both arms changes no probabilities. Mass 4 illustrates the phase law beyond the
single K4 source catalogue, whose maximum cycle count is 3.</p>
<h2>An exact bound mode, beyond the finite-time simulation</h2>
<p>For the one-cycle source, eigenvalues are ±(9 + 2i)/√85. A normalized eigenstate has
probability 6/17 at the origin; its tail probability falls by a factor 5/17 at each successive site.
Evolution changes only its global phase. A probe initially at the origin in direction 0 has total
squared overlap 6/17 with these two orthogonal modes.</p>
<p>The mode has an infinite, summable tail on the discrete line. The simulation above has finite support
at each finite time and uses no spatial truncation. The mode is a property of the chosen unitary coupling,
not a theorem of submodularity alone.</p>
<h2>What follows from the lattice, and what was added?</h2>
<p><b>Derived:</b> submodular graphic rank; nonnegative integer cycle mass;
defect as excess mass under joining; construction action telescopes to the endpoint mass difference.</p>
<p><b>Added:</b> a spatial line, a clock step, two probe directions, a unitary splitter,
the phase ζ, and coupling to the mass already present at a site. The source is static by design.</p>
<p><b>Quantum source check:</b> coherently controlling a probe phase by zero-cycle and one-cycle source
states yields reduced purity 9/10. The full state stays pure and normalized; source and probe become entangled.</p>
<script id="data" type="application/json">PAYLOAD</script>
<script>
const data=JSON.parse(document.getElementById('data').textContent);
const scenario=document.getElementById('scenario'), slider=document.getElementById('step');
slider.max=data.steps;slider.value=Math.min(16,data.steps);
const extent=data.steps;document.getElementById('left').textContent=-extent;
document.getElementById('right').textContent=extent;
function draw(){
 const record=data.walks[scenario.value][Number(slider.value)];
 document.getElementById('stepValue').textContent=record.step;
 const near=record.near_source_exact.split('/').map(Number);
 document.getElementById('summary').textContent='Total probability: exactly 1. Probability within |x| ≤ 4: '+
  (100*near[0]/(near[1]||1)).toFixed(2)+'%. This finite-time concentration is not proof of a bound state.';
 const values=new Map(record.positions.map(p=>[p.x,p])), bars=document.getElementById('bars');bars.replaceChildren();
 for(let x=-extent;x<=extent;x++){
  const p=values.get(x)||{x,p:0,exact:'0'}, bar=document.createElement('button');
  bar.className='bar';bar.style.height=Math.max(.5,240*p.p)+'px';
  bar.title='x = '+x+', P = '+p.exact;bar.setAttribute('aria-label',bar.title);
  bar.onclick=()=>document.getElementById('detail').textContent='Step '+record.step+', position '+x+'\nP = '+p.exact;
  bars.appendChild(bar);
 }
 document.getElementById('detail').textContent='Select a probability bar.';
}
for(const row of data.interferometer){const tr=document.createElement('tr');
 for(const value of [row.mass,...row.probabilities]){const td=document.createElement('td');td.textContent=value;tr.appendChild(td);}
 document.getElementById('ports').appendChild(tr);}
scenario.onchange=draw;slider.oninput=draw;draw();
</script></html>""".replace("PAYLOAD", payload)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--with-explorer", action="store_true",
                        help="also generate the optional HTML explorer in --output-dir")
    parser.add_argument("--steps", type=int, default=32)
    args = parser.parse_args()
    if args.with_explorer and not args.output_dir:
        parser.error("--with-explorer requires --output-dir")
    if not 4 <= args.steps <= 64:
        parser.error("choose 4–64 steps for this finite experiment")
    assert PHASE.norm2() == 1
    check_unitary(BEAM)
    results = {"steps": args.steps, "lattice": verify_lattice(),
               "associahedron_rank_obstruction": associahedron_rank_obstruction(),
               "interferometer": [interferometer(m) for m in range(5)],
               "quantum_source": quantum_source(), "bound_mode": bound_mode(),
               "walks": walk_experiment(args.steps)}
    print(json.dumps({key: value for key, value in results.items() if key != "walks"}, indent=2))
    for name, records in results["walks"].items():
        near = F(records[-1]["near_source_exact"])
        print(f"{name}: P(|x| <= 4) at t={args.steps}: {float(near):.6f}")
    print("All exact lattice, unitarity, normalization, reversal, and global-phase checks passed.")
    if args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        (args.output_dir / "results.json").write_text(json.dumps(results, indent=2) + "\n")
        if args.with_explorer:
            (args.output_dir / "explorer.html").write_text(explorer_html(results))
        print(f"Wrote results.json to {args.output_dir}")
        if args.with_explorer:
            print(f"Wrote optional explorer.html to {args.output_dir}")


if __name__ == "__main__":
    main()
