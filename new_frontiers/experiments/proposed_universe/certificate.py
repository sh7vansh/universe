"""Symbolic dispersion and curvature checks for new_frontiers/experiments/proposed_universe/README.md.

Requires SymPy. Fourier momentum labels translations of a discrete lattice;
its use here does not posit continuous physical space or time.
"""

import sympy as s

h, lam = s.symbols("h lam", nonzero=True)
k = s.symbols("k", real=True)
B = s.Matrix([[1+s.I, 1-s.I], [1-s.I, 1+s.I]])/2
assert s.simplify(B.H * B - s.eye(2)) == s.zeros(2)
assert s.simplify(B**2 - s.Matrix([[0, 1], [1, 0]])) == s.zeros(2)
U = s.diag(1/h, h) * B
polynomial = s.expand((lam*s.eye(2) - U).det())
expected = lam**2 - (1+s.I)*(h+1/h)*lam/2 + s.I
assert s.simplify(polynomial-expected) == 0
print("Single-object characteristic polynomial: exact identity checked.")

# lambda = exp(i*pi/4) * exp(-i*omega); cos(omega)=cos(k)/sqrt(2).
# Select the local branch E=omega-pi/4 with U eigenvalue exp(-iE).
free_energy = s.acos(s.cos(k)/s.sqrt(2)) - s.pi/4
free_curvature = s.simplify(s.diff(free_energy, k, 2).subs(k, 0))
assert free_curvature == 1
print("Single-object low-momentum curvature:", free_curvature)

# The '+' bound band is lambda=exp(i*asin(cos(K)/3)).
# A local quasienergy is E=-asin(cos(K)/3); additive constants do not affect curvature.
bound_energy = -s.asin(s.cos(k)/3)
bound_curvature = s.simplify(s.diff(bound_energy, k, 2).subs(k, 0))
assert bound_curvature == s.sqrt(2)/4
assert s.simplify(1/bound_curvature) == 2*s.sqrt(2)
print("Bound-pair low-momentum curvature:", bound_curvature)
print("Bound-pair curvature mass:", s.simplify(1/bound_curvature))

# Both curvatures define only a dimensionless small-momentum kinetic proxy.
# They do not establish an invariant relativistic rest mass.
assert s.simplify(s.diff(free_energy + s.pi, k, 2) - s.diff(free_energy, k, 2)) == 0
print("Changing an intrinsic parity phase shifts quasienergy but leaves curvature unchanged.")

# SEPARATE clock-length postulate: W sends channel q to q+1 and applies U
# only at wraparound. Its spectrum obeys lambda**M in spectrum(U).
for count in range(1, 5):
    W = s.zeros(2*count)
    for clock in range(count):
        out_clock = (clock+1) % count
        block = U if out_clock == 0 else s.eye(2)
        for i in range(2):
            for j in range(2):
                W[2*out_clock+i, 2*clock+j] = block[i, j]
    expected_clock = expected.subs(lam, lam**count)
    assert s.simplify((lam*s.eye(2*count)-W).det()-expected_clock) == 0
    print("Clock characteristic polynomial checked, M =", count)

M = s.symbols("M", positive=True)
clock_curvature = s.simplify(s.diff(free_energy/M, k, 2).subs(k, 0))
assert clock_curvature == 1/M
assert s.simplify(M*clock_curvature) == 1
print("Conditional clock curvature mass = M; defect charge times curvature = 1.")
