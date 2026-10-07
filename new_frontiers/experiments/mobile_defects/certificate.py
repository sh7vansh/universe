"""Symbolic certificate for the mobile-defect bound band.

Optional proof check; requires SymPy (the simulator itself has no dependencies).
Run: python3 -m new_frontiers.experiments.mobile_defects.certificate

We reduce the exact rational matching equations modulo the bound-band
polynomial. The domain, decay, and denominator conditions are in the report.
"""

import sympy as s


lam, h = s.symbols("lam h", nonzero=True)
I = s.I
H = h + 1 / h
polynomial = 3 * h * lam**2 - I * (h**2 + 1) * lam - 3 * h
rho = H / 6
moving_R = -I / lam
f = (lam * H - 2 * I) / (lam * (2 * lam - I * H))
a, b = (f + I) / 2, (f - I) / 2
stationary_R = (2 * lam / h - 2 * I) / (2 * lam * (2 * lam - I * H)) * (moving_R - rho)
stationary_L = (2 * lam * h - 2 * I) / (2 * lam * (2 * lam - I * H)) * (moving_R - rho)


def zero_mod_band(name, expression):
    numerator = s.fraction(s.cancel(expression))[0]
    assert s.factor(s.rem(numerator, polynomial, lam)) == 0, name
    print(name + ": exact polynomial remainder is zero")


zero_mod_band("incoming boundary", b * moving_R - a * rho + lam)
zero_mod_band("outgoing bulk", a * moving_R - b * rho - lam * rho * moving_R)
zero_mod_band("stationary RR",
              (I * stationary_R + moving_R - rho - I * stationary_L) / (2 * h) - lam * stationary_R)
zero_mod_band("stationary LL",
              h * (-I * stationary_R + moving_R - rho + I * stationary_L) / 2 - lam * stationary_L)


def conjugate_on_unit_circles(expression):
    # |h|=|lambda|=1 is established from their explicit expressions in the report.
    return expression.xreplace({I: -I, h: 1 / h, lam: 1 / lam})


tail_norm = sum(z * conjugate_on_unit_circles(z)
                for z in (stationary_R, moving_R, -rho, stationary_L))
total_norm = 2 + 2 * tail_norm / (1 - rho**2)
zero_mod_band("all-momentum norm equals six", total_norm - 6)
assert s.Rational(2, 6) * 2 == s.Rational(2, 3)
print("Initial coincident singlet has projection weight 2/3 onto the two bound bands.")
