import math

u = 3
d = 5

def norm(m):
    return math.sqrt(sum(abs(c)**2 for r in m for c in r))

Mu = [[complex(u, 0), complex(0, 1)], [complex(0, -1), complex(-u, 0)]]
Md = [[complex(d, 0), complex(0, 1)], [complex(0, -1), complex(-d, 0)]]

def mat_mul(m1, m2):
    return [[sum(a * b for a, b in zip(r, c)) for c in zip(*m2)] for r in m1]

Muu = mat_mul(Mu, Mu)
Mudd = mat_mul(Muu, Md)

print("||M_u|| =", norm(Mu))
print("||M_d|| =", norm(Md))
print("||M_uu|| =", norm(Muu))
print("||M_udd|| =", norm(Mudd))

# What is 132.738?
print("\nIs it related to pi?")
print("132.738 * pi =", 132.738 * math.pi)

print("\nIs it related to prime identifier sum?")
# proton primes = 3, 3, 5. Sum = 11. 11 * 12 = 132
print("11 * something?")

# What about the fine structure constant?
alpha = 1/137.036
print("alpha^-1 =", 1/alpha)

# Vector space dimension of 2x2 complex matrices is 8.
# Maybe kappa = something with 8?
print("7 * kappa = 929.166")

# What if binding energy is exactly the product of the magnitudes?
print("Magnitude of Proton signature = 45")
print("Magnitude of Neutron signature = 75")
# 45 * 20.6 = 929?
# 75 * 12.3 = 929?

# Look at the exact sequence: 0 -> A -> C -> B -> 0
# The Ext^1 dimension?
# Maybe the formula is E_binding = norm(M_C)^2 / something?
print("||M_udd||^2 =", norm(Mudd)**2)
print("||M_udd||^2 / (something) =", norm(Mudd)**2 / 929.166)

M_neutron = mat_mul(Mu, mat_mul(Md, Md))
print("||M_neutron||^2 =", norm(M_neutron)**2)
print("||M_neutron||^2 / (something) =", norm(M_neutron)**2 / 929.166)

# wait! norm(M_udd)^2 = 5200.
# 5200 / 929.166 = 5.596.

# norm(M_u)^2 = 20
# norm(M_d)^2 = 52
# for u, u, d: 20 + 20 + 52 = 92? No.
