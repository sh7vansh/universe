import math
import cmath

def norm(m):
    return math.sqrt(sum(abs(c)**2 for r in m for c in r))

def det(m):
    return m[0][0]*m[1][1] - m[0][1]*m[1][0]

u_v = 3
d_v = 5

M_u = [[complex(u_v, 0), complex(0, 1)], [complex(0, -1), complex(-u_v, 0)]]
M_d = [[complex(d_v, 0), complex(0, 1)], [complex(0, -1), complex(-d_v, 0)]]

def mat_mul(m1, m2):
    return [[sum(a * b for a, b in zip(r, c)) for c in zip(*m2)] for r in m1]

M_uu = mat_mul(M_u, M_u)
M_proton = mat_mul(M_uu, M_d)

print("Proton norm:", norm(M_proton))
print("Proton det:", det(M_proton))

M_dd = mat_mul(M_d, M_d)
M_neutron = mat_mul(M_u, M_dd)

print("Neutron norm:", norm(M_neutron))
print("Neutron det:", det(M_neutron))

# What about the extension class norm?
# The commutator M_A M_B - M_B M_A was used for phase shift.
# Is the binding energy || M_A M_B || ?
# For proton: || M_uu M_d || = 72.11

# What if binding energy is sum of norms of factors?
# ||M_u|| = sqrt(10+10) = sqrt(20) ~ 4.47
# ||M_d|| = sqrt(26+26) = sqrt(52) ~ 7.21
# 2*4.47 + 7.21 = 16.15
