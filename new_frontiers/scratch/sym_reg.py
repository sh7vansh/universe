# Data
# A, B primes:
data = [
    (3, 3, 10.0),
    (9, 5, 919.1),
    (5, 5, 10.0),
    (25, 3, 917.9),
    (45, 75, -2.2),
    (3375, 3375, -23.6),
    (11390625, 2, -0.0000136),
    (22781250, 2, -0.0000136)
]

for pa, pb, E in data:
    diff = 4 * abs(pa - pb)
    print(f"{pa:8} {pb:8} | E={E:12.6f} | pA+pB={pa+pb:8} | 4|pA-pB|={diff:8} | pA*pB={pa*pb:10} | pA/pB={pa/pb:8.3f}")
