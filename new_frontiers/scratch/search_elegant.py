def test_elegant(c1, c2, c3):
    total_mass = 41.4 # bare
    def E(pa, pb):
        return c1*(pa+pb) + c2*abs(pa-pb) + c3*(pa*pb)
    
    # bindings
    total_mass += 2*E(3,3)
    total_mass += 2*E(9,5)
    total_mass += 2*E(5,5)
    total_mass += 2*E(25,3)
    total_mass += 2*E(45,75)
    total_mass += E(3375,3375)
    return total_mass

# Let's search for small integer/half-integer c1, c2, c3 that give ~3728.4
results = []
for c1 in [i/2 for i in range(-20, 20)]:
    for c2 in [i/2 for i in range(-20, 20)]:
        for c3 in [i/2 for i in range(-20, 20)]:
            m = test_elegant(c1, c2, c3)
            if abs(m - 3728.4) < 100:
                results.append((c1, c2, c3, m))

for r in results:
    print(r)
