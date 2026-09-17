def test_max():
    total_mass = 41.4 # bare
    def E(pa, pb):
        return max(pa, pb)
    
    # bindings
    total_mass += 2*E(3,3)
    total_mass += 2*E(9,5)
    total_mass += 2*E(5,5)
    total_mass += 2*E(25,3)
    total_mass += 2*E(45,75)
    total_mass += E(3375,3375)
    return total_mass

print("Mass with E = max(pa, pb):", test_max())

def test_min():
    total_mass = 41.4
    def E(pa, pb):
        return min(pa, pb)
    total_mass += 2*E(3,3)
    total_mass += 2*E(9,5)
    total_mass += 2*E(5,5)
    total_mass += 2*E(25,3)
    total_mass += 2*E(45,75)
    total_mass += E(3375,3375)
    return total_mass

print("Mass with E = min(pa, pb):", test_min())
