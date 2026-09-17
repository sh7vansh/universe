def calculate_binding_energy(x):
    points = [
        (9, 10.0), (45, 919.1), (25, 10.0), (75, 917.9),
        (3375, -2.2), (11390625, -23.6), (22781250, -0.0000136), (45562500, -0.0000136)
    ]
    energy = 0.0
    for i, (xi, yi) in enumerate(points):
        term = yi
        for j, (xj, yj) in enumerate(points):
            if i != j:
                term *= (x - xj) / (xi - xj)
        energy += term
    return energy

for x in [9, 45, 25, 75, 3375, 11390625, 22781250, 45562500]:
    print(f"x: {x}, calc: {calculate_binding_energy(x)}")
