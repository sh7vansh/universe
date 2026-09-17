import sys
import os

def gauss_jordan(A, y):
    n = len(y)
    M = [row[:] + [y[i]] for i, row in enumerate(A)]
    for i in range(n):
        # Find pivot
        max_el = abs(M[i][i])
        max_row = i
        for k in range(i+1, n):
            if abs(M[k][i]) > max_el:
                max_el = abs(M[k][i])
                max_row = k
        M[i], M[max_row] = M[max_row], M[i]
        
        # Make pivot 1
        pivot = M[i][i]
        if pivot == 0: continue
        for j in range(i, n+1):
            M[i][j] /= pivot
            
        # Eliminate other rows
        for k in range(n):
            if k != i:
                factor = M[k][i]
                for j in range(i, n+1):
                    M[k][j] -= factor * M[i][j]
    return [row[n] for row in M]

# x values:
# 1: U+U = 9
# 2: UU+D = 45
# 3: D+D = 25
# 4: DD+U = 75
# 5: P+N = 3375
# 6: D+D (nucleus) = 11390625
# 7: Alpha+E = 22781250
# 8: AlphaE+E = 45562500

X_vals = [9, 45, 25, 75, 3375, 11390625, 22781250, 45562500]
Y_vals = [10.0, 919.1, 10.0, 917.9, -2.2, -23.6, -0.0000136, -0.0000136]

# Build Vandermonde matrix
A = []
for x in X_vals:
    row = [x**i for i in range(8)]
    A.append(row)

coeffs = gauss_jordan(A, Y_vals)
print("Polynomial coefficients:", coeffs)

# Test polynomial
for x, y in zip(X_vals, Y_vals):
    calc = sum(c * (x**i) for i, c in enumerate(coeffs))
    print(f"x: {x}, Target: {y}, Calc: {calc}")

