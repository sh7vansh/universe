def E(pA, pB):
    return 4 * abs(pA - pB)

# Quarks
u = 2.2
d = 4.7

# U + U (3, 3)
p_uu = 9
m_uu = u + u + E(3, 3) # 4.4 + 0 = 4.4

# UU + D (9, 5)
p_p = 45
m_p = m_uu + d + E(9, 5) # 4.4 + 4.7 + 4*4 = 9.1 + 16 = 25.1

# D + D (5, 5)
p_dd = 25
m_dd = d + d + E(5, 5) # 9.4 + 0 = 9.4

# DD + U (25, 3)
p_n = 75
m_n = m_dd + u + E(25, 3) # 9.4 + 2.2 + 4*22 = 11.6 + 88 = 99.6

# P + N (45, 75)
p_d = 3375
m_d = m_p + m_n + E(45, 75) # 25.1 + 99.6 + 4*30 = 124.7 + 120 = 244.7

# Alpha (3375, 3375)
p_alpha = 11390625
m_alpha = m_d + m_d + E(3375, 3375) # 244.7 + 244.7 + 0 = 489.4

print("Mass P:", m_p)
print("Mass N:", m_n)
print("Mass D:", m_d)
print("Mass Alpha:", m_alpha)
