import itertools

def search():
    target_mass = 3728.4
    bare_mass = 41.4 # without electrons, or 42.422 with
    target_bind = 3728.422 - 42.422 # 3686.0
    
    # Interactions: 2*(3,3), 2*(9,5), 2*(5,5), 2*(25,3), 2*(45,75), 1*(3375,3375)
    # ignoring EM for the moment
    interactions = [
        (3,3,2), (9,5,2), (5,5,2), (25,3,2), (45,75,2), (3375,3375,1)
    ]
    
    # Let E = c1 * (pa+pb) + c2 * |pa-pb| + c3 * |pa-pb|^2 + c4 * 1
    # Actually, we can just print the properties to see if there's an obvious linear combination
    sum_pa_pb = sum((pa+pb)*count for pa, pb, count in interactions)
    sum_diff = sum(abs(pa-pb)*count for pa, pb, count in interactions)
    sum_diff2 = sum((pa-pb)**2*count for pa, pb, count in interactions)
    sum_count = sum(count for pa, pb, count in interactions)
    
    print("Sum pa+pb:", sum_pa_pb)
    print("Sum |pa-pb|:", sum_diff)
    print("Sum |pa-pb|^2:", sum_diff2)
    print("Count:", sum_count)

search()
