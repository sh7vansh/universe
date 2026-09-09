import math
import numpy as np
from sympy import primerange
from itertools import product

class CombOrbitEngine:
    def __init__(self, primes, max_len=4):
        self.primes = list(primes)
        self.max_len = max_len
        
    def is_primitive(self, w):
        """
        Check if word w is primitive (not equal to v^m for m > 1).
        """
        n = len(w)
        for m in range(2, n + 1):
            if n % m == 0:
                l = n // m
                v = w[:l]
                if v * m == w:
                    return False
        return True
        
    def get_necklace(self, w):
        """Return the lexicographically smallest cyclic permutation (necklace)."""
        return min(w[i:] + w[:i] for i in range(len(w)))

    def generate_primitive_words(self):
        """
        Yields primitive necklaces (one representative per cyclic orbit) of length 1 to max_len.
        """
        seen = set()
        for length in range(1, self.max_len + 1):
            for w in product(self.primes, repeat=length):
                if self.is_primitive(w):
                    neck = self.get_necklace(w)
                    if neck not in seen:
                        seen.add(neck)
                        yield neck
                        
    def weight(self, w, s_val):
        """
        A(w) = \prod p_i^{-s}
        """
        wt = 1.0
        for p in w:
            wt *= p ** (-s_val)
        return wt

def run_layer13(s_val=1.5, max_len=6, p_max=10):
    primes = list(primerange(2, p_max))
    engine = CombOrbitEngine(primes, max_len=max_len)
    
    print(f"=== Layer 13: Combinatorial Orbit Engine (s={s_val}) ===")
    print(f"Alphabet: Primes <= {p_max}: {primes}")
    
    # 1. Euler Zeta (Only length-1 primitive orbits w = (p))
    euler_sum = 0.0
    for p in primes:
        # Sum over repetitions m
        # sum_{m=1}^M A((p))^m / m
        # We can sum up to a large M, e.g. 50, to get convergence
        m_sum = 0.0
        for m in range(1, 100):
            m_sum += (p ** (-s_val))**m / m
        euler_sum += m_sum
        
    # Theoretical Euler sum
    theoretical_euler = -sum(np.log(1 - p**(-s_val)) for p in primes)
    
    print("\n--- 1. Euler Zeta (1-letter orbits) ---")
    print(f"Constructed from repetitions (m>=1) : {euler_sum:.8f}")
    print(f"Theoretical -sum log(1 - p^-s)      : {theoretical_euler:.8f}")
    print(f"Match? {'Yes' if abs(euler_sum - theoretical_euler) < 1e-7 else 'No'}")
    
    # 2. Word Zeta (All primitive words)
    print(f"\n--- 2. Word Zeta (All primitive words up to length {max_len}) ---")
    word_sum = 0.0
    word_count = 0
    for w in engine.generate_primitive_words():
        wt = engine.weight(w, s_val)
        # Sum over repetitions m
        m_sum = 0.0
        for m in range(1, 100):
            m_sum += (wt ** m) / m
        word_sum += m_sum
        word_count += 1
        
    # Theoretical Word Zeta
    # Z_word = -log(1 - sum_p p^{-s})
    sum_p = sum(p**(-s_val) for p in primes)
    theoretical_word = -np.log(1 - sum_p)
    
    print(f"Analyzed {word_count} primitive words.")
    print(f"Constructed from word orbits        : {word_sum:.8f} (truncated at L={max_len})")
    print(f"Theoretical -log(1 - sum p^-s)      : {theoretical_word:.8f}")
    
    # Let's show convergence of the word sum as length increases
    print("\nWord Zeta Convergence by Max Word Length:")
    for L in range(1, max_len + 1):
        l_sum = 0.0
        for w in product(primes, repeat=L):
            if engine.is_primitive(w):
                wt = engine.weight(w, s_val)
                for m in range(1, max_len // len(w) + 2): # Just a few repetitions for illustration
                    pass # We will just sum directly up to M=50 for each
                
        # Better to just run the engine up to L
        partial_sum = 0.0
        for w in CombOrbitEngine(primes, max_len=L).generate_primitive_words():
            wt = engine.weight(w, s_val)
            for m in range(1, 100):
                partial_sum += (wt ** m) / m
        print(f"  L={L}: sum = {partial_sum:.8f}")
        
    print("\nCONCLUSION:")
    print("The 1-letter primitive orbits perfectly reproduce the Euler Zeta product.")
    print("Allowing composite primitive words like (p, q) generates a completely different object (the Word Zeta).")
    print("To model the Riemann Zeta function organically, the topological/algebraic rules of the operator MUST restrict the primitive orbits exclusively to single primes. Cross-prime sequences cannot be allowed to form new primitive loops.")

if __name__ == "__main__":
    run_layer13(s_val=1.5, max_len=6, p_max=7)
