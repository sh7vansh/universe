"""Exact complex arithmetic and matrix helpers shared by the experiments.

QComplex uses Gaussian rationals. The tuple helpers times/plus/conjugate
operate on the Gaussian integer numerators used by the moving-object walks.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product


@dataclass(frozen=True)
class QComplex:
    """A Gaussian rational: both components are exact fractions."""

    real: F = F(0)
    imag: F = F(0)

    def __post_init__(self):
        object.__setattr__(self, "real", F(self.real))
        object.__setattr__(self, "imag", F(self.imag))

    def __add__(self, other):
        other = as_q(other)
        return QComplex(self.real + other.real, self.imag + other.imag)

    __radd__ = __add__

    def __neg__(self):
        return QComplex(-self.real, -self.imag)

    def __sub__(self, other):
        return self + -as_q(other)

    def __mul__(self, other):
        other = as_q(other)
        return QComplex(self.real * other.real - self.imag * other.imag,
                        self.real * other.imag + self.imag * other.real)

    __rmul__ = __mul__

    def conjugate(self):
        return QComplex(self.real, -self.imag)

    def norm2(self):
        return self.real**2 + self.imag**2

    def __pow__(self, exponent: int):
        if exponent < 0:
            assert self.norm2() == 1
            return self.conjugate() ** -exponent
        result, base = ONE, self
        while exponent:
            if exponent % 2:
                result = result * base
            base = base * base
            exponent //= 2
        return result

    def __str__(self):
        if self.imag == 0:
            return str(self.real)
        return f"({self.real} {'+' if self.imag >= 0 else '-'} {abs(self.imag)}i)"


def as_q(value):
    return value if isinstance(value, QComplex) else QComplex(value)


ZERO, ONE = QComplex(), QComplex(1)


def dagger(matrix):
    return tuple(tuple(z.conjugate() for z in col) for col in zip(*matrix))


def apply(matrix, vector):
    return tuple(sum((a * b for a, b in zip(row, vector)), ZERO) for row in matrix)


def check_unitary(matrix):
    for i, j in product(range(len(matrix)), repeat=2):
        inner = sum((row[i].conjugate() * row[j] for row in matrix), ZERO)
        assert inner == (ONE if i == j else ZERO)


def diagonal(values):
    return tuple(tuple(value if i == j else ZERO for j in range(len(values)))
                 for i, value in enumerate(values))


def times(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def conjugate(a):
    return a[0], -a[1]


def plus(a, b):
    return a[0] + b[0], a[1] + b[1]
