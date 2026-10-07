"""The exact rational direction coin used by both Dirac experiments."""

from .exact import QComplex


def rational_coin(mass_value, epsilon):
    a = epsilon*mass_value/2
    c, b = (1-a*a)/(1+a*a), QComplex(0, -2*a/(1+a*a))
    return ((QComplex(c), b), (b, QComplex(c)))
