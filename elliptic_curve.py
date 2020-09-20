#! /usr/bin/python3

from gmpy2 import f_mod


class EllipticCurve(object):
    def check_point(self, X, Y):
        """"check if point belong to this curve 
			Y^2 == X^3 + A*X + B
        """
        return f_mod((Y * Y), self.P) == f_mod((X * X * X + self.A * X + self.B), self.P)

    def check_delta(self):
        """"check delta condidtion with definition, gcd(delta, n) = 1"""
        return f_mod((4 * (self.A * self.A * self.A) + 27 * (self.B * self.B)), self.P) != 0
    
    def __str__(self):
        return 'E.C.: [1, ' + str(int(self.A)) + ', ' + str(int(self.B)) + ']'

    def __init__(self, P, A, B):
        """elliptic curve such that delta = 4*A^3 + 27*B^2 in Z_P"""
        self.P = P
        self.A = A
        self.B = B
        if not self.check_delta():
            raise BaseException("delta is zero")
