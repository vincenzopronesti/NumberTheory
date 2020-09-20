#! /usr/bin/python3

from elliptic_curve import EllipticCurve
from point import Point
from ideal import Ideal
from gmpy2 import invert
from gmpy2 import f_mod
from gmpy2 import mpz_random
from random import randint
from gmpy2 import random_state
from gmpy2 import gcd
from gmpy2 import fac

from gmpy2 import is_prime
from gmpy2 import next_prime
import math

class Lenstra(object):
    def create_curve(self):
        """
        :return: random Elliptic curve  and init Point
        """
        for i in range(10):
            try:
                self.X = self._generate_random_number()
                self.Y = self._generate_random_number()
                self.A = self._generate_random_number()
                self.B = f_mod((self.Y * self.Y - self.X * self.X * self.X - self.A * self.X), self.N)
                curve = EllipticCurve(self.N, self.A, self.B)
                
                self.point = Point(curve, self.X, self.Y)
                
                return curve
            except Exception as e:
                print("Error when curve is generated %s" % str(e))
                raise Exception

    def __init__(self, N, t=0):
        self.N = N
        self.t = t if t != 0 else None
        self.curve = self.create_curve()
        self.point = Point(self.curve, self.X, self.Y)

    def _generate_random_number(self):
        """
        :return: random number  
        """
        rstate = random_state()
        r = randint(40, 100)
        return f_mod(mpz_random(rstate, 2 << r).bit_set(0).bit_set(r), self.N)

    def is_not_point(self, p):
        return (isinstance(p, Ideal) == False and isinstance(p, Point) == False)

    def factorECM(self, b1, max_round):
        """ @param b1: smoothness bound
            @param max_round: maximum number of tries to execute the algorithm
        """
        # build k such that k is the product of all the primes (< b1) to the greatest power
        k = 1
        for i in range(2, b1):
            if is_prime(i):
                t = 1
                while t < b1:
                    k = k*i
                    t = t*i
        # define second smoothness bound
        b2 = int(math.floor(100 * b1)) ###
        # estimated number of primes <= b2
        #num_primes = math.floor(b2/math.log(b2))
        

        # pre-calculation for second phase
        q = next_prime(b1)
        delta_max = 2
        # create delta vector with the distance between primes in [b1, b2]
        delta_vector = []
        while True:
            q1 = next_prime(q + 1)
            if q1 > b2:
                break
            dd = q1 - q
            q = q1
            if dd > delta_max:
                delta_max = dd
            delta_vector.append(dd)
        
        print("greatest prime minor than b2 is: ", q1)

        for j in range(max_round):
            print('round: ', j)
            self.curve = self.create_curve() # generate new random curve c and point p
            e = self.curve
            p = self.point
            print('curve ' + str(e) + ' point ' + str(p))
            
            print("phase 1")
            p = self.mul(k, p)
            if self.is_not_point(p):
                if p is None:
                    raise BaseException('prime number')
                print("found factor: ", p)
                return

            print("phase 2")
            
            R_i_d = {}
            for i in range(2, delta_max + 1, 2):
                p2 = self.mul(i, p)
                if self.is_not_point(p2):
                    if p2 is None:
                        pass
                        #raise BaseException('prime number')
                    #raise BaseException('p2 is not a point')
                R_i_d[i] = p2
                #print('adding item: ', i)
                #R_i.append(p2)
                
            prime_i = next_prime(b1)
            q_i = self.mul(prime_i, p)
            if self.is_not_point(q_i):
                if q_i is None:
                    pass
                    #raise BaseException('prime number')
                raise BaseException('q_i is not a point, factor should be ', prime_i)
            
            while prime_i < b2:
                prime_i_minus_1 = prime_i
                prime_i = next_prime(prime_i)
                if prime_i >= b2:
                    break
                q_i_minus_1 = q_i
                #print('len R_i: ', len(R_i))
                #print('delta max: ', delta_max)
                #print('accessing item: ', prime_i - prime_i_minus_1)
                q_i = self.addition(q_i_minus_1, R_i_d[prime_i - prime_i_minus_1])
                if self.is_not_point(q_i):
                    if q_i is None:
                        raise BaseException('prime number')
                    print('q_i is not a point, found factor: ', int(q_i))
                    return
            

    def addition(self, P, Q):
        """
        :param P: One point on EC 
        :param Q: Second Point on EC
        :return: P + Q
        """
        if P.ideal() and not Q.ideal():
            return Q
        elif not P.ideal() and Q.ideal():
            return P
        elif not P.ideal() and not Q.ideal():
            N = P.curve.P
            d = gcd(P.X - Q.X, N)
            if 1 < d < N:
                return d # non trivial factor
            if d == 1: # x1 = x2
                iv = invert(f_mod(P.X - Q.X, N), N)
                delta = f_mod((P.Y - Q.Y) * iv, N)
                x_3 = f_mod(delta * delta - P.X - Q.X, N)
                y_3 = f_mod(delta * (P.X - x_3) - P.Y, N)
                return Point(P.curve, x_3, y_3)
            else:
                d = gcd(P.Y + Q.Y, N)
                if 1 < d < N:
                    return d # non trivial factor
                if d == N:
                    return Ideal() # non trivial factor
                if d == 1: # x1 != x2
                    iv = invert(f_mod(P.Y + Q.Y, N), N)
                    delta = f_mod((3 * P.X * P.X + P.curve.A) * iv, N)
                    x_3 = f_mod(delta * delta - P.X - Q.X, N)
                    y_3 = f_mod(delta * (P.X - x_3) - P.Y, N)
                    return Point(P.curve, x_3, y_3)

    def mul(self, k, p):
        """
        :param k: how many times 
        :param p: Point
        :return: k*P
        """        
        e = bin(k)[2:]  # transform to binary
        e = e[::-1]  # reverse it
        Q = p
        R = Ideal() if e[0] == '0' else p # ideal if k is even, p otherwise
        for i in e:
            Q = self.addition(Q, Q)
            if self.is_not_point(Q): # neither ideal nor point
                return Q
            if i == '1':
                R = self.addition(R, Q)
                if self.is_not_point(R):
                    return R
        return R


if __name__ == "__main__":   
    p = next_prime(10**20 + 12345)
    q = next_prime(10**40 +8985465)
    l = Lenstra(p*q)
    print('factor p:' + str(p) + ', len: ' + str(len(str(p))))
    print('factor q:' + str(q) + ', len: ' + str(len(str(q))))
    print('factor p*q:' + str(p*q) + ', len: ' + str(len(str(p*q))))

    l.factorECM(b1=15000, max_round=200)
    
    """
    # 36 cifre
    p = next_prime(10**15)
    q = next_prime(10**20)
    l = Lenstra(p*q)
    l.factorECM(b1=9000, max_round=200)

    # 46 cifre
    p = next_prime(10**15)
    q = next_prime(10**30)
    l = Lenstra(p*q)
    l.factorECM(b1=9000, max_round=200)

    # 46 cifre
    p = next_prime(10**15)
    q = next_prime(10**30)
    l = Lenstra(p*q)
    l.factorECM(b1=10000, max_round=200)

    # 51 cifre
    p = next_prime(10**20)
    q = next_prime(10**30)
    l = Lenstra(p*q)
    l.factorECM(b1=11000, max_round=200) # con 10000 e' al limite (182), con 11000 (28), 12000 (63)

    # 56 cifre
    p = next_prime(10**15)
    q = next_prime(10**40)
    l = Lenstra(p*q)
    l.factorECM(b1=10000, max_round=200) # 10000 con (65), 11000 (6)

    # 61 cifre
    p = next_prime(10**20)
    q = next_prime(10**40)
    l = Lenstra(p*q)
    l.factorECM(b1=12000, max_round=200) # funziona anche con 10000

    # 71 cifre
    p = next_prime(10**20)
    q = next_prime(10**50)
    l = Lenstra(p*q)
    l.factorECM(b1=13000, max_round=200) # funziona anche con 12000
    """
