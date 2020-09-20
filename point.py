#! /usr/bin/python3

from ideal import Ideal
from gmpy2 import invert
from gmpy2 import f_mod


class Point(Ideal):
    def __init__(self, curve, X, Y):
        """
        :param curve: point belongs to curve
        :param X: coordinate X
        :param Y: coordinate Y
        """
        self.curve = curve
        self.X = X
        self.Y = Y
        if not self.curve.check_point(self.X, self.Y):
            raise BaseException("wrong point")

    def getCurve(self):
        return self.curve

    def getX(self):
        return self.X
    
    def getY(self):
        return self.Y
    
    def _compare_points_(self, other):
        return (self.X == other.X) and (self.Y == other.Y)

    def __double_point__(self):
        """
        P = [x_1, y_1]
        2*P = [x_3, y_3]
        :return: 2*P = [m^2 - 2*x_1, -m(x_3 - x_1) - y_1]
        m = 3*(x_1)^2 + A
            --------------
                 2*y_1
        """
        invert_y = invert(2 * self.Y, self.curve.P)
        if invert_y == 0:
            raise BaseException('infinite')
        m = f_mod((((3 * (self.X * self.X) + self.curve.A)) * (invert_y)), self.curve.P)
        x_3 = f_mod(((m * m) - self.X - self.X), self.curve.P)
        y_3 = f_mod((m * (self.X - x_3) - self.Y), self.curve.P)
        return Point(self.curve, x_3, y_3)

    def __add_other_point(self, other):
        """
        P = [x_1, y_1]
        Q = [x_2, y_2]
        m = y_2 - y_1
            ---------
            x_2 - x_1
        P + Q = [x_3, y_3] = [m^2 - x_1 - X-2, -m(x_3 - x_1) - y_1]
        :param other: Point 
        :return: self + other according to EC rules
        """
        x = f_mod((other.X - self.X), self.curve.P)
        x = invert(x, self.curve.P)
        if x == 0:
            raise BaseException('infinite')
        m = f_mod(((other.Y - self.Y) * x), self.curve.P)
        x_3 = f_mod((m * m - self.X - other.X), self.curve.P)
        y_3 = f_mod((m * (self.X - x_3) - self.Y), self.curve.P)
        return Point(self.curve, x_3, y_3)

    def __add__(self, other):
        if self._compare_points_(other):
            return self.__double_point__()
        else:
            return self.__add_other_point(other)

    def __str__(self):
        return "(%s, %s)" % (self.X, self.Y)

    def ideal(self):
        return False
