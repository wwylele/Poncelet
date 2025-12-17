# Outer: (x-u)^2 + y^2 = r^2
# Inner: x^2 + y^2 = 1
# Elliptic: 
#   y^2 = x * (r^2*x^2 + (1 - u^2 - r^2)*x + u^2)
#   y^2 = r^2*x^3 + (1 - u^2 - r^2)*x^2 + u^2 * x
# Elliptic additive point = (0, 1)

import math
import matplotlib.pyplot as plt
import matplotlib
import numpy
from fractions import Fraction
import sys
from tabulate import tabulate

sys.set_int_max_str_digits(0)



max_degree = 2

target = 3


degree_list = [(X, Y, is_deno) 
                for X in range(max_degree + 1)
                for Y in range(max_degree + 1)
                for is_deno in [True, False] 
                if X + Y <= max_degree]
fixation_term = (0, 0, True)
fixation_term2 = None

degree_list.sort(key = lambda j : j[0] + j[1])

jj_symbols = [f"{"Deno" if is_deno else "Nume"}_X^{X}_Y^{Y}" for X, Y, is_deno in degree_list]

def run(u, r, k):
        
    assert (u + r) * (u + r) - 1 == k * k


    fixation_term2 = ((0, 1, True), Fraction(0))

    def rpoint (pq) :
        p0, p1, q0, q1 = pq
        return (2 * q0 + 2 * u * q1 * q1 - p0,
                2 * q1 - 2 * u * q0 * q1 - p1, 
                q0, q1)

    def rchord (pq):
        p0, p1, q0, q1 = pq
        return (p0, p1,
                2 * p0 / (2 * u * p0 + r * r - u * u) - q0,
                2 * p1 / (2 * u * p0 + r * r - u * u) - q1)
        
    def elliptic_add (xy):
        x, y = xy
        k = (y - 1) / (x - 1)
        x2 = (k * k + u * u - 1) / (r * r) - x
        return (x2, -(k * (x2 - 1) + 1))

            
    def xformula (pq):
        x, y, a, b = pq
        return (-u*(u-r)*k * x + -u*(u+r) * y + -2*u*r*k * a + (u*(u*u-r*r)*(u+r) + 2*u*r) * b) / \
            (r*(u-r)*k * x + r*(u+r) * y + -2*u*r*k * a + (r*(u*u-r*r)*(u+r) - 2*u*r) * b) 
            

    def yformula (pq):
        x, y, a, b = pq
        return (u*((u+r)**2-1) * x + -k*u*(r*r+u*r-1) * y + u*((u+r)**2-1)*(u*u-r*r) * a + -2*u*u*((u+r)**2-1)) / \
            (r*(r*r+u*r-1) * x + k*r * y + -2*r*((u+r)**2-1) * a + k*r*((u+r)**2-2) * b + u*r*(u+r)**2)
    
    def pxformula (xy):
        x, y = xy
        return (2*r*r*r*((u+r)**2-1) * x*x - r*r*(u+r) * y*y + 2*r*(1-r*r-r*u)*((u+r)**2-1) * x + (u+r)*u*u*((u+r)**2-1)) / \
            (-r*r * y*y + 2*r*u*((u+r)**2-1) * x + u*u*((u+r)**2-1))
    
    def pxformula2 (xy):
        x, y = xy
        return (r*r*(u+r)*x*x + 2*r*(1-r*r-r*u)*x + u*u*(u+r)) / (r * x + u)**2
    
    def pyformula (xy):
        x, y = xy
        return ( 2*r*r*r*k*x*y -2*r*k*((u+r)**2-1)*y) / \
            (-r*r * y*y + 2*r*u*((u+r)**2-1) * x + u*u*((u+r)**2-1))
    
    def pyformula2 (xy):
        x, y = xy
        return -2*r*k*y / (r * x + u)**2
    
    def paformula (xy):
        x, y = xy
        return (2*r*((u+r)**2-1) * (u-r*x) * y +  (r*x+u) * (r*r*(u+r)*x*x + 2*r*(1-r*(u+r))*x + (u+r)*u*u)) / \
               ((r*x+u) * ((r*x-u)**2*(u+r)**2 + 4*u*r*x))
    
    def paformula2 (xy):
        x, y = xy
        return (u+r)**2 * \
                (2*r*((u+r)**2-1) * (u-r*x) * y +  (r*x+u) * (r*r*(u+r)*x*x + 2*r*(1-r*(u+r))*x + (u+r)*u*u)) / \
               ((r*x+u) * ( ((u+r)**2*(r*x-u)+2*u)**2 + (2*u*k)**2) )
    
    def pbformula (xy):
        x, y = xy
        return k * (-2*r*(r*x+u)*y + (u - r*x)* (r*r*(u+r)*x*x + 2*r*(1-r*(r+u))*x + (u+r)*u*u)) / \
                ((r*x+u) * ((r*x-u)**2*(u+r)**2 + 4*u*r*x))

    
    def assertElliptic (xy):
        x, y = xy
        assert y * y == r*r*x*x*x + (1 - u*u - r*r)*x*x + u*u * x

    pq0 = (u + r, 0, 1 / (u + r), k / (u + r))

    pqlist = [pq0]
    xylist = [(Fraction(0), Fraction(0))]

    for i in range(100):
        pqlist.append(rchord(rpoint(pqlist[-1])))
        xylist.append(elliptic_add(xylist[-1]))

    for i in range(0, len(pqlist)):
        assertElliptic(xylist[i])
        assert xylist[i][0] == xformula(pqlist[i])
        assert xylist[i][1] == yformula(pqlist[i])

        x,y=xylist[i]
        if (r * x + u)**2 != 0 :
            assert pqlist[i][0] == pxformula2(xylist[i])
            assert pqlist[i][1] == pyformula2(xylist[i])
        else:
            print("pxformula/pyformula has zero divisor!!!")

        assert pqlist[i][2] == paformula2(xylist[i])
        assert pqlist[i][3] == pbformula(xylist[i])
    '''fig, ax = plt.subplots()
    outer = plt.Circle((float(u), 0), float(r), edgecolor = 'black', fill = False)
    inner = plt.Circle((0, 0), 1, edgecolor = 'black', fill = False)

    ax.add_patch(outer)
    ax.add_patch(inner)

    ax.add_line(matplotlib.lines.Line2D([float(pq[0]) for pq in pqlist], 
                                        [float(pq[1]) for pq in pqlist]))
    ax.add_line(matplotlib.lines.Line2D([float(xy[0]) for xy in xylist], 
                                        [float(xy[1]) for xy in xylist], color='red'))

    ax.set_aspect('equal')
    ax.set_xlim(float(u - r-1), float(u + r+1))
    ax.set_ylim(float(-r-1), float(r+1))

    #plt.show()'''


    print("Generated points")

    equation_count = len(degree_list)
    print(equation_count)
    equations = []

    a = []
    for d in degree_list:
        if d == fixation_term:
            a.append(Fraction(1))
        else:
            a.append(Fraction(0))
    a.append(Fraction(1))
    assert len(a) == equation_count + 1
    equations.append(a)

    if fixation_term2 is not None:
        a = []
        term, v = fixation_term2
        for d in degree_list:
            if d == term:
                a.append(Fraction(1))
            else:
                a.append(Fraction(0))
        a.append(v)
        assert len(a) == equation_count + 1
        equations.append(a)



    remaining = equation_count - len(equations)

    for i in range(remaining):
        if i >= len(pqlist):
            raise "What"
        a = []
        for (X, Y, is_deno) in degree_list:
            term = xylist[i][0] ** X * \
                xylist[i][1] ** Y 
            if is_deno:
                a.append(-term * pqlist[i][target])
            else:
                a.append(term)
        a.append(Fraction(0))
        assert len(a) == equation_count + 1
        equations.append(a)

    def add_to_row(dest, addon, mult):
        for i in range(len(dest)):
            dest[i] += addon[i] * mult

    print("\n*** Guassian pass A ***")
    for row in range(equation_count):
        print(f"> row {row}")
        sys.stdout.flush()
        for good_row in range(row, equation_count):
            if equations[good_row][row] != 0:
                break
        else:
            print(f"Singular at row {row}!")
            good_row = equation_count - 1
            equations[good_row] = [Fraction(0, 1) if i != row else Fraction(1, 1) for i in range(equation_count + 1)]

        if good_row != row:
            equations[row], equations[good_row] = equations[good_row], equations[row]

        for col in range(row + 1, len(equations[row])):
            equations[row][col] /= equations[row][row]
        equations[row][row] = Fraction(1, 1)

        for row2 in range(row + 1, equation_count):
            mult = -equations[row2][row]
            add_to_row(equations[row2], equations[row], mult)

    print("\n*** Guassian pass B ***")
    for row in reversed(range(1, equation_count)):
        print(f"> row {row}")
        sys.stdout.flush()
        for row2 in range(0, row):
            mult = -equations[row2][row]
            add_to_row(equations[row2], equations[row], mult)

    for row in range(equation_count):
        for col in range(equation_count):
            if row == col:
                assert equations[row][col] == 1
            else:
                assert equations[row][col] == 0


    final_solution = [equations[i][-1] for i in range(equation_count)]
    
    final_solution = [f for f in final_solution]

    print("\n*** Solution ***")
    for symbol, value in zip(jj_symbols, final_solution):
        print(f"{symbol} = {value}")

    for n, (pq, xy) in enumerate(zip (pqlist, xylist)):
        num = Fraction(0)
        den = Fraction(0)
        for c, (X, Y, is_deno) in zip(final_solution, degree_list):
            term = c * xy[0] ** X * \
                xy[1] ** Y
            if is_deno:
                den += term
            else:
                num += term
        if den == 0:
            print(f"[{n}]>>> DIV BY ZERO")
        else:
            print(f"[{n}]>>> {num / den  - pq[target]}")
        if n > equation_count + 20:
            break
    return final_solution

spaceList = [
    (Fraction(13, 5), Fraction(12, 5), Fraction(1, 5)),
    (Fraction(5, 3), Fraction(4, 3), Fraction(1,3)),
    (Fraction(17, 15), Fraction(8, 15), Fraction(1, 15))
]

urkList = []

for u_add_r, k, urunit in spaceList:
    u = urunit
    r = u_add_r - u
    while r > 0:
        urkList.append((u, r, k))
        u += urunit
        r -= urunit

solutions = [["-"] + jj_symbols]

for urk in urkList:
    solutions.append([f"u={urk[0]}, r={urk[1]}"] + run(urk[0], urk[1], urk[2]))

solutions.append(["Note"] + ["= "] * len(jj_symbols))

print(tabulate(list(map(list, zip(*solutions)))))