# Outer: (x-u)^2 + y^2 = r^2
# Inner: x^2 + y^2 = 1
# Elliptic: 
#   y^2 = (x + 1) * (r^2*x^2 - (u^2 - r^2 - 1)*x +1)
#   y^2 = r^2*x^3  + (1 + 2*r^2 - u^2) * x^2 + (2 + r^2 - u^2) * x + 1
# Elliptic additive point = (0, 1)

import math
import matplotlib.pyplot as plt
import matplotlib
import numpy
from fractions import Fraction
import sys
from tabulate import tabulate

sys.set_int_max_str_digits(0)



max_degree = 1

target = 0 

if target == 0:
    degree_list = [(p0, p1, q0, q1, is_deno) 
                    for q0 in range(max_degree + 1)
                    for q1 in range(max_degree + 1)
                    for p0 in range(max_degree + 1) 
                    for p1 in range(max_degree + 1)
                    for is_deno in [True, False] 
                    if p0 + p1 + q0 + q1 <= max_degree and
                    (p0, p1, q0, q1) != (0, 2, 0, 0) and
                    (p0, p1, q0, q1) != (0, 0, 0, 2)and
                    (p0, p1, q0, q1) != (0, 1, 0, 1)]
    fixation_term = (0, 1, 0, 0, True)
elif target == 1:
    degree_list = [(p0, p1, q0, q1, is_deno) 
                    for q0 in range(max_degree + 1)
                    for q1 in range(max_degree + 1)
                    for p0 in range(max_degree + 1) 
                    for p1 in range(max_degree + 1)
                    for is_deno in [True, False] 
                    if p0 + p1 + q0 + q1 <= max_degree and
                    (p0, p1, q0, q1) != (0, 2, 0, 0) and
                    (p0, p1, q0, q1) != (0, 0, 0, 2)and
                    (p0, p1, q0, q1) != (0, 1, 0, 1)]
    fixation_term = (0, 0, 0, 0, True)

degree_list.sort(key = lambda j : j[0] + j[1] + j[2] + j[3])

jj_symbols = [f"{"Deno" if is_deno else "Nume"}_x^{p0}_y^{p1}_a^{q0}_b^{q1}" for p0, p1, q0, q1, is_deno in degree_list]

def run(u, r, k):
        
    assert (u + r) * (u + r) - 1 == k * k

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
        k = (y - 1) / x
        x2 = (k * k + u * u - 2 * r * r - 1) / (r * r) - x
        return (x2, -(k * x2 + 1))


    #def xformula_old (pq):
    #    x, y, a, b = pq
    #    return ((r*r*r + r*r*u - r*u*u - 2*r - u*u*u) * b + (u + r) * (u + r) * a * b + (u*u - r*r) * k * b*b) / \
    #        (r * (u + r) * k * b*b + r * b + r * k * a - r * (u + r) * a * b - r * k * x)

            
    def xformula (pq):
        x, y, a, b = pq
        return (-(u*u-r*r)*k * x + -(u+r)*(u+r) * y + ((u*u-r*r)*(u*u-r*r) + 4*u*r) * b) / \
            (r*(u-r)*k * x + r*(u+r) * y + -2*u*r*k * a + (r*(u*u-r*r)*(u+r) - 2*u*r) * b) 
            

    def yformula (pq):
        x, y, a, b = pq
        return (u*((u+r)*(u+r)-1) * x + -k*u*(r*r+u*r-1) * y + u*((u+r)*(u+r)-1)*(u*u-r*r) * a + -2*u*u*((u+r)*(u+r)-1)) / \
            (r*(r*r+u*r-1) * x + k*r * y + -2*r*((u+r)*(u+r)-1) * a + k*r*((u+r)*(u+r)-2) * b + u*r*(u+r)*(u+r))
    
    def assertElliptic (xy):
        x, y = xy
        assert y * y == r*r*x*x*x + (1 + 2*r*r - u*u) * x*x + (2 + r*r - u*u) * x + 1

    pq0 = (u + r, 0, 1 / (u + r), k / (u + r))

    pqlist = [pq0]
    xylist = [(Fraction(-1), Fraction(0))]

    for i in range(100):
        pqlist.append(rchord(rpoint(pqlist[-1])))
        xylist.append(elliptic_add(xylist[-1]))

    for i in range(0, len(pqlist)):
        x = xformula(pqlist[i])
        y = yformula(pqlist[i])
        assert xylist[i][0] == x
        assert xylist[i][1] == y
        assertElliptic(xylist[i])

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

    for xyi in [target]:
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

        for i in range(equation_count - 1):
            if i >= len(pqlist):
                raise "What"
            a = []
            for (p0, p1, q0, q1, is_deno) in degree_list:
                term = pqlist[i][0] ** p0 * \
                    pqlist[i][1] ** p1 * \
                    pqlist[i][2] ** q0 * \
                    pqlist[i][3] ** q1
                if is_deno:
                    a.append(-term * xylist[i][xyi])
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
            for c, (p0, p1, q0, q1, is_deno) in zip(final_solution, degree_list):
                term = c * pq[0] ** p0 * \
                    pq[1] ** p1 * \
                    pq[2] ** q0 * \
                    pq[3] ** q1
                if is_deno:
                    den += term
                else:
                    num += term
            if den == 0:
                print(f"[{n}]>>> DIV BY ZERO")
            else:
                print(f"[{n}]>>> {num / den  - xy[xyi]}, ({float(pq[0])}, {float(pq[1])}) ({float(pq[2])}, {float(pq[3])}) -> {float(xy[xyi])}")
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