"""Exact (sympy) certificate for Proposition 'OSH explicit for d <= 3' (condition (D)).

d = 3.  Admissible q for fixed p (p0 >= p1 >= p2 > 0, sum 1): q0 >= q1 >= q2, q0/p0 <= q1/p1 <= q2/p2, sum 1.
This is a polytope whose vertices are V1 = p, V2 = (1,1,1)/3, V3 = (p0,p1,p1)/(p0+2p1), V4 = (p1,p1,p2)/(2p1+p2)
(extreme rays of the cone {q0>=q1>=q2, p0 q1 >= p1 q0, p1 q2 >= p2 q1}).
(D) <=> lam2 <= x_j <= lam0 for j=0,1,2 (x_j = q_j p_j + (q_j - p_j)/2, lam_j = q_j p_j), i.e. the six AFFINE
(in q) conditions
   C0lo: q0 <= p0   C0hi: p0 - q0 <= 2(q0 p0 - q2 p2)
   C1hi: q1 - p1 <= 2(q0 p0 - q1 p1)          C1lo: p1 - q1 <= 2(q1 p1 - q2 p2)
   C2lo: q2 >= p2   C2hi: q2 - p2 <= 2(q0 p0 - q2 p2)
(x0 <= lam0, x0 >= lam2, x1 <= lam0, x1 >= lam2, x2 >= lam2, x2 <= lam0).
Each condition 'RHS - LHS >= 0' is evaluated at each vertex with p = (c+b+a, c+b, c)/s, s = a + 2b + 3c,
a,b,c >= 0 (this parametrises exactly the sorted p), multiplied by the (positive) denominators, and the resulting
polynomial in (a,b,c) is checked to have only NONNEGATIVE coefficients -> nonnegative on the whole region.
Also checks d = 2 and the flow identity sum_{i<k} c_ik/2 - sum_{j>k} c_kj/2 = (q_k - p_k)/2 for symbolic d = 2..7.
"""
import sympy as sp

a, b, c = sp.symbols('a b c', nonnegative=True)
s = a + 2 * b + 3 * c
p0, p1, p2 = (c + b + a) / s, (c + b) / s, c / s

vertices = {
    'V1 (q=p)': (p0, p1, p2),
    'V2 (uniform)': (sp.Rational(1, 3),) * 3,
    'V3 (p0,p1,p1)/Z': tuple(v / (p0 + 2 * p1) for v in (p0, p1, p1)),
    'V4 (p1,p1,p2)/Z': tuple(v / (2 * p1 + p2) for v in (p1, p1, p2)),
}


def conds(q0, q1, q2):
    return {
        'C0lo q0<=p0': p0 - q0,
        'C0hi x0>=lam2': 2 * (q0 * p0 - q2 * p2) - (p0 - q0),
        'C1hi x1<=lam0': 2 * (q0 * p0 - q1 * p1) - (q1 - p1),
        'C1lo x1>=lam2': 2 * (q1 * p1 - q2 * p2) - (p1 - q1),
        'C2lo q2>=p2': q2 - p2,
        'C2hi x2<=lam0': 2 * (q0 * p0 - q2 * p2) - (q2 - p2),
    }


all_ok = True
for vname, (q0, q1, q2) in vertices.items():
    for cname, expr in conds(q0, q1, q2).items():
        num, den = sp.fraction(sp.together(sp.simplify(expr)))
        num = sp.expand(num)
        den = sp.expand(den)
        # make denominator positive-coefficient (it is a product of positive factors); flip signs if needed
        dpoly = sp.Poly(den, a, b, c)
        if all(co <= 0 for co in dpoly.coeffs()):
            num, den = -num, -den
            dpoly = sp.Poly(den, a, b, c)
        assert all(co >= 0 for co in dpoly.coeffs()), (vname, cname, den)
        if num == 0:
            ok = True
            info = "identically 0"
        else:
            npoly = sp.Poly(num, a, b, c)
            ok = all(co >= 0 for co in npoly.coeffs())
            info = f"{len(npoly.coeffs())} terms, min coeff {min(npoly.coeffs())}"
        all_ok &= ok
        print(f"{vname:18s} {cname:16s}: {'OK ' if ok else 'FAIL'} ({info})")
print("d=3 vertex certificate:", "ALL CONDITIONS HOLD" if all_ok else "FAILED")

# d = 2: (D) <=> x1 <= lam0  <=>  3 q0 + p0 >= 2 (q0, p0 >= 1/2)
q0s, p0s = sp.symbols('q0 p0')
x1 = (1 - q0s) * (1 - p0s) + ((1 - q0s) - (1 - p0s)) / 2
print("d=2: lam0 - x1 =", sp.factor(sp.expand(q0s * p0s - x1)), " (= (3 q0 + p0 - 2)/2 >= 0 for q0,p0 >= 1/2)")

# flow identity for symbolic vectors
for d in range(2, 8):
    P = sp.symbols(f'p0:{d}')
    Qv = sp.symbols(f'q0:{d}')
    subsP = {P[-1]: 1 - sum(P[:-1])}
    subsQ = {Qv[-1]: 1 - sum(Qv[:-1])}
    okf = True
    for k in range(d):
        inflow = sum((Qv[k] * P[i] - Qv[i] * P[k]) / 2 for i in range(k)) \
            - sum((Qv[j] * P[k] - Qv[k] * P[j]) / 2 for j in range(k + 1, d))
        diff = sp.expand((inflow - (Qv[k] - P[k]) / 2).subs(subsP).subs(subsQ))
        okf &= (diff == 0)
    print(f"flow identity eps = c/2 solves conservation, d={d}: {okf}")
