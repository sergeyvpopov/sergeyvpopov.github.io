"""
Ex6SolutionChecker_exact.sage
-----------------------------

Exact/rigorous uniqueness certificate for

    X* = [[1,1,0],[1,1,0]]

under the row-sum constraints Y_1=Y_2=2, with
    alpha=3/10, beta=1/10, theta=(1,-5), v=(1,1,-5).

Proof structure
===============
1. Exact rational arithmetic proves Phi(X*) = 0.
2. The existing interval branch-and-bound proves Phi(X)>0 outside a
   small box N around X*.  This is a genuine global exclusion result.
3. Inside N, interval arithmetic proves G^1_{3,1}<0 and G^2_{3,1}<0.
   Since G^i_{1,3}=-G^i_{3,1}, Phi(X)=0 then forces X[1,3]=X[2,3]=0.
4. The row-sum constraints therefore reduce the local problem to
       X = [[a,2-a,0],[c,2-c,0]].
   With a,c in N, Phi=0 forces G^1_{2,1}=G^2_{2,1}=0.
5. After clearing denominators, Sage computes the exact resultant of
   those two polynomial equations.  Its factorisation is

       const*(a-1)*(3*a^2-6*a-22)
            *(68781*a^2-137562*a-949300).

   The two quadratic factors have no roots in the local interval
   [0.98,1.02]. Hence a=1. Substitution a=1 gives gcd=c-1,
   hence c=1. Therefore X=X* is the unique zero in N.

Together with step 2 this proves X* is the unique zero of Phi on F.

Run with Sage:
    sage Ex6SolutionChecker_exact.sage

We used https://sagecell.sagemath.org/ for running this code.
"""

alpha = QQ(3)/10
beta  = QQ(1)/10
theta = vector(QQ, [1, -5])
v     = vector(QQ, [1, 1, -5])

# ---------------------------------------------------------------------------
# Exact model


def model_exact(X):
    I3 = identity_matrix(QQ, 3)
    A = (I3 - alpha*beta*(X.transpose()*X)).inverse()
    B = (1-alpha)*v + alpha*(1-beta)*(X.transpose()*theta)
    R = A*B
    q = (1-beta)*theta + beta*(X*R)
    return A, B, R, q


def G_exact(X, i, j, k):
    A, B, R, q = model_exact(X)
    xi = X.row(i)
    Ax = A*xi
    return alpha*q[i]*(A[j,j]-A[k,k]) + alpha*beta*(R[j]-R[k])*(Ax[j]+Ax[k])


def Phi_exact(X):
    A, B, R, q = model_exact(X)
    total = QQ(0)
    for i in range(2):
        for k in range(3):
            if X[i,k] <= 0:
                continue
            for j in range(3):
                if j == k:
                    continue
                g = G_exact(X, i, j, k)
                if g > 0:
                    total += g**2
    return total

Xstar = matrix(QQ, [[1,1,0],[1,1,0]])
print("="*78)
print("PART 1: exact check at X*")
print("="*78)
phi_star = Phi_exact(Xstar)
print("Phi(X*) =", phi_star)
assert phi_star == 0
G1_31_star = G_exact(Xstar, 0, 2, 0)
G2_31_star = G_exact(Xstar, 1, 2, 0)
print("G^1_{3,1}(X*) =", G1_31_star)
print("G^2_{3,1}(X*) =", G2_31_star)
assert G1_31_star < 0 and G2_31_star < 0

# ---------------------------------------------------------------------------
# PART 2: global exclusion by interval branch-and-bound.
# We retain the rigorous interval calculation, but its conclusion is now
# explicitly only: Phi>0 outside N.  The local uniqueness proof is below.

RIF = RealIntervalField(200)
ALPHA = RIF(3)/RIF(10)
BETA  = RIF(1)/RIF(10)
THETA = vector(RIF, [1, -5])
V     = vector(RIF, [1, 1, -5])
I3_iv = identity_matrix(RIF, 3)


def model_iv(X):
    A = (I3_iv - ALPHA*BETA*(X.transpose()*X)).inverse()
    B = (1-ALPHA)*V + ALPHA*(1-BETA)*(X.transpose()*THETA)
    R = A*B
    q = (1-BETA)*THETA + BETA*(X*R)
    return A, B, R, q


def G_iv(M, X, i, j, k):
    A, B, R, q = M
    xi = X.row(i)
    Ax = A*xi
    return ALPHA*q[i]*(A[j,j]-A[k,k]) + ALPHA*BETA*(R[j]-R[k])*(Ax[j]+Ax[k])


def third_entry(x1, x2):
    if x1.lower() + x2.lower() > 2:
        return None, False
    x3 = RIF(2) - x1 - x2
    x3 = x3.intersection(RIF(0, 2))
    return x3, True


def Phi_lowerbound(x11, x12, x21, x22):
    x13, f1 = third_entry(x11, x12)
    if not f1:
        return None, False
    x23, f2 = third_entry(x21, x22)
    if not f2:
        return None, False

    X = matrix(RIF, [[x11,x12,x13],[x21,x22,x23]])
    M = model_iv(X)
    total = RIF(0)
    rows = [[x11,x12,x13],[x21,x22,x23]]
    for i in range(2):
        for k in range(3):
            # A contribution is guaranteed only when the whole interval
            # is strictly positive. Otherwise omit it for a safe lower bound.
            if rows[i][k].lower() <= 0:
                continue
            for j in range(3):
                if j == k:
                    continue
                g = G_iv(M, X, i, j, k)
                if g.lower() > 0:
                    total += g*g
    return total, True

EPS = RIF(1)/50       # 0.02
EPS_F = 0.02


def box_inside_N(box):
    (a,b),(c,d),(e,f),(g,h) = box
    return (a >= 1-EPS_F and b <= 1+EPS_F and
            c >= 1-EPS_F and d <= 1+EPS_F and
            e >= 1-EPS_F and f <= 1+EPS_F and
            g >= 1-EPS_F and h <= 1+EPS_F)


def branch_and_bound(box0, maxdepth=40):
    stack = [(box0, 0)]
    resolved = 0
    unresolved = []
    while stack:
        box, depth = stack.pop()
        (x11lo,x11hi),(x12lo,x12hi),(x21lo,x21hi),(x22lo,x22hi) = box
        x11 = RIF(x11lo,x11hi); x12 = RIF(x12lo,x12hi)
        x21 = RIF(x21lo,x21hi); x22 = RIF(x22lo,x22hi)

        val, feasible = Phi_lowerbound(x11, x12, x21, x22)
        if not feasible:
            resolved += 1
            continue
        if val.lower() > 0:
            resolved += 1
            continue
        if depth >= maxdepth:
            unresolved.append(box)
            continue

        widths = [x11hi-x11lo, x12hi-x12lo, x21hi-x21lo, x22hi-x22lo]
        d = widths.index(max(widths))
        pts = list(box)
        lo, hi = pts[d]
        mid = (lo+hi)/2
        p1 = pts[:]; p1[d] = (lo, mid)
        p2 = pts[:]; p2[d] = (mid, hi)
        stack.append((tuple(p1), depth+1))
        stack.append((tuple(p2), depth+1))
    return resolved, unresolved

print("\n" + "="*78)
print("PART 2: global exclusion outside N")
print("N = [0.98,1.02]^4 in (x11,x12,x21,x22)")
print("="*78)
box0 = ((0.0,2.0),(0.0,2.0),(0.0,2.0),(0.0,2.0))
resolved, unresolved = branch_and_bound(box0, maxdepth=40)
print("boxes certified Phi > 0:", resolved)
print("boxes unresolved:", len(unresolved))

if not unresolved:
    raise RuntimeError("Unexpected: no unresolved boxes; inspect branch-and-bound output.")
if not all(box_inside_N(box) for box in unresolved):
    print("Some unresolved boxes are outside N.")
    for box in unresolved[:10]:
        print("  ", box)
    raise RuntimeError("Global exclusion did not reduce all unresolved boxes to N.")
print("GLOBAL EXCLUSION CERTIFIED: Phi(X)>0 for every feasible X outside N.")

# ---------------------------------------------------------------------------
# PART 3: local sign certificate.
# On N, prove G^1_{3,1}<0 and G^2_{3,1}<0.
# If Phi=0 and x_i3>0, then both G^i_{3,1} and G^i_{1,3} must be <=0;
# since they are negatives of one another, they must both be zero.  The
# strict negativity below therefore forces x_i3=0.

print("\n" + "="*78)
print("PART 3: local support reduction")
print("="*78)

x11N = RIF(0.98,1.02); x12N = RIF(0.98,1.02)
x21N = RIF(0.98,1.02); x22N = RIF(0.98,1.02)
# Restrict third column to [0, 0.04]: feasible points in N have x_i3 = 2 - x_i1 - x_i2 >= 0
# (the previous inclusion of negative values made the interval over-approximation of G too loose).
XN = matrix(RIF, [[x11N, x12N, RIF(0, 0.04)],
                  [x21N, x22N, RIF(0, 0.04)]])
MN = model_iv(XN)
g1N = G_iv(MN, XN, 0, 2, 0)   # G^1_{3,1}
g2N = G_iv(MN, XN, 1, 2, 0)   # G^2_{3,1}
print("G^1_{3,1}(N) =", g1N)
print("G^2_{3,1}(N) =", g2N)
assert g1N.upper() < 0
assert g2N.upper() < 0
print("Both intervals are strictly negative.")
print("Hence any zero of Phi in N must have x13=x23=0.")

# ---------------------------------------------------------------------------
# PART 4: exact 2D boundary problem.
# X = [[a,2-a,0],[c,2-c,0]].  Near X*, all four nonzero holdings are
# positive, so Phi=0 forces G^1_{2,1}=G^2_{2,1}=0.
# Clear denominators and eliminate c exactly.

print("\n" + "="*78)
print("PART 4: exact algebraic uniqueness on x13=x23=0")
print("="*78)

a,c = var('a c')
Xac = matrix(SR, [[a,2-a,0],[c,2-c,0]])

# Build the same formulas over SR.
Aac = (identity_matrix(SR,3) - SR(alpha*beta)*(Xac.transpose()*Xac)).inverse()
Bac = (1-SR(alpha))*vector(SR,[1,-5,-0+0]) + SR(alpha*(1-beta))*(Xac.transpose()*vector(SR,[1,-5]))
# The preceding vector construction is deliberately replaced immediately below
# to avoid any coercion ambiguity.
Bac = (1-SR(alpha))*vector(SR,[1,1,-5]) + SR(alpha*(1-beta))*(Xac.transpose()*vector(SR,[1,-5]))
Rac = Aac*Bac
# Correct formula: q = (1-beta)*theta + beta*(X*R)   (was incorrectly using 1-alpha)
qac = (1-SR(beta))*vector(SR,[1,-5]) + SR(beta)*(Xac*Rac)


def G_ac(i,j,k):
    xi = Xac.row(i)
    Ax = Aac*xi
    return SR(alpha)*qac[i]*(Aac[j,j]-Aac[k,k]) + SR(alpha*beta)*(Rac[j]-Rac[k])*(Ax[j]+Ax[k])

f1 = G_ac(0,1,0)
f2 = G_ac(1,1,0)
p1 = f1.numerator()
p2 = f2.numerator()

# Put both polynomials into a genuine exact polynomial ring.
P = PolynomialRing(QQ, names=('a','c'), order='lex')
aa,cc = P.gens()
p1P = P(p1)
p2P = P(p2)

res = p1P.resultant(p2P, cc)
res_factor = factor(res)
print("Resultant factorisation:")
print(res_factor)

expected = (-5992368042253824000000)*(aa-1)*(3*aa^2-6*aa-22)*(68781*aa^2-137562*aa-949300)
assert P(res) == P(expected)
print("Resultant matches the exact factorisation.")

# The two quadratic factors have no roots in [0.98,1.02].  Use exact
# algebraic roots, not floating-point root finding.
# Convert to a univariate ring because multivariate polynomials
# (MPolynomial_libsingular) do not implement .roots().
R1 = PolynomialRing(QQ, 'a')
aa1 = R1.gen()
q1 = R1(3*aa1**2 - 6*aa1 - 22)
q2 = R1(68781*aa1**2 - 137562*aa1 - 949300)
for q in [q1, q2]:
    roots = q.roots(ring=AA)
    print("roots of", q, ":", roots)
    assert all(abs(RR(r) - 1) > RR(1)/50 for r, m in roots)

# Thus a=1 in the local box.  At a=1 the gcd in c is exactly c-1.
p1_at_1 = P(p1P.subs({aa:1}))
p2_at_1 = P(p2P.subs({aa:1}))
g = gcd(p1_at_1, p2_at_1)
print("gcd after setting a=1:", factor(g))
assert g == cc-1

print("Therefore c=1, hence a=1 and")
print("X = [[1,1,0],[1,1,0]] = X*.")

# ---------------------------------------------------------------------------
# Final conclusion

print("\n" + "="*78)
print("CERTIFICATE")
print("="*78)
print("1. Phi(X*) = 0 exactly.")
print("2. Phi(X) > 0 is rigorously certified outside N.")
print("3. Inside N, G^1_{3,1}<0 and G^2_{3,1}<0, forcing x13=x23=0")
print("   at any zero of Phi.")
print("4. On that boundary, exact resultant elimination gives a=1 and")
print("   exact gcd gives c=1.")
print("5. Hence X* is the UNIQUE zero of Phi on the feasible set F.")
print("="*78)

# ---------------------------------------------------------------------------
# LaTeX-ready export (Appendix 2)
# ---------------------------------------------------------------------------
print("\n" + "="*78)
print("LATEX EXPORT (copy the block below into your paper)")
print("="*78)
print(r"""
\begin{proposition}[Uniqueness of the stable allocation in Example~6]
Let \(\alpha=\frac{3}{10}\), \(\beta=\frac{1}{10}\), \(\theta=(1,-5)\), \(v=(1,1,-5)\)
and let \(\mathcal{F}\) be the set of non-negative \(2\times 3\) matrices with
row sums \(Y_1=Y_2=2\).  Define
\[
\Phi(X)=\sum_{i=1}^{2}\sum_{\substack{k=1\\X_{ik}>0}}^{3}
\sum_{\substack{j=1\\j\neq k}}^{3}\max\bigl(G^i_{j,k}(X),0\bigr)^2.
\]
Then \(X^*=\begin{pmatrix}1&1&0\\1&1&0\end{pmatrix}\) is the unique zero of
\(\Phi\) on \(\mathcal{F}\).
\end{proposition}

\begin{proof}[Computer-assisted proof]
We work throughout with exact rational arithmetic and rigorous interval
arithmetic (200 bits of precision).

\emph{Step 1 (exact evaluation).}
Direct substitution yields \(\Phi(X^*)=0\) and
\[
G^1_{3,1}(X^*)<0,\qquad G^2_{3,1}(X^*)<0.
\]

\emph{Step 2 (global exclusion).}
An interval branch-and-bound search on the box \([0,2]^4\) for the free
entries \((x_{11},x_{12},x_{21},x_{22})\) proves that every feasible point
outside the neighbourhood
\[
N=[0.98,1.02]^4
\]
satisfies \(\Phi(X)>0\).

\emph{Step 3 (local support reduction).}
On the feasible part of \(N\) (i.e.\ with third-column entries in
\([0,0.04]\)) interval evaluation gives
\[
G^1_{3,1}(N)\subset(-\infty,0),\qquad
G^2_{3,1}(N)\subset(-\infty,0).
\]
Consequently any zero of \(\Phi\) inside \(N\) must have \(x_{13}=x_{23}=0\).

\emph{Step 4 (exact algebraic uniqueness on the boundary).}
The problem reduces to the two-parameter family
\[
X=\begin{pmatrix}a&2-a&0\\c&2-c&0\end{pmatrix},\qquad
a,c\in[0.98,1.02].
\]
Vanishing of \(\Phi\) forces the two polynomial equations
\(G^1_{2,1}(X)=0\) and \(G^2_{2,1}(X)=0\).  After clearing denominators the
resultant with respect to \(c\) factors as
\[
\operatorname{Res}_c(p_1,p_2)
=-5992368042253824000000\,(a-1)\,(3a^2-6a-22)\,(68781a^2-137562a-949300).
\]
The two quadratic factors have no roots in the interval \([0.98,1.02]\)
(exact algebraic roots computed in the real algebraic numbers \(\mathbb{A}\)).
Hence \(a=1\).  Substituting \(a=1\) yields
\[
\gcd(p_1|_{a=1},p_2|_{a=1})=c-1,
\]
so \(c=1\).  Therefore the only zero inside \(N\) is \(X^*\).

Combining Steps 2--4 shows that \(X^*\) is the unique zero of \(\Phi\) on
the whole feasible set \(\mathcal{F}\).
\end{proof}

\noindent\textit{Computational certificate.}
The complete SageMath script that produces the interval bounds, the
resultant factorisation and the algebraic root isolation is available
as supplementary material.
""")
print("="*78)
