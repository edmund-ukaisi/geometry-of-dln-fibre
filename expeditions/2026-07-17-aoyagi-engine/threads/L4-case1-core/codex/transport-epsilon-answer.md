## Verdict

[MODELING] I used the dimensions and multiplication order stated in the question:

\[
C^{(1)}C^{(2)}C^{(3)},
\]

and the canonical Schur shear \(c_{ij}\mapsto c_{ij}-c_{iJ}c_{Jj}\) for \(i,j>J\). The double path necessarily also contains:

\[
(2,0)\xrightarrow{\mathrm{case12}}(2,1)
\xrightarrow{\mathrm{case11}}(2,1)
\xrightarrow{\mathrm{case2}}(2,2)
\xrightarrow{\mathrm{rollover}}(3,0).
\]

The case2 edge after boost #1 is required because case11 does not advance `cleared`.

### 1. Single boost: `(2,2,2,2)`

[OBSERVED—SymPy] After the two layer-1 edges, with \(w=u_{12}\),

\[
A_*=
\begin{pmatrix}
1&a\\
g&w-ag
\end{pmatrix}.
\]

Thus the literal coordinate-recursive residual is

\[
R_1=A_*BZ,
\]

where

\[
B=\begin{pmatrix}b_{00}&b_{01}\\b_{10}&b_{11}\end{pmatrix},
\qquad
Z=\begin{pmatrix}z_{00}&z_{01}\\z_{10}&z_{11}\end{pmatrix}.
\]

Equivalently, putting

\[
P=b_{00}+ab_{10},\quad Q=b_{01}+ab_{11},\quad
U=gb_{00}+(w-ag)b_{10},\quad V=gb_{01}+(w-ag)b_{11},
\]

we obtain

\[
R_1=
\begin{pmatrix}
Pz_{00}+Qz_{10}&Pz_{01}+Qz_{11}\\
Uz_{00}+Vz_{10}&Uz_{01}+Vz_{11}
\end{pmatrix}.
\]

For \(C=\{w,b_{00},b_{10}\}\):

| Part | Verdict | Exact witness |
|---|---|---|
| A1 | **FALSE** | \(R_{00}|_{C=0}=(b_{01}+ab_{11})z_{10}\neq0\) |
| A2 | **FALSE** | \(R_{10}\) contains \(w\,b_{10}z_{00}\), of center degree \(2\) |
| A3 | **FALSE** | After \(b_{00},b_{10}\mapsto wb_{00},wb_{10}\), the A1 witness remains non-divisible by \(w\) |

[OBSERVED—SymPy] The maximum exponent of \(w\) is \(1\); no \(w^2\) occurs.

[INFERENCE] The previously used triangular form

\[
ZB\begin{pmatrix}1&a\\0&w\end{pmatrix}
\]

is not this `foldResid`: it also performs a generator-side row/column preparation and reverses the factor convention. Those ideal-preserving operations are absent from the stated “core generators followed only by coordinate substitutions” definition.

### 2. Double boost: `(3,3,2,2)`

[OBSERVED—SymPy] Immediately before the second boost,

\[
R_2=A_*B_*Z,
\]

with

\[
A_*=
\begin{pmatrix}
1&a_{01}&a_{02}\\
a_{10}&a_{11}-a_{01}a_{10}&a_{11}a_{12}-a_{02}a_{10}\\
a_{20}&a_{11}a_{21}-a_{01}a_{20}&
a_{11}w-a_{02}a_{20}-a_{11}a_{12}a_{21}
\end{pmatrix},
\]

and

\[
B_*=
\begin{pmatrix}
1&b_{01}\\
b_{10}&wb_{11}-b_{01}b_{10}\\
b_{20}&b_{11}b_{21}-b_{01}b_{20}
\end{pmatrix}.
\]

Here \(w=u_{13}\). With the stated \(M^{(s)}\times M^{(s+1)}\) orientation, the second center is

\[
C_2=\{w,z_{00},z_{01}\}.
\]

| Part | Verdict | Exact witness |
|---|---|---|
| A1 | **FALSE** | \(R_{00}|_{C_2=0}=\bigl[b_{01}-a_{01}b_{01}b_{10}-a_{02}b_{01}b_{20}+a_{02}b_{11}b_{21}\bigr]z_{10}\) |
| A2 | **FALSE** | \(R_{20}\) contains \(a_{11}b_{20}wz_{00}\), of center degree \(2\) |
| A3 | **FALSE** | The A1 witness survives the boost substitution and is not divisible by \(w\) |

[OBSERVED—SymPy] The exact maximum exponent of \(w\) is

\[
\boxed{1}.
\]

There is no \(w^2\) monomial. A2 nevertheless fails because of mixed center monomials such as \(wz_{00}\).

[OBSERVED—SymPy] Using the transposed partial block \(\{w,z_{00},z_{10}\}\) gives the same double verdict `(FALSE,FALSE,FALSE)`, maximum \(w\)-exponent \(1\), and no \(w^2\).

[INFERENCE] The suspected “old b-chain \(w\) times new boost \(w\)” does not occur because the boost block lies before the old suffix carrying \(w\). In the exact matrix contraction, the two potential \(w\)-sources occupy different intermediate indices.

## 3. Design answer

[INFERENCE] The proposed accumulating transport

\[
\epsilon_w\mathrel{+}=\#\{\text{center entries read}\}
\]

is not the right invariant. It predicts possible accumulation that the exact double computation does not exhibit. The b-chain exponent is instead binary:

\[
\epsilon_d(i)=\mathbf 1_{\{\widetilde t_d<i\}}\in\{0,1\}.
\]

A per-layer degree bound alone is also insufficient: it does not force support outside the boost center to carry \(w\).

[INFERENCE] For a prepared residual, the smallest useful carried form for a prospective boost center \(C=\{w\}\cup P\) is

\[
r=\sum_{x\in P}a_xx
  +w\sum_{y\in X\setminus P}b_yy,
\]

where the coefficients ignore \(C\). This records precisely:

- terms using the partial block \(P\) do not already contain \(w\);
- terms using support outside \(P\) contain exactly one \(w\).

For all future divisors, this can be carried as the binary incidence law \(\epsilon_d(i)=\mathbf1_{\widetilde t_d<i}\), together with one-current-layer-coordinate-per-term. A full arbitrary exponent vector per monomial is stronger than necessary.

[INFERENCE] The δ=1 boost consumes only the local decomposition

\[
r=\sum_{c\in C}q_c\,c,\qquad q_c\text{ independent of }C,
\]

which yields

\[
r(\operatorname{blockBlowupMap}_C)=
w\,r(\operatorname{blockBlowupCoordQuot}_w).
\]

The induction must carry the stronger future-facing routing law and the Schur-prepared form.

[INFERENCE] For the literal `foldResid` checked above, that prepared form is false already in the single case. Therefore no ε invariant can prove the stated boost-readiness without changing the residual object to include the regular generator-side \(P,Q\) preparation.

## SymPy run

```python
import sympy as sp

def syms(prefix, rows, cols):
    return sp.Matrix(rows, cols, sp.symbols(
        ' '.join(f'{prefix}{i}{j}'
                 for i in range(rows) for j in range(cols))))

def apply(M, subst):
    return M.applyfunc(
        lambda f: sp.expand(f.subs(subst, simultaneous=True)))

def schur_edge(coords, M, J, center, pivot, delta):
    sh = {x: x for x in coords}
    for i in range(M.rows):
        for j in range(M.cols):
            if i > J and j > J:
                sh[M[i,j]] = M[i,j] - M[i,J]*M[J,j]

    out = {}
    for x in coords:
        if delta:
            out[x] = 1 if x == pivot else sh[x]
        elif x == pivot:
            out[x] = sh[x]
        elif x in center:
            out[x] = sp.expand(pivot*sh[x])
        else:
            out[x] = sh[x]
    return out

def case11_edge(coords, center, pivot):
    return {
        x: x if x == pivot else pivot*x if x in center else x
        for x in coords
    }

def audit(R, center, pivot, allvars):
    entries = list(map(sp.expand, R))
    zero = {x: 0 for x in center}

    a1 = all(f.subs(zero, simultaneous=True).expand() == 0
             for f in entries)

    def degree(f):
        return max((sum(m) for m in sp.Poly(f, *center).monoms()),
                   default=0)

    a2 = all(degree(f) <= 1 for f in entries)

    pull = {x: pivot*x for x in center if x != pivot}
    pulled = [f.subs(pull, simultaneous=True).expand()
              for f in entries]
    a3 = all(
        g.subs(pivot, 0).expand() == 0
        and sp.cancel(g/pivot).is_polynomial(*allvars)
        for g in pulled
    )

    max_w = max(sp.Poly(f, pivot).degree() for f in entries)
    w2 = [
        term for f in entries for term in sp.Add.make_args(f)
        if term.as_powers_dict().get(pivot, 0) >= 2
    ]
    return a1, a2, a3, max_w, w2

# Single
A, B, Z = syms('a',2,2), syms('b',2,2), syms('z',2,2)
w = sp.Symbol('w')
A = A.subs(A[1,1], w)
coords = set(A) | set(B) | set(Z)

Astar = apply(A, schur_edge(coords, A, 0, set(A), A[0,0], 1))
Astar = apply(Astar, schur_edge(coords, A, 1, {w}, w, 0))
R1 = (Astar*B*Z).applyfunc(sp.expand)

C1 = (w, B[0,0], B[1,0])
V1 = tuple(sorted(set().union(*(f.free_symbols for f in R1)),
                  key=str))
assert audit(R1, C1, w, V1)[:4] == (False, False, False, 1)

# Double
A, B, Z = syms('a',3,3), syms('b',3,2), syms('z',2,2)
A = A.subs(A[2,2], w)
coords = set(A) | set(B) | set(Z)

Astar = A
for J, delta in ((0,1), (1,0), (2,0)):
    center = {A[i,j] for i in range(J,3) for j in range(J,3)}
    Astar = apply(
        Astar, schur_edge(coords, A, J, center, A[J,J], delta))

# case12 at (2,0)
Bstar = apply(B, schur_edge(coords, B, 0, set(B), B[0,0], 1))
# boost #1 at (2,1)
Bstar = apply(Bstar, case11_edge(coords, {w, B[1,1]}, w))
# required case2 clear before rollover
center_clear = {B[i,j] for i in range(1,3) for j in range(1,2)}
Bstar = apply(
    Bstar,
    schur_edge(coords, B, 1, center_clear, B[1,1], 0))

R2 = (Astar*Bstar*Z).applyfunc(sp.expand)
C2 = (w, Z[0,0], Z[0,1])
V2 = tuple(sorted(set().union(*(f.free_symbols for f in R2)),
                  key=str))

out = audit(R2, C2, w, V2)
assert out[:4] == (False, False, False, 1)
assert not out[4]  # no w^2 term

print(Astar)
print(Bstar)
print(out[:4])
```