## Verdict

The proposed path has one error: since \(\delta=[J=0]\), the second layer-1 edge starts at \(J=1\), so it has \(\delta=0\), not \(\delta=1\).

The actual trace is

\[
(1,0)\xrightarrow[\delta=1]{\mathrm{case2}}(1,1)
\xrightarrow[\delta=0]{\mathrm{case2}}(1,2)
\xrightarrow{\mathrm{rollover}}(2,0)
\xrightarrow[\delta=1]{\mathrm{case11}}\cdots
\]

This agrees with the b-chain \((u_{11},u_{11}u_{12})\): \(u_{12}\) is non-dominant at \(p\), so `foldB p = u₁₁`, not \(u_{11}u_{12}\).

| Interpretation | A1 | A2 | A3 |
|---|---:|---:|---:|
| Actual fold, δ-sequence \(1,0\) | TRUE | TRUE | TRUE |
| Literal “two quotient maps” | FALSE | TRUE | FALSE |

Let \(s=u_{12}\), let \(B=(b_{ij})\) be the recoordinatized layer-2 matrix, \(Z=C^{(3)}\), and \(H=ZB=(h_{ij})\). The actual residual is

\[
R_p
=H
\begin{pmatrix}1&\beta\\0&s\end{pmatrix}
=
\begin{pmatrix}
h_{00}&\beta h_{00}+s h_{01}\\
h_{10}&\beta h_{10}+s h_{11}
\end{pmatrix}.
\]

For the center \(C=\{s,b_{00},b_{10}\}\), every monomial contains exactly one center variable. Hence A1 and A2 hold. Under the boost \(b_{00},b_{10}\mapsto s b_{00},s b_{10}\), every entry acquires an exact factor \(s\), proving A3.

If the second edge is incorrectly quotiented, \(s\mapsto1\). Then, after setting the center to zero, entry \((0,1)\) leaves

\[
b_{01}z_{00}+b_{11}z_{01}\neq0,
\]

which also obstructs divisibility in A3.

## Architecture verdict

Needs-carrying under the current `IsRealBranch`/`foldB` interface.

More precisely, the needed invariant is weighted b-chain compatibility, not merely boost-readiness at one center. `foldB p` records only the dominant monomial \(u_{11}\); it does not encode the non-dominant ratio \(b_2/b_1=u_{12}\).

There is an exact countermodel with the same full-support Deg1 property and the same scalar `foldB`:

\[
R_{\mathrm{bad}}
=ZB
\begin{pmatrix}1&\beta\\ \gamma&s\end{pmatrix}.
\]

It is exactly degree one in the full \(B\)-block, but center-zeroing leaves

\[
\gamma(b_{01}z_{00}+b_{11}z_{01}),
\]

so it is not boost-ready. This corresponds to omitting the Schur preparation; the current coarse shear predicate admits such an identity/unprepared shear.

Per edge:

- The first case2 \(\delta=1\) step must establish the Schur-prepared weighted form.
- The second case2 step is \(\delta=0\); it only specializes \(\Delta\mapsto u_{12}\) and cannot create missing divisibility.
- Rollover is identity and merely preserves the property.
- The case1(1) step consumes boost-readiness to obtain exact division; it does not derive it from full-support Deg1.

Thus either carry a weighted invariant, or strengthen `IsRealBranch` to pin the exact canonical Q/Schur shear. With that stronger provenance, it could instead become a derived theorem.

A suitable maintenance statement is:

```lean
theorem bChainCompatible_step
    (hbc : BChainCompatible d e p)
    (hcan : CanonicalQSchurStep d p ed) :
    BChainCompatible d e (p.extend ed)
```

Then `realBranch_boostReady_case11` is a corollary of `BChainCompatible`.

## SymPy script run

```python
import sympy as sp

u11,u12,beta,gamma = sp.symbols('u11 u12 beta gamma')
b00,b01,b10,b11 = sp.symbols('b00 b01 b10 b11')
z00,z01,z10,z11 = sp.symbols('z00 z01 z10 z11')
Delta = sp.symbols('Delta')
B = sp.Matrix([[b00,b01],[b10,b11]])
Z = sp.Matrix([[z00,z01],[z10,z11]])
C = (u12,b00,b10)
S = (b00,b01,b10,b11)
allvars = (u11,u12,beta,gamma,*S,z00,z01,z10,z11)

def degs(f, xs):
    return [sum(m) for m in sp.Poly(sp.expand(f), *xs).monoms()]

def checks(R):
    fs = list(R)
    a1 = all(sp.expand(f).subs(
        {x:0 for x in C}, simultaneous=True) == 0 for f in fs)
    a2 = all(max(degs(f,C), default=0) <= 1 for f in fs)
    pulled = [sp.expand(f.subs(
        {b00:u12*b00,b10:u12*b10}, simultaneous=True)) for f in fs]
    a3 = all(
        sp.expand(f.subs(u12,0)) == 0 and
        bool(sp.cancel(f/u12).is_polynomial(*allvars))
        for f in pulled)
    return a1,a2,a3

Qinv = sp.Matrix([[1,beta],[0,1]])
R1 = sp.expand(Z*B*sp.diag(1,Delta)*Qinv)
R_actual = sp.expand(R1.subs(Delta,u12))
R_literal = sp.expand(R1.subs(Delta,1))
R_bad = sp.expand(Z*B*sp.Matrix([[1,beta],[gamma,u12]]))

print('R_actual =', R_actual)
print('actual A1,A2,A3 =', checks(R_actual))
print('R_literal =', R_literal)
print('literal A1,A2,A3 =', checks(R_literal))
print('literal center-zero witness =',
      sp.expand(R_literal[0,1]).subs(
          {x:0 for x in C}, simultaneous=True))
print('bad full-support degree sets =',
      [set(degs(f,S)) for f in list(R_bad)])
print('bad A1,A2,A3 =', checks(R_bad))
print('bad center-zero witness =',
      sp.expand(R_bad[0,0]).subs(
          {x:0 for x in C}, simultaneous=True))

Sidx,J = 1,0
trace=[]
for edge in ('case2','case2','rollover','case11'):
    trace.append((Sidx,J,edge,int(J == 0)))
    if edge == 'case2':
        J += 1
    elif edge == 'rollover':
        Sidx,J = Sidx+1,0
print('trace =', trace)

assert checks(R_actual) == (True,True,True)
assert checks(R_literal) == (False,True,False)
assert all(set(degs(f,S)) == {1} for f in list(R_bad))
assert checks(R_bad)[0] is False
assert [x[3] for x in trace] == [1,0,0,1]
print('PASS')
```