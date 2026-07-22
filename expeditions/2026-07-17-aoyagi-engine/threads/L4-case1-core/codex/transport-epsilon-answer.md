Sandbox note: file creation in `/tmp` was denied as read-only. I read no repository files and ran the fresh script inline.

1. `[computed]` Only `ed1` is nontrivial.

```python
ed1=quot((0,0,0),shear(0,0))
ed2=blow({(0,1,1)},(0,1,1),shear(0,1))
ed3=blow(set(),None,ident())
R=apply(A2*A1*A0,compose(ed1,compose(ed2,ed3)))
pm('literal foldResid',R)
```

```text
ed1 changed coordinates = {'u_0_0_0': 1, 'u_0_1_1': -u_0_0_1*u_0_1_0 + u_0_1_1}
ed2 changed coordinates = {}
ed3 changed coordinates = {}
literal foldResid
  r00 = u_0_1_0*u_1_0_1*u_2_0_0 + u_0_1_0*u_1_1_1*u_2_0_1 + u_1_0_0*u_2_0_0 + u_1_1_0*u_2_0_1
  r01 = -u_0_0_1*u_0_1_0*u_1_0_1*u_2_0_0 - u_0_0_1*u_0_1_0*u_1_1_1*u_2_0_1 + u_0_0_1*u_1_0_0*u_2_0_0 + u_0_0_1*u_1_1_0*u_2_0_1 + u_0_1_1*u_1_0_1*u_2_0_0 + u_0_1_1*u_1_1_1*u_2_0_1
  r10 = u_0_1_0*u_1_0_1*u_2_1_0 + u_0_1_0*u_1_1_1*u_2_1_1 + u_1_0_0*u_2_1_0 + u_1_1_0*u_2_1_1
  r11 = -u_0_0_1*u_0_1_0*u_1_0_1*u_2_1_0 - u_0_0_1*u_0_1_0*u_1_1_1*u_2_1_1 + u_0_0_1*u_1_0_0*u_2_1_0 + u_0_0_1*u_1_1_0*u_2_1_1 + u_0_1_1*u_1_0_1*u_2_1_0 + u_0_1_1*u_1_1_1*u_2_1_1
```

2. `[computed]` Every entry fails `Deg1SupportedOn C`: A1=False, A2=True, A3=False.

```python
pt('literal center C=(d,e,g), pivot=d:',R,[d,e,g],[f,h],d)
```

```text
literal center C=(d,e,g), pivot=d: A1/A2/A3 = (False, True, False)
A1 breaking monomials:
 r00: c*f*u_2_0_0, c*h*u_2_0_1
 r01: -b*c*f*u_2_0_0, -b*c*h*u_2_0_1
 r10: c*f*u_2_1_0, c*h*u_2_1_1
 r11: -b*c*f*u_2_1_0, -b*c*h*u_2_1_1
A2 breaking monomials = {}
A3 breaking coefficients:
 r_i0: c*u_2_i_0 (for f), c*u_2_i_1 (for h)
 r_i1: -b*c*u_2_i_0 (for f), -b*c*u_2_i_1 (for h)
```

Here \(b=u_{0,0,1}\), \(c=u_{0,1,0}\), \(d=u_{0,1,1}\), \(f=u_{1,0,1}\), \(h=u_{1,1,1}\).

3. `[computed]` No single proposed change suffices. A full clear plus the Schur pivot \(s=d-cb\) passes algebraically. A faithful realization additionally uses the deeper recoordinatization.

```python
Q=sp.Matrix([[1,0],[-c,1]])
U=sp.Matrix([[1,-b],[0,1]])
D=(Q*sp.Matrix([[1,b],[c,d]])*U).applyfunc(sp.expand)
```

```text
Q*A0_postquot*U = [[1, 0], [0, -u_0_0_1*u_0_1_0 + u_0_1_1]]
given residual, Schur pivot only: A1/A2/A3 = (False, True, False)
full clear, literal pivot d: A1/A2/A3 = (False, True, False)
full clear + Schur pivot: A1/A2/A3 = (True, True, True)
```

Thus the raw minimum is `(i)+(iii)`. For a product-preserving construction, use the column-clear \(Q\), `(ii)`, and `(iii)`; the row-clear \(U\) is optional for support.

Strictly applying another Gaussian clear after the given shear double-subtracts:

```text
strictly sequential Q*A0_given*U =
[[1, 0], [0, -2*u_0_0_1*u_0_1_0 + u_0_1_1]]
```

It passes only with the artificial pivot \(d-2cb\), so it is not the faithful correction.

4. `[computed]` YES. Let \(B=A_1Q^{-1}=\begin{pmatrix}E&F\\G&H\end{pmatrix}\) be the new independent deeper coordinates and \(s=d-cb\). Then

\[
A_1A_0=B(QA_0)=B
\begin{pmatrix}1&b\\0&s\end{pmatrix}
=BDU^{-1}.
\]

```python
T=(Q*A0_postquot).applyfunc(sp.expand)
Rfaith=(A2*B*T).applyfunc(sp.expand)
print(((A1*Q.inv())*T-A1*A0_postquot).applyfunc(sp.expand).tolist())
pt(..., Rfaith_sigma, [sigma,E,G], [F,H], sigma)
```

```text
faithfulness identity after B=A1*Q^-1 = [[0, 0], [0, 0]]
faithful column-clear/recoord + Schur pivot:
A1/A2/A3 = (True, True, True)
A1 breaking monomials = {}
A2 breaking monomials = {}
A3 breaking coefficient monomials = {}
T - D*U^-1 = [[0, 0], [0, 0]]
```

Final verdict: maps exactly as given are **not boost-ready**. The underlying claim is **true** for the faithful \(Q\)-clear, deeper recoordinatization, and Schur-pivot construction.