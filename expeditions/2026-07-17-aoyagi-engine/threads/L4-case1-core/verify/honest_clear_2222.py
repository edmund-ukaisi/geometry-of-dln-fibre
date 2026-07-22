"""
Is Aoyagi's UNDERLYING theorem true on d=(2,2,2,2)? i.e. after a FAITHFUL clear of layer 0
(Schur + L/U pivot-row/col zeroing + deeper recoordinatization A_1 -> A_1*Q^{-1}), is the layer-1
residual degree-1 on the boost center?

We build M = A_2 * A_1 * A_0 and clear A_0's pivot (0,0) HONESTLY, expressing everything in the
resolution CHART coords:
  - A_1' = A_1 * L^{-1}  (L clears the pivot COLUMN; recoordinatizes the DEEPER matrix)  -> coords w
  - L*A_0*U = diag(1, e2)   (e2 = Schur second-pivot exceptional coord)
  - M = A_2 * A_1' * diag(1,e2) * U^{-1},   U^{-1} = [[1, s],[0,1]]  (s = pivot-row coord of A_0)
Boost pivot = e2 (the reused second-pivot exceptional coord). center = {e2} + {w col 0}.
We test with and without the U^{-1} input-change factor (the U-clear recoordinatizes the FIBRE B,
which may or may not belong in the residual family).
"""
import sympy as sp

D = 2
# layer-2 (untouched), recoordinatized layer-1 (w), second-pivot exceptional e2, pivot-row coord s
A2 = sp.Matrix([[sp.Symbol(f"u_2{r}{c}") for c in range(D)] for r in range(D)])
w  = sp.Matrix([[sp.Symbol(f"w_1{r}{c}") for c in range(D)] for r in range(D)])
e2 = sp.Symbol("e2")            # second-pivot exceptional (the boost pivot)
s  = sp.Symbol("s")             # pivot-row coord of A_0 (u_001), moved into U on the input side
Uinv = sp.Matrix([[1, s], [0, 1]])
D0 = sp.diag(1, e2)

def checks(M, center, extra):
    fs_all = [M[i, j] for i in range(D) for j in range(D)]
    A1 = all(sp.expand(f.subs({c: 0 for c in center})) == 0 for f in fs_all)
    def maxdeg(f, xs):
        fs = sp.expand(f).free_symbols
        if not any(x in fs for x in xs):
            return 0
        return max(sum(m) for m in sp.Poly(sp.expand(f), *xs).monoms())
    A2f = all(maxdeg(f, center) <= 1 for f in fs_all)
    A3 = all(sp.expand(sp.expand(f.diff(x)).subs(center[0], 0)) == 0
             for f in fs_all for x in extra)   # extra coeff carries pivot=center[0]=e2
    return A1, A2f, A3, fs_all

center = [e2, w[0, 0], w[1, 0]]    # boost pivot e2 + partial block (col 0)
extra  = [w[0, 1], w[1, 1]]        # extra block (col 1)

print("=== WITH the U^{-1} input-change factor: M = A2 * w * diag(1,e2) * Uinv ===")
M1 = A2 * w * D0 * Uinv
A1, A2f, A3, fs = checks(M1, center, extra)
for i, f in enumerate(fs):
    print(f"  M[{i}] =", sp.expand(f))
print("A1,A2,A3 =", (A1, A2f, A3), " BOOST-READY:", A1 and A2f and A3)

print("\n=== WITHOUT the U^{-1} factor: M = A2 * w * diag(1,e2) ===")
M2 = A2 * w * D0
A1b, A2b, A3b, fsb = checks(M2, center, extra)
for i, f in enumerate(fsb):
    print(f"  M[{i}] =", sp.expand(f))
print("A1,A2,A3 =", (A1b, A2b, A3b), " BOOST-READY:", A1b and A2b and A3b)
