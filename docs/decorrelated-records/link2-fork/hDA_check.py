import sympy as sp
print("="*78)
print("hDA QUESTION: is deepBlkA s = (reindex(w s)).toBlocks11 (leading rxr) invertible,")
print("given IsDeepLayers (rank(w s)=r + boundary frame conditions)?")
print("="*78)
print()
print("--- INTERIOR layers (0<s, s+1<L): w s = diag(E_r, 0) EXACTLY (IsDeepLayers cond 3).")
print("    toBlocks11 = I_r (the E_r corner).  det = 1.  hDA HOLDS trivially for interior.")
print()
# Interior: w s = [[I_r,0],[0,0]] (after the threshold reindex this IS diag(E_r,0)).
r=2; m=3; n=3
W_int = sp.Matrix(m,n, lambda i,j: 1 if (i==j and i<r) else 0)
B11_int = W_int[:r,:r]
print("   interior toBlocks11 =", B11_int.tolist(), " det =", B11_int.det())
print()
print("--- BOUNDARY layer 0 (s=0, L>=2): cond 4 = last (H1 - r) COLUMNS vanish; rank = r.")
print("    So w0 = [ C | 0 ] with C an (H0 x r) block of rank r (the nonzero columns).")
print("    toBlocks11 = TOP-LEFT rxr of w0 = top r rows of C.  Is THIS invertible?")
print("    NOT forced by rank(w0)=r alone: the rank-r of C could live in the BOTTOM rows.")
# Witness: a rank-r w0 with cols>=r zero, but top rxr singular.
# C is H0 x r, rank r, but top r rows singular: put the independent rows at the bottom.
# e.g. H0=3, r=2: C = [[1,0],[0,0],[0,1]] -> rank 2, but top 2x2 = [[1,0],[0,0]] SINGULAR.
C_bad = sp.Matrix([[1,0],[0,0],[0,1]])
W0_bad = C_bad.row_join(sp.zeros(3, n-r))   # [C | 0], 3x3
print()
print("   WITNESS w0_bad = [C|0] =", W0_bad.tolist())
print("     rank(w0_bad) =", W0_bad.rank(), " (= r, satisfies IsDeepLayers cond 2)")
print("     cols>=r zero:", all(W0_bad[i,j]==0 for i in range(3) for j in range(r,n)), "(satisfies cond 4)")
print("     toBlocks11 (top-left 2x2) =", W0_bad[:r,:r].tolist(), " det =", W0_bad[:r,:r].det())
print("     => deepBlkA 0 SINGULAR for this IsDeepLayers point => hDA0 FAILS.")
print()
print("CONCLUSION: hDA is NOT forced by the CURRENT IsDeepLayers.  An obstruction witness exists.")
print("            (rank-r with the pivot rows not at the top.)  This IS the (1a) gap.")

print()
print("="*78)
print("(1a) STRENGTHENING: is hDA ACHIEVABLE without breaking IsDeepLayers / the loss?")
print("="*78)
print("The deepest point is built (deepestPoint_exists) from a rank-r factorization of B.")
print("Layer 0 = U0 where U0 is H0 x r (rank r), padded.  The (1a) move: permute ROWS of U0")
print("(left-multiply by a permutation P) to bring r independent rows to the top.")
print()
print("KEY: layer 0 is the FIRST layer.  In the product B = w0 . w1 ... w_{L-1}, a ROW permutation")
print("of w0 permutes the ROWS of the whole product B' = P.w0.w1... = P.B.")
print("BUT the loss is frobSq(prod - B) at the FIBRE; the deepest point is IN the fibre (prod=B).")
print("A row-permutation P of w0 changes prod to P.B != B  -- it does NOT stay in the fibre")
print("UNLESS we also permute the OUTPUT, i.e. it changes which B we hit.")
print()
print("RESOLUTION (the actual (1a)): the permutation is absorbed into the GAUGE, not the data.")
print("The fibre / optimalSet is invariant under the GL-gauge w_s -> g_{s-1}^{-1} w_s g_s.")
print("A row-permutation of w0 paired with the SAME permutation on the col-frame of the")
print("PRECEDING gauge (here the boundary: output frame) is a gauge move -> SAME point of optimalSet,")
print("SAME loss, SAME rank.  And it brings the pivot rows of w0 to the top => leading rxr invertible.")
print()
# Verify: for ANY rank-r C (H0 x r), there's a row-permutation making top rxr invertible.
import itertools, sympy as sp
def can_make_top_invertible(C):
    H0 = C.rows; r = C.cols
    # exists a choice of r rows (a subset) that is invertible; if so a permutation brings them to top.
    for rows in itertools.combinations(range(H0), r):
        sub = C[list(rows), :]
        if sub.det() != 0:
            return True, rows
    return False, None
tests = [
    sp.Matrix([[1,0],[0,0],[0,1]]),       # the bad one
    sp.Matrix([[0,0],[1,0],[0,1]]),       # pivots at bottom
    sp.Matrix([[1,2],[2,4],[0,1]]),       # row0,row1 dependent
]
for C in tests:
    ok, rows = can_make_top_invertible(C)
    print(f"   C={C.tolist()} rank={C.rank()} -> can pick invertible r-row subset: {ok} (rows {rows})")
print()
print("THEOREM (always achievable): a rank-r matrix C (H0 x r) ALWAYS has r linearly independent")
print("ROWS (row rank = col rank = r), so SOME r-row subset is invertible => a row-permutation")
print("brings them to the top.  No obstruction.  hDA0 is dischargeable via the (1a) gauge move.")
