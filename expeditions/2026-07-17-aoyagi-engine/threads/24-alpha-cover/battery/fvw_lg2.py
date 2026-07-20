#!/usr/bin/env python3
# pnp-full (thread 24): Q3 refined -- the cross-layer Rg keeps a COMPENSATION on layer S+1, so the
# JOINT map over (layer S, layer S+1) may be a bijection (det != 0) even though the layer-S piece
# alone zeroes the pivot row. Likewise Lg's honest form couples back to earlier layers. Compute the
# EXACT joint Jacobian det. And test the Aoyagi-order (beta-first) div-free candidate. Exact sympy.
import sympy as sp

def two_layers(mS, mMid, mNext, tagA='a', tagB='b'):
    A = {(i, j): sp.Symbol(f'{tagA}{i}{j}', real=True) for i in range(mS) for j in range(mMid)}
    B = {(i, j): sp.Symbol(f'{tagB}{i}{j}', real=True) for i in range(mMid) for j in range(mNext)}
    return A, B

def joint_jac_det(A0, B0, A1, B1, mS, mMid, mNext):
    ca = [(i, j) for i in range(mS) for j in range(mMid)]
    cb = [(i, j) for i in range(mMid) for j in range(mNext)]
    after = sp.Matrix([sp.together(A1[c]) for c in ca] + [sp.together(B1[c]) for c in cb])
    src = [A0[c] for c in ca] + [B0[c] for c in cb]
    return sp.factor(sp.simplify(after.jacobian(src).det()))

def rg_crosslayer(A, B, mS, mMid, mNext, c=0):
    """clear layer-S pivot ROW (col op on A, cols j>c) + compensate layer S+1 (row op on B, row c)."""
    A1 = dict(A); B1 = dict(B); p = A[(c, c)]
    f = {j: A[(c, j)] / p for j in range(c + 1, mMid)}
    for j in range(c + 1, mMid):
        for i in range(mS):
            A1[(i, j)] = A[(i, j)] - f[j] * A[(i, c)]
    for k in range(mNext):
        B1[(c, k)] = B[(c, k)] + sum(f[j] * B[(j, k)] for j in range(c + 1, mMid))
    return A1, B1

def lg_leftcompensate(Aprev, A, mPrev, mS, mMid, c=0):
    """Lg honest: clear layer-S pivot COLUMN (row op on A, rows i>c) + compensate layer S-1 (col op on
       Aprev). This is the LEFT-multiplier propagating back. Test joint (layer S-1, layer S)."""
    Ap1 = dict(Aprev); A1 = dict(A); p = A[(c, c)]
    f = {i: A[(i, c)] / p for i in range(c + 1, mS)}
    for i in range(c + 1, mS):
        for j in range(mMid):
            A1[(i, j)] = A[(i, j)] - f[i] * A[(c, j)]
    # compensate layer S-1 (columns): col_c(Aprev) absorbs, col_i += f_i * col_c ... transpose of Rg
    for k in range(mPrev):
        Ap1[(k, c)] = Aprev[(k, c)] + sum(f[i] * Aprev[(k, i)] for i in range(c + 1, mS))
    return Ap1, A1

if __name__ == "__main__":
    print("### CROSS-LAYER Rg: joint (layer S, layer S+1) Jacobian det ###")
    for (mS, mMid, mNext) in [(2, 2, 2), (3, 3, 3), (3, 3, 4), (2, 3, 2), (4, 3, 4)]:
        A, B = two_layers(mS, mMid, mNext)
        A1, B1 = rg_crosslayer(A, B, mS, mMid, mNext)
        d = joint_jac_det(A, B, A1, B1, mS, mMid, mNext)
        # also record which layer-S cells got zeroed
        zeroed = [(0, j) for j in range(1, mMid) if sp.simplify(A1[(0, j)]) == 0]
        print(f"  layers {mS}x{mMid} , {mMid}x{mNext}:  joint |det Jac| = {d}   (pivot-row zeroed in A: {zeroed})")
    print()
    print("### Lg honest (pivot-col clear + compensate layer S-1): joint (S-1, S) Jacobian det ###")
    for (mPrev, mS, mMid) in [(2, 2, 2), (3, 3, 3), (2, 3, 3), (4, 4, 3)]:
        Aprev = {(i, j): sp.Symbol(f'p{i}{j}', real=True) for i in range(mPrev) for j in range(mS)}
        A = {(i, j): sp.Symbol(f'a{i}{j}', real=True) for i in range(mS) for j in range(mMid)}
        Ap1, A1 = lg_leftcompensate(Aprev, A, mPrev, mS, mMid)
        # joint jacobian over (Aprev cells, A cells)
        ca = [(i, j) for i in range(mPrev) for j in range(mS)]
        cb = [(i, j) for i in range(mS) for j in range(mMid)]
        after = sp.Matrix([sp.together(Ap1[c]) for c in ca] + [sp.together(A1[c]) for c in cb])
        src = [Aprev[c] for c in ca] + [A[c] for c in cb]
        d = sp.factor(sp.simplify(after.jacobian(src).det()))
        zeroed = [(i, 0) for i in range(1, mS) if sp.simplify(A1[(i, 0)]) == 0]
        print(f"  layers {mPrev}x{mS} , {mS}x{mMid}:  joint |det Jac| = {d}   (pivot-col zeroed in A: {zeroed})")
