import sympy as sp, random
random.seed(7)
# deepestPoint(firstLayer) = U·[I_r|0], U : (H0)×r rank r (from block_elimination, B=U·V).
# Columns: first r = U, tail = 0. So A = [[U_top],[U_bot]] | 0  (in r⊕(a-r) rows).
# A11 = U_top (top r×r of U). CLAIM (controller): rank-r cols first ⟹ A11 invertible. CHECK:
# U is rank r (r independent columns). Is its TOP r×r block necessarily invertible? NO.
fails=0; tot=0
for _ in range(8):
    a0 = 1  # tail rows
    r = 1
    # U : (r+a0)×r, rank r. Construct a rank-r U whose top r×r block is SINGULAR:
    # e.g. r=1: U = [[0],[1]] is rank 1 but top block [0] singular.
    U = sp.Matrix([[0],[1]])  # rank 1, top-left 1×1 block = [0] singular
    if U.rank()!=r: continue
    A11 = U[0:r, 0:r]
    tot+=1
    if A11.det()==0: fails+=1
print(f"deepestPoint corner U=[[0],[1]]: A11 singular in {fails}/{tot} → controller's 'rank-r cols first ⟹ A11 invertible' is FALSE in general")
# But: CAN U be CHOSEN with A11 invertible? U rank r ⟹ some r rows independent ⟹ permute to top.
U = sp.Matrix([[0],[1]])
# row-permute: swap rows → [[1],[0]], top block [1] invertible. So achievable by re-choosing U (row perm).
print("Achievable by row-permuting U (rank-r ⟹ r independent rows ⟹ permute to top): YES, but it's a CHOICE/strengthening, not automatic.")
