"""
THE DECISIVE STRUCTURAL DECOMPOSITION (exact, multi-M).

Chart: A_k = chainA(N_k,W_k,C_{k+1}) = [[I,-N_k],[0,I]] @ [[C_{k+1}],[W_k]]   (row block op)
       C_{k+1} = B_{k+1} chainQ(N_{k+1}) + u R_{k+1}     (interior)
       C_L     = u Rfin                                  (leaf)

We decompose Phi as a NESTED composition and check the per-piece structure:

  STEP A (Schur frames, per boundary, INDEPENDENT): the map
      (B_s, N_s) |-> Cfull_s := B_s @ chainQ(N_s)   [the schurFrame output, T_s x W_s], for each s>=1.
    Each is a function of boundary-s's OWN coords only. Its derivative det = (det K_s)^(r_s+c_s)
    (schurFrameDeriv_det) where K_s is the leading square LDU core of B_s.

  STEP B (radial): add u R_{k+1} into the kept rows. Affine in u, factors u^{minAdm-1}.

  STEP C (chain shear, per boundary): A_k = [[I,-N_k],[0,I]] [C_{k+1};W_k]. Unipotent: det 1.
    This shear COUPLES boundary k's N_k with boundary k+1's Cfull. THIS is the coupling
    genm-mapeq flagged. We verify it is (a) unipotent (det 1 independent of M), (b) the ONLY
    cross-boundary coupling.

KEY CHECK: build Phi two ways and confirm equality, then confirm the chain shear is the unique
non-block-local factor and is det-1 unipotent. If yes -> per-piece factorization HOLDS uniformly.
"""
import sympy as sp
from sympy import symbols, eye, zeros, Matrix, factor, expand, Poly
from perpiece_v2 import chainQ, chainA

def shear_block(N, t, c):
    """[[I_t, -N],[0, I_c]] as a (t+c)x(t+c) matrix (the row block op in chainA)."""
    S = eye(t + c)
    for i in range(t):
        for j in range(c):
            S[i, t + j] = -N[i, j]
    return S

def build_direct(L, M, T, bl, u):
    """The fused chart (ground truth)."""
    C = {}
    C[L] = u * bl[L]['Rfin']
    for k in range(L-1, -1, -1):
        tk1 = T[k+1]; ck = M[k] - tk1
        C[k] = bl[k]['B'] * chainQ(bl[k]['N'], tk1, ck) + u * bl[k]['R']
    A = {}
    for k in range(L):
        tk1 = T[k+1]; ck = M[k] - tk1; mp = M[k+1]
        A[k] = chainA(bl[k]['N'], bl[k]['W'], C[k+1], tk1, ck, mp)
    return A, C

def build_factored(L, M, T, bl, u):
    """Phi via the explicit factor pipeline: Cfull_s (schur) + u R (radial), then shear (chain).
       Returns A (should equal build_direct's A) + the pieces for inspection."""
    # Step A+B: Cfull_{k} = B_k chainQ(N_k) + u R_k  (interior), C_L = u Rfin
    Cfull = {}
    Cfull[L] = u * bl[L]['Rfin']
    schur_out = {}
    for k in range(L):
        tk1 = T[k+1]; ck = M[k] - tk1
        schur_out[k] = bl[k]['B'] * chainQ(bl[k]['N'], tk1, ck)   # pure schur frame, u-free
        Cfull[k] = schur_out[k] + u * bl[k]['R']
    # Step C: A_k = shear_k @ [Cfull_{k+1}; W_k]
    A = {}
    shears = {}
    for k in range(L):
        tk1 = T[k+1]; ck = M[k] - tk1; mp = M[k+1]
        stacked = zeros(tk1 + ck, mp)
        for i in range(tk1):
            for j in range(mp): stacked[i, j] = Cfull[k+1][i, j]
        for i in range(ck):
            for j in range(mp): stacked[tk1 + i, j] = bl[k]['W'][i, j]
        Sh = shear_block(bl[k]['N'], tk1, ck)
        shears[k] = Sh
        A[k] = Sh * stacked
    return A, Cfull, schur_out, shears

def check(label, L, M, T, mk_blocks, NC):
    x = symbols('x0:%d' % NC, real=True); u = x[0]
    bl, used, groups = mk_blocks(x)
    Ad, Cd = build_direct(L, M, T, bl, u)
    Af, Cfull, schur_out, shears = build_factored(L, M, T, bl, u)
    print(f"\n===== {label}: M={M} T={T} =====")
    # (i) MAP equality: factored == direct
    eqA = all(expand(Ad[k] - Af[k]) == zeros(*Ad[k].shape) for k in range(L))
    print(f"   (i) factored chart == fused chart (MAP equality, exact): {eqA}")
    # (ii) chain shears unipotent / det 1, uniform
    detsh = [shears[k].det() for k in range(L)]
    print(f"   (ii) chain shear dets (each must be 1): {detsh}")
    # also: shear is unipotent (I + strictly-upper nilpotent) -> det 1 structurally
    unip = all((shears[k] - eye(shears[k].rows)).is_lower_triangular == False for k in range(L))  # info only
    # (iii) per-boundary schur frame det = (det K_s)^(r_s+c_s) — checked separately in perpiece_full
    return x, u, bl, Ad, Af, schur_out, shears, groups
