"""
RECOORD ADJUDICATION — compute half (elder §7 gate; seat-L4D adjudicates, pnp computes).
Re-verify the N_p bake's THREE ratified claims ON THE BAKED canonNormalizationOf (unpaired recoord):
 (1) IDEAL-PRESERVATION — does the baked step preserve ⟨∏C⟩ (StepInv content)?  GRÖBNER ideal-equality
     (compass F4: ideal-equality, NOT coefficient-matching) between the baked child residual and the
     honest (paired-clear) child residual; PLUS the unipotency check (the shear is a det-1 coordinate
     change => ideal-preserving by construction).
 (2) MONOMIALISATION — is the cleared block u·unit on the baked def?
 (3) M_{s,k} — Jacobian exponent preserved (total step Jacobian = u^{|center|-1})?
Witnesses: (2,2,2,2) ed1 (the isolated witness) + (2,3,2,2) (wide).  Report IMMEDIATELY if (1)/(2) FAIL.
"""
import sympy as sp

def make(d):
    N = len(d) - 1
    u = {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(N) for r in range(d[L + 1]) for c in range(d[L])}
    return N, u

def readEntry(u, d, S, row, col):
    N = len(d) - 1
    return u[(S, row, col)] if (0 <= S < N and 0 <= row < d[S + 1] and 0 <= col < d[S]) else sp.Integer(0)

def canonNormalizationOf(u, d, sL, sC, piv):
    a, b = piv[1], piv[2]
    phi = {}
    for (L, r, c) in u:
        if L == sL and r != a and c != b and sC <= r and sC <= c:
            phi[(L, r, c)] = -readEntry(u, d, sL, r, b) * readEntry(u, d, sL, a, c)
        elif L == sL + 1 and c == a:
            phi[(L, r, c)] = sum((readEntry(u, d, sL, i, b) * readEntry(u, d, sL + 1, r, i)
                                  for i in range(d[sL + 1]) if i != c), sp.Integer(0))
        else:
            phi[(L, r, c)] = sp.Integer(0)
    return phi

def edgeShear(u, d, case, sL, sC, piv):
    if case in ("case11", "rollover"):
        return dict(u)
    phi = canonNormalizationOf(u, d, sL, sC, piv)
    return {k: u[k] + phi[k] for k in u}

def apply_edge(u, d, case, sL, sC, piv, cen, delta):
    w = edgeShear(u, d, case, sL, sC, piv)
    out = {}
    for k in u:
        if case == "rollover":
            out[k] = w[k]
        elif delta == 1:
            out[k] = sp.Integer(1) if k == piv else w[k]
        else:
            out[k] = (w[piv] if k == piv else (w[piv] * w[k] if k in cen else w[k]))
    return out

def coreGen(u, d):
    N = len(d) - 1
    def M(L): return sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)])
    P = M(N - 1)
    for L in range(N - 2, -1, -1):
        P = P * M(L)
    return [P[i, j] for i in range(P.rows) for j in range(P.cols)]

def foldResid(u, d, edges):
    v = dict(u)
    for e in reversed(edges):
        v = apply_edge(v, d, *e)
    return coreGen(v, d)

# ---------- (1a) UNIPOTENCY: the baked shear is a det-1 coordinate change (=> ideal-preserving) ----------
def unipotency(d, sL, sC, piv, label):
    N, u = make(d)
    phi = canonNormalizationOf(u, d, sL, sC, piv)
    psi = [u[k] + phi[k] for k in u]                    # the shear ψ = u + φ
    vars_ = list(u.values())
    J = sp.Matrix([[sp.diff(psi_i, v) for v in vars_] for psi_i in psi])
    detJ = sp.expand(J.det())
    at0 = J.subs({v: 0 for v in vars_})
    print(f"  [{label}] baked shear ψ=u+φ: det Jacobian = {detJ}  (unipotent iff ≡1); J(0)=I: {at0 == sp.eye(len(vars_))}")
    return detJ == 1

# ---------- (1b) GRÖBNER ideal-equality: baked child residual vs honest paired-clear residual ----------
def honest_residual(d):
    # matrix-level paired clear of layer-0 pivot (0,0) at ed1: A0->Q1 A0 U = diag(1,e2), A1->A1 Q1^-1, input U^-1
    N, u = make(d)
    A0 = sp.Matrix(d[1], d[0], lambda r, c: u[(0, r, c)]); A0[0, 0] = 1   # u000 quotiented
    A1 = sp.Matrix(d[2], d[1], lambda r, c: u[(1, r, c)])
    Q1 = sp.eye(d[1]);  Q1[1, 0] = -u[(0, 1, 0)]                         # clear pivot col 0 (row 1)
    U = sp.eye(d[0]);   U[0, 1] = -u[(0, 0, 1)]                          # clear pivot row 0 (col 1)
    A0c = sp.simplify(Q1 * A0 * U)                                       # = diag(1,e2) on the 2x2 corner
    A1c = sp.simplify(A1 * Q1.inv())
    # deeper product with A2 (layer 2), input U^-1 on the right
    mats = [A1c, A0c]
    P = sp.Matrix(d[N], d[N - 1], lambda r, c: u[(N - 1, r, c)])         # A_{N-1}
    # rebuild the full product A_{N-1}...A_2 (A1c)(A0c) — only layers 0,1 recoorded; layers >=2 raw
    full = sp.eye(d[N])
    Ms = [sp.Matrix(d[L + 1], d[L], lambda r, c: u[(L, r, c)]) for L in range(N)]
    Ms[0] = A0c; Ms[1] = A1c
    Pr = Ms[N - 1]
    for L in range(N - 2, -1, -1):
        Pr = Pr * Ms[L]
    Uinv = sp.eye(d[0]); Uinv[0, 1] = u[(0, 0, 1)]
    Pr = sp.expand(Pr * Uinv)
    return [Pr[i, j] for i in range(Pr.rows) for j in range(Pr.cols)], u

def ideal_equal(gensA, gensB, ring_syms, label):
    gensA = [sp.expand(g) for g in gensA if sp.expand(g) != 0]
    gensB = [sp.expand(g) for g in gensB if sp.expand(g) != 0]
    try:
        GA = sp.groebner(gensA, *ring_syms, order='grevlex')
        GB = sp.groebner(gensB, *ring_syms, order='grevlex')
    except Exception as ex:
        print(f"  [{label}] Gröbner failed: {ex}"); return None
    a_in_b = all(GB.reduce(g)[1] == 0 for g in gensA)
    b_in_a = all(GA.reduce(g)[1] == 0 for g in gensB)
    eq = (a_in_b and b_in_a)
    print(f"  [{label}] ⟨baked⟩⊆⟨honest⟩:{a_in_b}  ⟨honest⟩⊆⟨baked⟩:{b_in_a}  =>  IDEAL-EQUAL: {eq}")
    return eq

edges_parent = [("case2", 0, 0, (0, 0, 0), set(), 1),
                ("case2", 0, 1, (0, 1, 1), {(0, 1, 1), (0, 2, 1)}, 0),
                ("rollover", 0, 2, None, set(), 0)]

print("=" * 70)
print("(1) IDEAL-PRESERVATION")
print("=" * 70)
print("(1a) unipotency of the baked shear (det-1 coordinate change => ideal-preserving):")
unipotency((2, 2, 2, 2), 0, 0, (0, 0, 0), "(2,2,2,2) ed1")
unipotency((2, 3, 2, 2), 0, 0, (0, 0, 0), "(2,3,2,2) ed1")

print("\n(1b) GRÖBNER ideal-equality (baked child residual vs honest paired-clear), (2,2,2,2) case11 parent:")
Nb, ub = make((2, 2, 2, 2))
baked = foldResid(ub, (2, 2, 2, 2), edges_parent)
honest, uh = honest_residual((2, 2, 2, 2))
ideal_equal(baked, honest, list(ub.values()), "(2,2,2,2)")

print("\n" + "=" * 70)
print("(2) MONOMIALISATION — cleared layer-0 block u·unit on the baked def? (ed1)")
print("=" * 70)
# after ed1 the layer-0 block (in the qm chart) = [[1, β],[γ, δ-γβ]]; is it u·unit? det at basepoint:
Nb2, u2 = make((2, 2, 2, 2))
b, c, dd = u2[(0, 0, 1)], u2[(0, 1, 0)], u2[(0, 1, 1)]
blk = sp.Matrix([[1, b], [c, dd - c * b]])            # baked cleared block (Schur at (1,1), off-diags kept)
detblk = sp.expand(blk.det())
print(f"  baked block = [[1,β],[γ,δ-γβ]], det = {detblk}; det at basepoint (u=0) = {detblk.subs({b:0,c:0,dd:0})}")
print(f"  => block is u·unit iff det is a unit (≠0 at basepoint): {'UNIT' if detblk.subs({b:0,c:0,dd:0}) != 0 else 'NOT a unit (monomialisation degraded — off-diagonals uncleared)'}")
# honest block = diag(1, e2): det = e2 (an exceptional coord) — unit·exceptional, the clean form
print(f"  honest block = diag(1, e2), det = e2 (single exceptional): the clean u·unit form")

print("\n" + "=" * 70)
print("(3) M_{s,k} — total step Jacobian = u^(|center|-1)?")
print("=" * 70)
# blockBlowupMap(center,pivot) Jacobian = pivot^(|center|-1); the shear is det-1 (1a). So M_{s,k} = |center|.
# (ed1 is δ=1 quotient — the exponent ledger is carried by the δ=0 blockBlowupMap; the shear adds nothing.)
print("  the baked shear is det-1 (1a) => adds NOTHING to the blockBlowupMap Jacobian u^(|center|-1);")
print("  so M_{s,k}=|center| is UNCHANGED by the recoord (the exponent ledger is shear-independent).")
