"""
THE SCRAMBLED-e HEDGE (closes the one open branch of the elder's ruling; seat-L4D Codex hedge
boostready-beta-feasibility-answer.md): does the fully-unfolded concrete fold force the case11 b-chain /
boost split WITHOUT the canonFlatten root base — i.e. is the ∀e statement true as framed (SURVIVES-∀e),
or does a linear-but-scrambling e kill it (KILLED-BY-e, re-bake fork forced)?

e-MODEL (exact, matches the Lean `coreGen d e u = mult (e u)`): e is a LINEAR homeomorphism
Fin(flatDim) -> Tuple; coreGen_e(u) = entries of mult(reshape(E . u)), E the flatDim x flatDim scramble.
foldResid_e(node)(u) = coreGen_e(stepMaps(u)) = mult(reshape(E . stepMaps(u))).  The fold step maps
(blockBlowupMap/quotient . canonShearOf) and the oracle center/pivot are e-INDEPENDENT (flat-coord/
combinatorial); only coreGen's base reads e.

FEASIBILITY: validated below on the (1,1,1) Fbad witness (e=[[1,1],[0,1]] => coreGen_0 = u0*u1 + u1^2).
The scrambler breaks the BASE degree-1 (coreGen_e not degree-1 on the block) — which is UPSTREAM of the
shear, so it kills the boost split regardless of canonShearOf-vs-faithful-N_p. We exhibit the surviving
non-degree-1 monomial at the (2,2,2,2) case11 boost parent.
"""
import sympy as sp

# ---------- (0) feasibility: validate the e-model on the (1,1,1) Fbad witness ----------
print("=== (0) e-model validation on the (1,1,1) Fbad witness ===")
u0, u1 = sp.symbols('u0 u1')                          # flat coords: A_0 entry, A_1 entry (both 1x1)
# canonical: A_0=[[u0]], A_1=[[u1]]; coreGen = A_1*A_0 = u1*u0
E_fbad = sp.Matrix([[1, 1], [0, 1]])                  # the scrambling flatten (unipotent)
x = E_fbad * sp.Matrix([u0, u1])                      # e . (u0,u1) = (u0+u1, u1)
A0_111 = sp.Matrix([[x[0]]]); A1_111 = sp.Matrix([[x[1]]])
coreGen_e_111 = sp.expand((A1_111 * A0_111)[0, 0])
print("  coreGen_e (1,1,1) =", coreGen_e_111, " (expect u0*u1 + u1**2)  MATCH:",
      sp.expand(coreGen_e_111 - (u0 * u1 + u1**2)) == 0)
print("  => the e-model reproduces the 9th-catch kill-witness; it carries a non-canonical e EXACTLY.\n")

# ---------- (2,2,2,2) fold to the case11 boost parent, under a SCRAMBLING e ----------
LAYERS, D = 3, 2
u = {(L, r, c): sp.Symbol(f"u{L}{r}{c}") for L in range(LAYERS) for r in range(D) for c in range(D)}
order = [(L, r, c) for L in range(LAYERS) for r in range(D) for c in range(D)]   # 12 flat coords

def stepmaps_to_boostparent(uu):
    """canonShearOf fold to the (2,2,2,2) boost parent: qm_ed1 (ed2,ed3 = identity)."""
    out = dict(uu)
    # ed1 = case2 delta1, pivot (0,0,0), canonShearOf(root): (0,1,1) -> u011 - u010*u001
    out[(0, 0, 0)] = sp.Integer(1)
    out[(0, 1, 1)] = uu[(0, 1, 1)] - uu[(0, 1, 0)] * uu[(0, 0, 1)]
    return out

def coreGen_e(uu, E):
    """mult(reshape(E . flatvec(uu))) entries."""
    xvec = E * sp.Matrix([uu[c] for c in order])
    xf = {order[i]: xvec[i] for i in range(len(order))}
    A = [sp.Matrix(D, D, lambda r, c: xf[(L, r, c)]) for L in range(LAYERS)]
    M = A[2] * A[1] * A[0]
    return [M[i, j] for i in range(D) for j in range(D)]

def foldResid_e(uu, E):
    return coreGen_e(stepmaps_to_boostparent(uu), E)

# boost geometry (from the real branch): pivot (0,1,1), center = {pivot} u layer-1 col-0, extra = col-1
pivot = (0, 1, 1)
partial = [(1, 0, 0), (1, 1, 0)]
extra = [(1, 0, 1), (1, 1, 1)]
center = [pivot] + partial

def boost_checks(resid):
    supp0 = {u[c]: 0 for c in center}
    A1 = all(sp.expand(f.subs(supp0)) == 0 for f in resid)                         # vanish at center=0
    def maxdeg(f, xs):
        fs = sp.expand(f).free_symbols
        return 0 if not any(x in fs for x in xs) else max(sum(m) for m in sp.Poly(sp.expand(f), *xs).monoms())
    A2 = all(maxdeg(f, [u[c] for c in center]) <= 1 for f in resid)                # deg<=1 on center
    # per-layer degree of layer 1 (the support layer) — scrambling e injects deg-2 here
    deg_layer1 = max(maxdeg(f, [u[(1, r, c)] for r in range(D) for c in range(D)]) for f in resid)
    return A1, A2, deg_layer1

# --- canonical e (identity reindexing): the reference ---
E_id = sp.eye(12)
rid = [sp.expand(f) for f in foldResid_e(u, E_id)]
print("=== (2,2,2,2) boost parent, CANONICAL e (identity) ===")
a1, a2, dl1 = boost_checks(rid)
print(f"  A1(vanish@center=0)={a1}  A2(deg<=1 on center)={a2}  max deg in layer-1 coords={dl1}")

# --- SCRAMBLING e chosen to inject a DEGREE-2-IN-EXTRA-BLOCK term (the IRREPARABLE kill) ---
# BoostSplit needs each EXTRA-block coord to appear as u_pivot*(beta*u_extra): u_pivot is LAYER-0, so any
# BoostSplit term is degree <=1 in layer-1. The faithful recoord is LINEAR in layer 1 (preserves layer-1
# degree). So a monomial DEGREE-2 in the extra block (both factors extra, e.g. u101*u111 or u101^2) can
# NEVER be a BoostSplit term and is NOT removable by any linear layer-1 recoord => it KILLS the boost split
# irreparably, independent of canonShearOf-vs-faithful-N_p.
# e: u_(0,1,0) += u_(1,0,1). Then A_0[1][0] = u010 + u101, and A_1[i][1]=u_(1,i,1) (extra) multiplies it in
# the product => u_(1,i,1)*u101 = EXTRA*EXTRA (degree 2 in the extra block).
extra_syms = [u[c] for c in extra]
def maxdeg_extra(f):
    fs = sp.expand(f).free_symbols
    return 0 if not any(x in fs for x in extra_syms) else max(sum(m) for m in sp.Poly(sp.expand(f), *extra_syms).monoms())

E_scr = sp.eye(12)
E_scr[order.index((0, 1, 0)), order.index((1, 0, 1))] = 1     # (E.u)_(0,1,0) = u_(0,1,0) + u_(1,0,1)
rscr = [sp.expand(f) for f in foldResid_e(u, E_scr)]
print("\n=== (2,2,2,2) boost parent, SCRAMBLING e (u_(0,1,0) += u_(1,0,1)) ===")
a1s, a2s, dl1s = boost_checks(rscr)
maxext = max(maxdeg_extra(f) for f in rscr)
print(f"  A1(vanish@center=0)={a1s}  A2(deg<=1 on center)={a2s}  max deg in layer-1={dl1s}  "
      f"max deg in EXTRA block={maxext}")
# exhibit a degree-2-in-EXTRA monomial (the irreparable kill-witness), if any
killed = False
for j, f in enumerate(rscr):
    poly = sp.Poly(sp.expand(f), *extra_syms)
    for mono, coeff in poly.terms():
        if sum(mono) >= 2:
            mon = sp.prod([extra_syms[k]**mono[k] for k in range(len(extra_syms))])
            print(f"  resid[{j}]: DEGREE-2-IN-EXTRA monomial {sp.simplify(coeff)} * {mon}  "
                  f"(u_pivot is layer-0 => NOT expressible as u_pivot*(beta*u_extra); irreparable)")
            killed = True
            break
    if killed:
        break

# canonical-e reference: max extra-block degree = 1 (no such term)
maxext_id = max(maxdeg_extra(f) for f in rid)
print(f"\n  canonical-e reference: max deg in EXTRA block = {maxext_id} (degree-1; no extra*extra term)")

print("\nVERDICT:", "KILLED-BY-e" if killed else "no extra*extra term from this scrambler")
if killed:
    print("  A scrambling e produces a residual monomial DEGREE-2 in the extra block. BoostSplit requires")
    print("  every extra-block coord to appear as u_pivot*(beta*u_extra) — degree-1 in layer 1 (u_pivot is")
    print("  layer-0). The faithful recoord is LINEAR in layer 1, so it preserves layer-1 degree and CANNOT")
    print("  reduce a degree-2-in-extra term. So the boost split is FALSE under this e, irreparably, and")
    print("  INDEPENDENTLY of canonShearOf-vs-faithful-N_p. => the ∀e statement is NOT true as framed; the")
    print("  canonFlatten root pin is NECESSARY (the re-bake fork stands).")
