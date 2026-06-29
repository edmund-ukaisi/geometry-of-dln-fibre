import sympy as sp

# ===========================================================================
# ABSTRACT MODEL of the LINK2 fork. We model the SLOT STRUCTURE of DeepestSplit
# q = (reg, (core, spec)) and the reductions as maps, then check which banked
# mechanism each leg of the NF-transitivity needs. The point is structural:
# verify the composition identities EXACTLY (symbolically), so the verdict
# rests on algebra, not prose.
#
# Slots: reg R^nR, core C^nC, spec S^nS. For (2,2,2)-style we keep slots
# symbolic-dimensional but instantiate concrete small dims to check identities.
# ===========================================================================

# --- shift functions (the schur corrections), as abstract continuous maps of (reg,spec) ---
# bare shift: smooth (schurCorrection).  conj shift: continuous-only (schurCorrectionConj).
# We model them as symbolic vector-valued functions sb(reg,spec), sc(reg,spec).
# For the algebra we only need: coreShear(shift): (reg,(core,spec)) |-> (reg,(core+shift(reg,spec), spec)).

def coreShear(shift):
    # returns a python function q=(reg,core,spec) -> (reg, core+shift(reg,spec), spec)
    return lambda reg,core,spec: (reg, core + shift(reg,spec), spec)

# ---------------------------------------------------------------------------
# CHECK 1: bareAbsorb o Theta = conjAbsorb, where Theta = coreShear(sc - sb).
# bareAbsorb = coreShear(sb); conjAbsorb = coreShear(sc).
# Theta shifts core by (sc-sb)(reg,spec); reg,spec unchanged so the inner shift
# arg (reg,spec) is unchanged after Theta. Then bareAbsorb adds sb(reg,spec).
# Net core: core + (sc-sb)(reg,spec) + sb(reg,spec) = core + sc(reg,spec). QED structurally.
# Verify symbolically with concrete shift fns.
# ---------------------------------------------------------------------------
reg = sp.symbols('r0 r1', real=True)
core = sp.symbols('c0 c1', real=True)
spec = sp.symbols('s0 s1', real=True)
reg = sp.Matrix(reg); core = sp.Matrix(core); spec = sp.Matrix(spec)

# arbitrary (nonlinear) continuous shift fns of (reg,spec) -> core-space (2-dim)
def sb(r,s):
    return sp.Matrix([ r[0]*s[0] + sp.sin(r[1]),  s[1]**2 - r[0] ])     # "smooth"
def sc(r,s):
    return sp.Matrix([ sp.Abs(r[0]) + s[0],        sp.sqrt(sp.Abs(s[1])) ])  # "continuous-only"

def Theta(reg,core,spec):
    return coreShear(lambda r,s: sc(r,s)-sb(r,s))(reg,core,spec)
bareAbsorb = coreShear(sb)
conjAbsorb = coreShear(sc)

# bareAbsorb o Theta
r,c,s = Theta(reg,core,spec)
lhs = bareAbsorb(r,c,s)
rhs = conjAbsorb(reg,core,spec)
diff = sp.simplify(sp.Matrix(lhs[1]) - sp.Matrix(rhs[1]))
print("CHECK1 bareAbsorb o Theta = conjAbsorb  (core slot diff, should be 0):")
print("   ", list(diff))
print("    reg slot eq:", sp.simplify(sp.Matrix(lhs[0])-sp.Matrix(rhs[0])).T.tolist())
print("    spec slot eq:", sp.simplify(sp.Matrix(lhs[2])-sp.Matrix(rhs[2])).T.tolist())
print("    Theta(0)=0:", [sp.simplify(x) for x in (Theta(sp.zeros(2,1),sp.zeros(2,1),sp.zeros(2,1))[1])])

print()
print("="*78)
print("CHECK 2: the Theta-peel and what it leaves on the BARE side.")
print("="*78)
# Phi_conj(q) = R'(q) + coreF(conjAbsorb(q))   [R' reads core slot of q]
# rlctAtOn is invariant under precomposition with an MP-homeo.  Apply Theta-peel:
#   rlctAtOn(Phi_conj) = rlctAtOn(Phi_conj o Theta^{-1})   [peel; MP only, NO ContDiff]
# Wait: rlctAtOn_comp_homeomorph: rlctAtOn(F o e) w0 = rlctAtOn F (e w0).
# So to PEEL e off of (F o e) we need Phi_conj to BE of the form (something o Theta).
# Phi_conj(q) = R'(q) + coreF(conjAbsorb(q)) = R'(q) + coreF(bareAbsorb(Theta(q)))   [CHECK1]
# Define G(q) := R'(Theta^{-1}(q)) + coreF(bareAbsorb(q)).  Then
#   G(Theta(q)) = R'(Theta^{-1}(Theta q)) + coreF(bareAbsorb(Theta q))
#              = R'(q) + coreF(bareAbsorb(Theta q)) = Phi_conj(q).
# So  Phi_conj = G o Theta,  hence rlctAtOn(Phi_conj) w0 = rlctAtOn(G o Theta) w0
#              = rlctAtOn G (Theta w0) = rlctAtOn G (w0)   [Theta w0 = w0, since Theta0=0].
# => rlctAtOn(Phi_conj) = rlctAtOn(G),  G(q) = R'(Theta^{-1} q) + coreF o bareAbsorb (q).
#
# KEY OBSERVATION: G's core term is coreF o bareAbsorb -- the BARE (smooth) core energy.
# The ONLY place sc enters G is through Theta^{-1} in the reg-read R'(Theta^{-1} q).
# Theta^{-1} = coreShear(sb - sc) (inverse of core-shift by (sc-sb)): it shifts the
# CORE slot by (sb-sc)(reg,spec).  R' reads (reg, core, spec).  So:
#   R'(Theta^{-1} q) = R'(q.reg, q.core + (sb-sc)(q.reg,q.spec), q.spec).
# This DOES contain sc (continuous-only) inside R'.  This is the "Theta-drag".
#
# THE FORK:  to finish, we need rlctAtOn(G) = rlctAtOn(NF) via a BARE-d diffeo g.
# (W) claims: a JOINT reg-core diffeo g built ONLY from sb (ContDiff) + a reg-straighten
#     reaches NF, and g's reg-straighten absorbs the Theta-drag.
# (O) claims: any sound diffeo reaching NF must reparametrize sc => sc must be ContDiff.
#
# Decisive sub-question: is R'(Theta^{-1} q) = NF-reg-term composed with a SMOOTH map,
# OR does the (sb-sc) drag force a non-smooth reparametrization?
print("Theta^{-1} = coreShear(sb - sc): shifts core by (sb-sc)(reg,spec).")
print("G(q) = R'( reg, core+(sb-sc)(reg,spec), spec ) + coreF(bareAbsorb q).")
print("The drag (sb-sc) is continuous-only (sc not ContDiff).")
