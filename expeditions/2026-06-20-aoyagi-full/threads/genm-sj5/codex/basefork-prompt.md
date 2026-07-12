<task>
Adjudicate an ARCHITECTURE fork in a decorated finiteness induction (Lean). Reason in exact terms.
Self-contained.

SETUP. A decorated induction proves `∀ D, adm D → DecoratedBoxThresholdFinite D` (∫ decLoss^{-c'} < ⊤ for
c' < ½minAdm M) by arity induction on the chain M, then specialises at the trivial decoration to get the plain
goal. A decoration D over chain M has: d (# exceptional coords u₁..u_d), a carrier (support matrix `supp : ι
→ Fin d → ℕ` + linear residuals `resᵢ(z)` via coeff), accumulated Jacobian `jac : Fin d → ℕ`, and deeper
data (Z, ctx, dom). decLoss(u,z) = Σᵢ (∏_ℓ |u_ℓ|^{supp i ℓ} · resᵢ(z))². The step peels width-(L+2) → width-
(L+1) redChain carrying the decoration (the IH is DECORATED — over d≥1 decorations, NOT plain trivials; the
plain-IH version was proven UNPROVABLE). Base = width-2 (2-node chain = a single matrix, smooth zero-locus).

adm currently := genuineCarrier D ∧ (a=0 ∨ b=0 ∨ pSimultaneous supp)  [pSimultaneous = ∃i₀ ∀j∀ℓ supp i₀ ℓ ≤
supp j ℓ, a support-minimality / (T) condition]. genuineCarrier pins the deeper data (Z ≃ full param tuple,
ctx reads the product) but does NOT constrain supp/jac/coeff beyond pSimultaneous.

THE FINDING (verify): DecoratedBaseHyp (∀ adm width-2 D → finite) is FALSE for this adm, two ways:
 (a) THRESHOLD: the terminal finiteness lemma requires `c' < monomialThreshold(d, sharedDivisorExp supp,
     jac)` as a HYPOTHESIS. adm's pSimultaneous is support-minimality, NOT a threshold bound; an adversarial
     admissible carrier (jac=0, large supp) has monomialThreshold ≪ ½minAdm → the base integral DIVERGES.
 (b) COUPLED RESIDUAL: the terminal lemma is u-only (residuals ≡ 1); but decLoss couples u with resᵢ(z) that
     can VANISH as z ranges dom. If the residual is DEGENERATE (vanishes on a positive-measure set, not just
     a null point), decLoss is the coupled (u,z) RLCT, not the u-only terminal, and diverges.

The needed base-invariants — (i) monomialThreshold(supp,jac) ≥ ½minAdm; (ii) residual COERCIVE (vanishes only
on a null set = a faithful normal-crossings resolution) — are exactly the OUTPUT of a faithful (S,J)
resolution (which the peel/step produces). So "adm decouples from the step" is incomplete: the base re-couples
adm to the step's resolution-invariants.

OPTIONS:
 (A) strengthen adm to CARRY the base-invariants (i)+(ii) [= "the carrier is a faithful (S,J) resolution of
     frobSq(product): threshold ≥ ½minAdm ∧ coercive residual"]; the step PRESERVES them; the base CONSUMES
     them. Cost: adm's def/preservation-proof re-couples to the step.
 (B) fold the d≥1 base into the step: the base handles only d=0 (trivial, free-block Morse); the step
     produces finite terminals by construction, never handing a raw d≥1 decoration to a separate base.

ASSESS:
 Q1. Confirm the finding: is DecoratedBaseHyp genuinely FALSE for the current adm (both (a) and (b))?
 Q2. A vs B. KEY: since the IH is DECORATED (over d≥1 decorations), the base MUST handle d≥1 width-2
     decorations — so is the coupling of adm to the step's resolution-invariants INTRINSIC (unavoidable), or
     can (B) genuinely keep the base d=0-only without collapsing to the (dead) plain-IH descent? Which option
     is sound + faithful + least structural risk?
 Q3. Does the arity recursion FORCE the width-2 carried decoration to be terminal-form (u-monomial × coercive
     free-block residual, threshold ½minAdm)? A 2-node chain is a single matrix (smooth zero-locus, no deeper
     product to couple) — so is there nothing left to resolve at width-2 (⟹ the carried decoration IS
     terminal-form given the resolution above was faithful), or can a partially-resolved (still-coupled)
     decoration reach width-2 (⟹ base fails)?
</task>

<output_contract>
Q1,Q2,Q3: verdict + reason, [DERIVED]/[INFERRED]. On Q2 state A or B and whether the #3↔#5 coupling is
intrinsic to the decorated descent. End: the cleanest base-invariant to add (if A) or the base/step split (if
B), and whether this is a wall or labour.
</output_contract>

<grounding_rules>
The IH is DECORATED (d≥1) — a plain-IH (d=0-only) descent was proven dead. Distinguish an intrinsic coupling
(the decoration IS the step's output, so the base over decorations must reference the step's invariants) from
an avoidable one. Do not paste code.
</grounding_rules>
