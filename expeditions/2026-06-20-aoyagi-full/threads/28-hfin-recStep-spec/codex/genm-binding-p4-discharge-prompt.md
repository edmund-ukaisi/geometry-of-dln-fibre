<task>
Lean 4 / Mathlib formalisation DESIGN review. I must build a theorem discharging a named
finiteness hypothesis `RouteMBoxThresholdFinite M` for the "binding p=4 family" of width
vectors M, GATED on the carve `schurRecStep_four`. I need you to adjudicate the RIGHT
statement shape + scope, and flag whether the bridge is reachable or a research wall.

## The objects (all built, sorry-free unless noted)

- `M : Fin (L+1) → ℕ` a width vector. `Params M` = tuple of layer matrices, layer s of size
  `M s.castSucc × M s.succ`. `prod M A` = the L-fold product `A0·A1·…·A_{L-1}`, size `M 0 × M(last L)`.
- `frobSq N = ∑_i ∑_j (N i j)^2`. `rmatMul` = raw matrix product.
- `routeMLayerBoxIntegral M c' T := ∫_{A ∈ paramsBoxM M T} frobSq(prod M A)^{−c'}` where
  `paramsBoxM M T = {A | ∀ s i j, A s i j ∈ [−T,T]}`. (T=1 is the unit box.)
- `RouteMBoxThresholdFinite M : Prop := ∀ c' : ℝ≥0, c' < minAdm M / 2 → routeMLayerBoxIntegral M c' 1 < ⊤`.
  This is the NAMED analytic gap I'm discharging. `minAdm M` = the minimal admissible codim.
- `matBox r n T = {X : Fin r → Fin n → ℝ | ∀ i j, X i j ∈ [−T,T]}`.
- `SchurCore (p r : ℕ) (c' T : ℝ) : Prop := (∫_{Δ∈matBox r r T}∫_{S∈matBox r p T} frobSq(Δ·S)^{−c'}) < ⊤`.
  HARDCODED at p=4 in the chain below.
- `schurLambda : ℕ → ℝ` = the p=4 corank-recursion threshold: `0, ½, 2, 4, 6, …` (= 2r−2 for r≥2).
- `schurGen_lt_top_modulo_recStep (hstep : SchurRecStep 4 schurLambda) :`
  `∀ r c', 0<c' → c'<schurLambda r → ∀ T, 0<T → SchurCore 4 r c' T`.
- `schurRecStep_four : SchurRecStep 4 schurLambda` — being landed by the carve thread (a hypothesis
  for me until the branches merge).

## What I've already built (and verified)

The ∀M reduction `routeMCore_le_matBox` (pure MP, `∫ |routeMCore M|^{−c'} ≤ routeMLayerBoxIntegral M c' 1`)
+ the named gap `RouteMBoxThresholdFinite` + the gated threshold theorem + the (3,3,4) WITNESS
`routeMBoxThresholdFinite_M334` (proven via the banked (3,3,4) blow-up chain `matBox334_blowup_lt_top`,
which is a (3,3,4)-bespoke 9-chart radial cover, NOT the SchurCore chain).

## The new task (team lead's brief, verbatim intent)

"Generalize `routeMBoxThresholdFinite_M334` to ALL p=4-binding M via `schurGen_lt_top_modulo_recStep` +
the carve. Build it GATED on `schurRecStep_four` as a hyp. Makes hbox proven for the whole binding
family (not just M334)."

## The mathematical situation I see (verify / correct me)

To go from `routeMLayerBoxIntegral M` (an L-FOLD product box `frobSq(A0·…·A_{L-1})`) to `SchurCore 4 r`
(a TWO-matrix box `frobSq(Δ·S)` with S being r×4) for a "binding p=4 M", I believe the bridge is:
  (1) an iterated-fibre FRONT-PEEL: integrate out the front layers A0,…,A_{L-3} via the banked
      `fibre_lintegral_mul_le` (threshold p/2 = rows of the peeled left factor), reducing
      `frobSq(A0·…·A_{L-1})` down to `frobSq(A_{L-2}·A_{L-1})` — a two-matrix product;
  (2) then a rank/Schur reduction of that two-matrix core to `SchurCore 4 r` (the radial blow-up,
      what the carve's firing does), giving finiteness for c' < schurLambda r.
The threshold has to reconcile: the front-peel caps each peeled layer at (its row count)/2; the binding
corank-r core at schurLambda r; and the whole must be ≥ ½·minAdm M (so the gate fires up to ½·minAdm).

## Questions (rank + answer each, concise)

1. What is the RIGHT precise definition of the "binding p=4 family"? Candidates: (i) M with
   `M (last L) = 4` (output width exactly 4)? (ii) M whose binding corank stratum has the p=4 SchurCore
   shape? (iii) the specific anchor set {(2,2,2),(3,3,4),(4,4,2,2)} + obvious extensions? I need a
   Lean-statable predicate `IsBindingP4 M : Prop` (or a concrete family) that (a) is non-vacuous,
   (b) makes the bridge to SchurCore 4 r actually hold, (c) the team lead's "binding p=4 family" most
   plausibly means. Which, and what's the predicate?

2. Is the two-step bridge (front-peel + SchurCore) above CORRECT and reachable, or is there a hidden
   wall? Specifically: does the front-peel threshold (min over peeled layers of (rows)/2) plus the
   corank-r SchurCore threshold actually compose to ≥ ½·minAdm M for the binding family, or is there a
   threshold gap where the peel undershoots? Give the threshold arithmetic for a concrete binding case
   (e.g. M=(4,4,4) or M=(3,3,4,4)) — does it reach ½·minAdm?

3. Given the carve provides ONLY `SchurCore 4 r` (square Δ, r×4 S), and the front-peel of a general
   binding-p4 M leaves a two-matrix product `A_{L-2}·A_{L-1}` whose factors are NOT generally square-Δ
   × r×4-S, is there a SHAPE MISMATCH? Can the residual two-matrix core always be massaged into the
   `SchurCore 4 r` shape (Δ square r×r, S r×4), or only for a narrow sub-family? If only narrow, the
   honest deliverable might be just the anchor set, not a "family".

4. RECOMMENDATION: given all the above, what is the bedrock-correct, NON-overclaiming statement to build
   NOW (gated on schurRecStep_four)? Options:
   (A) `routeMBoxThresholdFinite_of_schurRecStep (hstep : SchurRecStep 4 schurLambda) (M) (hbind :
       IsBindingP4 M) : RouteMBoxThresholdFinite M` — the genuine family, IF the bridge holds.
   (B) Just re-prove the existing anchors (M334 etc.) via the SchurCore chain (cleaner, but adds little
       over the banked bespoke chains).
   (C) A narrower honest statement (e.g. only `M (last L) = 4` AND L=2, i.e. the literal 2-matrix p=4
       case where SchurCore applies DIRECTLY with no front-peel) — `routeMBoxThresholdFinite_of_…` for
       the depth-2 output-4 family.
   Pick one and write the exact Lean signature. If (A)/the broad family is a research wall (the
   front-peel→SchurCore shape bridge is genuine new math, not a banked brick), SAY SO and recommend the
   honest narrower scope (C) instead.
</task>

<output_contract>
Four numbered sections matching the four questions. Q1: pick the predicate, state it Lean-precisely.
Q2: threshold arithmetic verdict (composes / undershoots) with a worked binding case. Q3: shape-mismatch
verdict (always massageable / narrow-only) with reasoning. Q4: a single recommendation (A/B/C) + the
exact Lean signature to build now, gated on schurRecStep_four. Be concise; flag inference vs derived.
</output_contract>

<grounding_rules>
Distinguish what you can DERIVE from the given definitions (matrix dims, fibre thresholds, minAdm
arithmetic) from what you'd ASSUME about project intent. If the broad "binding p=4 family" bridge needs
a brick that isn't banked (the front-peel→square-Δ-SchurCore massage), state plainly that it's a
research wall and recommend the honest narrower scope. Do not invent a family predicate that makes the
theorem vacuous or that the bridge can't actually discharge.
</grounding_rules>
