<task>
You are auditing the STRUCTURAL admissibility of one step in a Lean 4 (Mathlib v4.29) formalisation of
Aoyagi's (S,J) determinantal-locus RLCT resolution for deep linear networks. This is a
pen-and-paper / proof-architecture question, NOT a Lean-syntax question. Judge whether a proposed
proof organisation is LOGICALLY / MEASURE-THEORETICALLY admissible given the recursion's actual shape.
Do NOT worry about tactic details.

## The objects (exact Lean defs, paraphrased faithfully)

Chains are width vectors `M : Fin (L+3) → ℕ` = `(M0, M1, ..., M_L+2)`. The reduced chain
    redChain t M := Fin.cons t (fun i => M (i+2))        -- = (t, M2, M3, ..., M_{L+2})
DROPS EXACTLY ONE LAYER for EVERY t (arity L+3 -> L+2); the cut value t only sets the new leading width.

The target `RouteMBoxThresholdFinite M` says: for all real c' < minAdm M / 2, a certain box integral
`routeMLayerBoxIntegral M c' 1 < ∞`. It is proved by STRONG INDUCTION ON CHAIN ARITY. The step contract
(one of two live framings) is the DECORATED step:

    DecoratedStepHyp adm :=
      ∀ L (M : Fin (L+3) → ℕ),
        (∀ (M' : Fin (L+2) → ℕ) (D' : SJDecoration M'), adm M' D' → DecoratedBoxThresholdFinite D')  -- the IH
        → ∀ (D : SJDecoration M), adm M D → DecoratedBoxThresholdFinite D

i.e. GIVEN box-finiteness for EVERY admissible decoration of EVERY one-shorter chain (the IH is
UNIVERSALLY quantified over one-shorter chains AND over admissible decorations), prove it for M.

`DecoratedBoxThresholdFinite D := ∀ c' < carrierThreshold M, D.integral c' < ∞`, where
`carrierThreshold M = minAdm M / 2` and `D.integral c' = ∫_{z ∈ D.dom} ∫_{u ∈ unitBox d} (monomial(u) *
D.decLoss(u,z)^(-c'))`. For the trivial decoration on M, `D.dom` is the full parameter box and the
integral equals `routeMLayerBoxIntegral M c' 1`.

The front-split (banked, measure-preserving) rewrites the box integral of an L+3 chain as
    ∫_{A' ∈ box(tailChain M)}  ∫_{A0 ∈ frontBox}  frobSq(A0 · prod(tailChain M) A')^(-c')
with the TAIL params A' OUTER (they produce the deep product Z := prod(tailChain M) A'), and the FRONT
matrix A0 INNER. A further banked "boundary peel" bounds this by a FINITE SUM over front pivot ranks
t = 1..min(M0,M1) and pivot charts (ρ,κ) of per-chart integrals `gammaPeelIntegral M t ρ κ c'`. Each of
those per-chart integrals, at a fixed front cut t, is (after a banked Schur-weld + shear) a triple
integral:
    ∫_{A' ∈ box(tailChain M)}   [OUTER, produces Z]
      ∫_{x ∈ clearedParams}
        ∫_{Γ ∈ shiftedBox}       [the FREED CORNER, dims (M0−t)×(M1−t), STILL AN INTEGRATION VARIABLE]
          freedSchurLoss(x, Γ, Z_sub)^(-c')
where Z_sub is a submatrix of Z. NOTE: the corner Γ is NOT yet Gaussian-integrated — the corner "charge"
½(M0−t)(M1−t) is not yet committed; Γ is live.

## Banked facts (assume these are sorry-free and available)

1. `redChain t M : Fin (L+2) → ℕ` for ANY t — a valid one-shorter chain the IH can be instantiated at.
2. Shell cover (measurability-FREE): for the deep product Z, define shells
   `S_j := {Z | min(weakEigCount ε Z) r = j}` for j : Fin(r+1), r = min(M0−t, M1−t). Then
   `⋃_j S_j = univ`, and `∫_{box} f ≤ Σ_j ∫_{S_j} f` holds WITHOUT any S_j being a measurable set
   (only exhaustiveness + monotonicity of ∫ in the domain + finite subadditivity). BANKED.
3. Charge arithmetic (banked, exact-ℕ): at any legal deeper cut u = t+j ≤ min(M0,M1),
   flag charge C_j := (M0−t−j)(M1−t−j) + minAdm(redChain (t+j) M) ≥ minAdm M, AND
   c' < carrierThreshold M ⟹ c' − ½·(M0−t−j)(M1−t−j) < carrierThreshold(redChain (t+j) M).
4. A reduced COMPARATOR decoration `cornerComparator (redChain u M) k jc` exists on the one-shorter chain
   `redChain u M`, is `adm`-admissible, its deeper space is Params(redChain u M) (full reduced box), and
   its decLoss = commonDivisor(u)²·frobSq(prod(redChain u M)). BANKED (adm proof + non-vacuity).
5. PSD-monotonicity `det_le_det_of_posSemidef_sub` and `uniformWenn_le` (a shell-0 PSD bound) and
   `detGram_lintegral_lt_top` (finiteness of ∫ det(XXᵀ)^(-a/2) over a matrix box when a < n−r+1). BANKED.
6. tailChain params factor (banked, measure-preserving, piFinSuccAbove) as
   Params(tailChain M) ≅ [M1×M2 matrix] × Params(M2,...,M_{L+2}); the deep-tail factor Params(M2,..)
   is SHARED with Params(redChain u M) ≅ [u×M2 matrix] × Params(M2,...,M_{L+2}).

## The established analytic finding (from an exact-algebra certificate, decorrelated-confirmed)

At a FIXED front cut t, the per-chart shell-j integrand's corner weight behaves like det(QQᵀ)^(-a/2)
with Q = A_cor·Z, a = M0−t, b = M1−t. When Z has j ≥ 1 weak singular directions (shell S_j, j≥1), this
weight is DIVERGENT if analysed as a fixed a×b corner (converges iff a < M2−b+1, FALSE at j≥1). BUT on
shell S_j it is DOMINATED (a clean ≤, via: peel a further (a−j)×(b−j) sub-corner freeing charge
½(a−j)(b−j); PSD-monotonicity ZZᵀ ⪰ ε²·P_strong eliminating the j weak Z-directions, giving a uniform
ε^{−(a−j)(b−j)} factor; a measure-preserving right-orthogonal transport of the strong block to
detGram at shrunk dims (a−j, b−j, M2−j); drop nonneg residual) by
    const(ε) · (cornerComparator (redChain (t+j) M) k jc).integral(c' − ½(a−j)(b−j)),
which is STRICTLY CONVERGENT (a−j < M2−b+1). No row-deleting change of variables is used; the corner
dims shrink via the deeper-cut Gaussian sub-corner peel + PSD Loewner monotonicity, NOT via a Jacobian.

## THE QUESTION (adjudicate decisively, either direction)

Does the DECORATED recursion STRUCTURE admit a proof of the step that, WITHIN a single per-chart integral
at fixed front cut t (say the binding cut t★), (a) stratifies the OUTER tail variable A' by the deep-Z
shell S_j, and (b) on each shell S_j dominates by the reduced comparator on `redChain (t★+j) M` and
closes it with the IH instantiated AT `redChain (t★+j) M` — a DIFFERENT reduced chain for each j?

Specifically:
- Q1. Is instantiating the (universally-quantified-over-one-shorter-chains) IH at `redChain (t★+j) M`
  for SEVERAL different j WITHIN ONE step invocation logically legitimate, or does the arity recursion
  somehow force a SINGLE reduced chain per step invocation?
- Q2. Does bounding `∫_{A' ∈ box} F(A') ≤ Σ_j ∫_{A' : Z(A') ∈ S_j} F(A')` (shell-stratifying the OUTER
  integration variable, where the shell is a condition on the deep product Z = prod(tailChain M) A')
  require any measure DISINTEGRATION theorem (e.g. disintegration over the ordered singular values of Z,
  which Mathlib lacks), or is it plain finite subadditivity over an exhaustive cover?
- Q3. The per-shell domination maps the LHS (fixed cut t★, corner a×b, live Γ, restricted to Z ∈ S_j)
  onto the comparator's FULL reduced box on redChain(t★+j)M, whose deep-tail factor Params(M2,...) is
  SHARED with the LHS tail. Does establishing this ≤ require disintegrating the tailChain measure over
  that shared deep-tail (a Tonelli/Fubini product factorisation), or something stronger (a genuine
  disintegration / conditional-measure theorem)? Is the banked product factorisation (fact 6) enough?
- Q4. Is there ANY step in (a)+(b) that genuinely requires an UNBANKED measure-disintegration theorem
  (a conditional-measure / Rokhlin-type disintegration), as opposed to bounded analytic LABOUR built on
  the banked facts 1-6? If yes, state PRECISELY the theorem's shape and whether Mathlib v4.29 has an
  adjacent primitive.

## Grounding rules

- Treat facts 1-6 as GIVEN (banked, sorry-free). Do not re-litigate them.
- Distinguish INFERENCE from FACT explicitly in your answer.
- The recursion descends by ARITY (one layer); redChain t M is one-shorter for ALL t. That is a FACT.
- Do NOT assume the step must "peel once at a single cut"; that is only a docstring sketch, not the Prop.
- Judge the PROP `DecoratedBoxThresholdFinite D` (= a finiteness statement admitting ANY valid proof),
  not any particular intended proof.

<output_contract>
Answer in EXACTLY these sections, terse:
1. VERDICT: one line — ADMITS (structure permits the per-shell deeper-cut descent) or
   DOES-NOT-ADMIT (a measure-disintegration wall is unavoidable). State confidence %.
2. Q1 (multi-j IH instantiation): FACT/INFERENCE + 2-3 sentences.
3. Q2 (outer shell subadditivity — disintegration or not): FACT/INFERENCE + 2-3 sentences.
4. Q3 (shared deep-tail — Tonelli product vs genuine disintegration): FACT/INFERENCE + 2-3 sentences.
5. Q4 (is any unbanked measure-disintegration theorem required): if yes, its precise shape + Mathlib
   adjacency; if no, why the banked facts 1-6 suffice.
6. The single most likely thing that would FLIP your verdict.
</output_contract>
