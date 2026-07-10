<task>
Lean 4 + Mathlib v4.29 formalisation. I am closing the last `sorry` of a front-peel RLCT
finiteness argument for deep linear networks. The isolated goal is a per-pivot-chart change-of-variables
(CoV) finiteness. I want the CLEANEST Lean decomposition + a feasibility read, NOT full code.

## The goal (the one remaining sorry)
```
theorem frontChartIntegral_lt_top (M : Fin (L+1+1+1) → ℕ) (q : ℕ) (hq : q ≤ tailMin M)
    (ρ : Fin q ↪ Fin (tailChain M 0)) (κ : Fin q ↪ Fin (tailChain M (Fin.last (L+1))))
    (c' : NNReal) (hc' : (c':ℝ) < (minAdm M)/2)
    (hIH : RouteMBoxThresholdFinite (fun i : Fin (L+1+1) => M i.succ - q)) :
    frontChartIntegral M q ρ κ (c':ℝ) < ⊤
```
where
```
frontChartIntegral M q ρ κ c' :=
  ∫⁻ A' in paramsBoxM (tailChain M) 1 ∩ {A' | IsUnit ((prod (tailChain M) A').submatrix ρ κ)},
    ∫⁻ A0 in matBox (M 0) (M 1) 1,
      ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c'))
```
- `Params H := ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ` (H : Fin (L+1) → ℕ).
- `prod H A` = the left-associated layer product `prodAux H A L` (matrix Fin(H 0)×Fin(H last)).
- `prodAux H A (k+1) = prodAux H A k * (reindexed A_k)` — FORWARD/left fold, peels the LAST layer.
- `tailChain M i = M i.succ` (arity L+2 → L+1 layers).
- `frobSq X = ∑ᵢⱼ Xᵢⱼ²`; `rmatMul A0 P` = raw matrix product; `paramsBoxM H 1` = all entries in [-1,1];
  `matBox p n 1` = entries in [-1,1].

## The math (a pen-and-paper witness, verified exact for L≤4)
On the chart where the (ρ,κ) q×q minor of P = prod(tailChain M) A' is a unit: block each tail factor
X_i = [[A_i,B_i],[C_i,D_i]] by the corank-q split, thread RIGHT-TO-LEFT with K_L=0,
  α_i = A_i + B_i·K_{i+1},  γ_i = C_i + D_i·K_{i+1},  K_i = γ_i·α_i⁻¹,  Y_i = D_i − γ_i·α_i⁻¹·B_i.
Unit-triangular shears M_i = [[1,0],[−K_i,1]] (det 1) give the per-factor identity (ALREADY PROVED, banked):
  `blockShear_step`: M_i · X_i · M_{i+1}⁻¹ = [[α_i,B_i],[0,Y_i]].
Telescoping (M_{i+1}⁻¹ cancels the next M_{i+1}): M_1·P = [[α_1···α_{L-1}, *],[0, Y_1···Y_{L-1}]],
so rank P = q + rank(Y_1···Y_{L-1}), and Y_1···Y_{L-1} = prod (redTail M q) Y is the reduced product
(redTail M q = fun i => M i.succ − q). The CoV (A') ↦ (α_i,B_i,γ_i,Y_i) is measure-preserving
(Jacobian ±1, composed unit-triangular shears). Loss splits disjointly: frobSq(A0·P) ≃ ‖R‖² + frobSq(Z),
R the M0·q Morse block, Z = prod(redTail) Y. So the chart integral becomes a reducedMorseFront integral
(Morse block dim M0·q + reduced-chain box), finite below ½·minAdm M — BUT at an ENLARGED radius T>1
(the K_i = γ_i α_i⁻¹ are UNBOUNDED on the open chart).

## Banked bricks I can consume (all proved, sorry-free)
- `blockShear_step {q a b} (A B C D Kp) [Invertible (A+B*Kp)] :
    fromBlocks 1 0 (-((C+D*Kp)*⅟(A+B*Kp))) 1 * fromBlocks A B C D * fromBlocks 1 0 Kp 1
      = fromBlocks (A+B*Kp) B 0 (D-(C+D*Kp)*⅟(A+B*Kp)*B)`   (opaque widths, `Matrix (Fin q ⊕ Fin a)…`).
- `rank_eq_q_add_of_normalForm (P α B Z U V) (hU hV : IsUnit det) (hα : IsUnit α.det)
    (hnf : U*P*V = fromBlocks α B 0 Z) : P.rank = q + Z.rank`.
- `measurePreserving_shearSub {α β} (hK : Measurable K) :
    MeasurePreserving (fun p:α×β => (p.1, p.2 - K p.1)) volume volume`  (the Jacobian-1 shear).
- `reducedMorseFront_lt_top M q hq c' hc' hIH : reducedMorseFront M q c' < ⊤`  where
  `reducedMorseFront M q c' = ∫⁻ Y in paramsBoxM (redTail M q) 1, ∫⁻ X in morseBox (M 0 * q) 1,
     ofReal((∑ i, (X i)^2 + frobSq (prod (redTail M q) Y))^(-c'))`.  (ALREADY PROVED, radius 1.)
- `paramsEquivFlat H : Params H ≃ᵐ (Fin (flatDim H) → ℝ)` measure-preserving; `frobSq(prod M A)=dlnLoss M 0 A`.
- Mathlib rank: `rank_mul_eq_{left,right}_of_isUnit_det`, `rank_fromBlocks_zero_offdiag`, `rank_of_isUnit`.
- Opaque-width discipline: block-split via `blockSplitEquiv`/`finSplit` NOT entrywise casts; reassoc via
  fully-applied `mul_three_reassoc` (Matrix.mul_assoc term-mode) NOT `rw [Matrix.mul_assoc]`; `⅟`→`⁻¹`
  via `invOf_eq_nonsing_inv`; dependent-dim `prodAux` peel by prefix-length induction reusing `prodAux_succ`.

## My questions
1. TELESCOPING: the shear recursion is BACKWARD (K_i from K_{i+1}, K_L=0) but `prodAux` is a FORWARD
   left fold. What is the cleanest Lean formulation to compose `blockShear_step` across the L-1 tail
   factors and land `∃ U V (units), U * P * V = fromBlocks α B 0 Z` with `IsUnit α.det` and
   `Z = prod (redTail M q) Y` — given the forward/backward mismatch and opaque widths? Is it better to
   (a) define the shear coefficients by a separate backward recursion and prove the block-upper form by
   induction on the forward fold, or (b) reassociate P and induct differently? Give the induction
   invariant explicitly.
2. RADIUS ENLARGEMENT (the key subtlety): the CoV image sits in a box of radius T>1 (K_i unbounded).
   I want to avoid a bounded-K sub-chart. Is there a BOX-SCALING HOMOGENEITY argument that makes
   finiteness radius-independent? Concretely: is
     `∫⁻ A in paramsBoxM H T, ofReal(frobSq(prod H A)^(-c')) = T^(exponent) · ∫⁻ A in paramsBoxM H 1, …`
   provable via `prod H (T • A) = T^(#layers) • prod H A` + a linear rescaling `A ↦ T•A` of the box
   (Jacobian T^(flatDim))? State the exact scaling identity + exponent, and whether it makes
   `reducedMorseFront`-at-radius-T finite from the radius-1 `reducedMorseFront_lt_top`. Is the exponent
   ever nonnegative in a way that BREAKS finiteness (i.e., does the T-power ever blow up)?
3. LOSS SPLIT: what is the cleanest way to get `frobSq(A0·P) ≃ ‖R‖² + frobSq(Z)` as an integrand
   equality usable under the A0-integral, given P is block-upper after the shear and A0 ranges over its box?
   Does the A0-integral need its OWN shear (A0 ↦ A0·M_1⁻¹) to expose R,Z as disjoint blocks?
4. FEASIBILITY: rank this CoV's four sub-pieces (telescoping / MP / loss-split / radius-scaling) by Lean
   difficulty at opaque widths, and tell me which single sub-piece to isolate as a named sub-sorry if I
   cannot finish all four, so the rest can be built above it.
</task>

<output_contract>
Four numbered sections matching my four questions. For (1) give the explicit induction invariant. For (2)
give the exact scaling identity + exponent formula + the finiteness verdict. For (3) yes/no on the A0-shear
+ the cleanest integrand-equality route. For (4) a difficulty ranking + the single recommended isolation
point. Be concrete about Lean tactics/lemmas; diagnosis over code. ≤ 900 words.
</output_contract>

<grounding_rules>
Flag any claim you are inferring vs. certain. If a scaling exponent or a lemma name is a guess, say so.
Do not assume Mathlib lemmas exist without hedging; v4.29 pin.
</grounding_rules>
