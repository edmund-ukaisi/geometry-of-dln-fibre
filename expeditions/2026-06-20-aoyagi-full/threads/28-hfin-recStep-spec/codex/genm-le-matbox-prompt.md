<task>
Lean 4 / Mathlib formalisation design review. I must build a generic ∀M theorem
`routeMCore_le_matBox` (an "M-shape" reduction) and re-point a SKELETON theorem
`routeMCore_threshold_lt_top` at an existing SchurCore-chain finiteness result.
Adjudicate whether the SchurCore-chain target is reachable for arbitrary M, and
if not, what the RIGHT intermediate target is.

## The objects (all already built, sorry-free unless noted)

- `M : Fin (L+1) → ℕ` is a width vector. A network parameter `A : Params M` is a
  tuple of layer matrices, layer s of size `M s.castSucc × M s.succ`.
- `prod M A : Matrix (Fin (M 0)) (Fin (M (last L))) ℝ` is the L-fold layer product
  `A0·A1·…·A_{L-1}` (left-associated). So the OUTPUT block has `M 0` rows and
  `M (last L)` columns; the inner widths are `M 1, …, M (L-1)`.
- `routeMCore M : (Fin (flatDim M) → ℝ) → ℝ` is `dlnLoss M 0 ∘ (paramsEquivFlat M).symm`.
  At target 0, `dlnLoss M 0 A = frobSq (prod M A)` (sum of squares of entries). So in
  flat coords `routeMCore M x = frobSq(prod M A)` where A is the unflattened x.
- `routeMBaseNbhd M = (−1,1)^{flatDim M}` (open box).
- `minAdm M : ℕ` is the minimal admissible codim; `½·minAdm M` is the target RLCT
  threshold. For the binding cases the corank stratification gives `minAdm`.
- `matBox p n T = {X : Fin p → Fin n → ℝ | ∀ i j, X i j ∈ [−T,T]}`.
- `rmatMul X Y` is the raw (function-level) matrix product.
- `frobSq M = ∑_i ∑_j (M i j)^2`.

## What I want to prove

The HEADLINE skeleton (currently `sorry`):
```
theorem routeMCore_threshold_lt_top {L : ℕ} (M : Fin (L + 1) → ℕ) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    ∫⁻ x in routeMBaseNbhd M, ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) < ⊤
```

## The two existing templates / tools

1. The r=3 template `routeMCore_M334_le_matBox` (M = [3,3,4], so L=2): reduces
   `∫_{routeMBaseNbhd M334} |routeMCore M334|^{−c'}` ≤ `∫_{A0∈matBox 3 3 1}∫_{A1∈matBox 3 4 1} frobSq(A0·A1)^{−c'}`.
   This works because L=2: `prod M334 A = A0·A1` is literally a TWO-matrix product.
   The proof is pure measure-preserving plumbing: open box ⊆ closed cube; transport
   via `paramsEquivFlat` (MP) to the all-entries-bounded `Params` box; reshape via a
   `piFinSuccAbove`+`piUnique` layer-split equiv `eParams334` (MP) to the product of the
   two layer matrix boxes; Tonelli.

2. The SchurCore chain. `SchurCore (p r : ℕ) (c' T : ℝ) : Prop :=`
   `(∫_{Δ∈matBox r r T}∫_{S∈matBox r p T} frobSq(Δ·S)^{−c'}) < ⊤`. There is a result
   `schurGen_lt_top_modulo_recStep (hstep : SchurRecStep 4 schurLambda) :`
   `∀ r c', 0<c' → c'<schurLambda r → ∀ T, 0<T → SchurCore 4 r c' T`.
   NOTE: SchurCore is HARDCODED at p=4 (the column count of the right factor S is 4).
   `schurLambda r` = the closed corank-recursion threshold at p=4 (= 0, ½, 2, 4, 6, …
   for r = 0,1,2,3,4,…). `schurRecStep_four` is being landed separately (the carve).

The 4422 route (M=[4,4,2,2], L=3, a 3-matrix product) does NOT use SchurCore; it
uses an ITERATED-FIBRE peel `fibre_lintegral_mul_le` that peels the front layer at
threshold `p/2` (p = #rows of the left factor), giving
`∫_{A2}∫_{A1}∫_{A0} frobSq(A0·A1·A2)^{−c'} ≤ C·∫_{A2} frobSq(A2)^{−c'} < ⊤` for c'<2.
But its threshold (2) is NOT generally `½·minAdm`.

## The tension I need adjudicated

The team brief says: build a GENERIC `routeMCore_le_matBox` (the ∀M M-shape
reduction) so that `routeMCore_threshold_lt_top` can wire to SchurCore via
`schurGen_lt_top_modulo_recStep`. But:

(a) `prod M A` is an L-FOLD product for general M, not a 2-matrix product. The r=3
    template only works because L=2.
(b) SchurCore is FIXED at p=4 (right factor S has 4 columns). The generic output
    width `M (last L)` is arbitrary.
(c) `schurLambda r` is the p=4 threshold, not `½·minAdm M` in general.

So a LITERAL ∀M reduction to `SchurCore 4 r` looks impossible (widths/columns/threshold
don't match arbitrary M).

## Questions (rank + answer each, concise)

1. Is the team's framing achievable as stated — a single ∀M `routeMCore_le_matBox`
   reducing arbitrary `routeMCore M` to a `SchurCore 4 r` two-matrix box — or is it
   a category error (the SchurCore chain is p=4-specific and only closes a SPECIFIC
   binding family, not arbitrary M)?

2. If it's NOT a fully-∀M target: what is the RIGHT honest statement for a generic
   `routeMCore_le_matBox`? Candidates:
   (i) A pure MP plumbing reduction `∫ |routeMCore M|^{−c'} ≤ ∫_{layer boxes}
       frobSq(A0·…·A_{L-1})^{−c'}` over the L layer matrix boxes (the L-fold analog of
       the M334 reduction, NO SchurCore, NO threshold claim — just the box reduction).
       Then `routeMCore_threshold_lt_top` is a SEPARATE finiteness of that box integral
       (which for general M would need the iterated-fibre OR a Schur recursion, and is
       genuinely the open content).
   (ii) Something narrower keyed to a specific binding family.

3. For the iterated-fibre peel route to finiteness of the L-layer box integral
   `∫ frobSq(A0·…·A_{L-1})^{−c'}`: peeling front layers via `fibre_lintegral_mul_le`
   (threshold p/2 = #rows of peeled left factor = M 0, M 1, …) terminates at a 2-matrix
   product `frobSq(A_{L-2}·A_{L-1})`. The reached threshold is `min_k (M k)/2` over the
   peeled layers — is THAT equal to `½·minAdm M`? (minAdm is the minimal admissible
   codim — does the iterated-fibre threshold match it, or is the iterated-fibre route
   strictly weaker than `½·minAdm` so that the SchurCore radial-blow-up is genuinely
   needed to reach `½·minAdm`?)

4. Given all the above, what is the SAFEST scoping for THIS tide: (A) the pure ∀M MP
   box-reduction lemma `routeMCore_le_matBox` (option 2(i)) + re-point the threshold
   skeleton to depend only on a clearly-named finiteness-of-the-box hypothesis (gated
   on the carve), OR (B) attempt the literal SchurCore wiring and likely hit a
   width/threshold wall? I want the bedrock-correct minimal statement, not an
   overclaim.
</task>

<output_contract>
Four numbered sections matching the four questions. For Q1 give a yes/no/category-error
verdict + one-paragraph justification. For Q2 pick the right statement and write the
exact Lean signature you'd commit (with hypotheses). For Q3 give the threshold
comparison verdict (equal / iterated-fibre weaker) with the reasoning. For Q4 give a
single recommendation (A or B) and the 3-5 step build order. Be concise; this is a
design adjudication, not a proof.
</output_contract>

<grounding_rules>
Distinguish what you can DERIVE from the definitions given (matrix dims, frobSq
structure, fibre thresholds) from what you'd need to ASSUME about the project's intent.
Flag any place where you're inferring the project's design rather than reading it off
the math. If the literal SchurCore-4 target is mathematically impossible for arbitrary
M, say so plainly.
</grounding_rules>
