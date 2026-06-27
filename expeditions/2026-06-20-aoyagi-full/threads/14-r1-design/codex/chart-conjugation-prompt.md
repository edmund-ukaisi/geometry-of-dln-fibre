<task>
Red-team a SOUNDNESS claim in a Lean 4 / Mathlib measure-theory proof (RLCT cover). I need you to
check whether a coordinate-permutation CONJUGATION correctly reduces three "A-pivot" integral summands
to a single already-proven one. This is the soundness-sensitive step; the rest is ring/decide-safe.

SETUP (all on `Fin 8 → ℝ` with Lebesgue volume):
- `myF222 x = (x0·x4 + x1·x6)² + (x0·x5 + x1·x7)² + (x2·x4 + x3·x6)² + (x2·x5 + x3·x7)²`
  (= ‖A·B‖²_Frobenius, A=[[x0,x1],[x2,x3]], B=[[x4,x5],[x6,x7]]).
- `Aact = {0,1,2,3}` (the A-block indices = a00,a01,a10,a11).
- `pivotBlowupOn active p x = fun i => if i = p then x p else if i ∈ active then x p * x i else x i`
  (the flat-subset blow-up with pivot p).
- `pivotBlowupOnDeriv active p x` has `.det = (x p)^(active.card − 1) = (x p)^3` for active=Aact.
- `chartDomOn active p = {x | ∀ j ∈ active, j ≠ p → |x j| ≤ 1}`.
- `pivotZeroOn p = {x | x p = 0}`.
- `openBox = univ.pi (fun _ => Ioo (-1) 1)` (the [−1,1]^8-ish bounded witness; an OPEN symmetric box).
- The p-th A-pivot summand (what `recStep Aact 0` produces, one per p ∈ Aact):
    S(p) := ∫⁻ x in chartDomOn Aact p \ pivotZeroOn p,
              ofReal |det(pivotBlowupOnDeriv Aact p x)| · openBox.indicator (|myF222|^(−c')) (pivotBlowupOn Aact p x)
- S(0) is ALREADY PROVEN finite (< ⊤) for c' < 3/2 (call it `p0_summand_via_tail`).

GOAL: prove S(1), S(2), S(3) < ⊤ by CONJUGATION: for each p, find a coordinate permutation
σ : Fin 8 ≃ Fin 8 (acting by `x ↦ x ∘ σ`) such that S(p) = S(0), reducing to the proven p0 case.

NUMERICALLY VERIFIED (exact, by me): myF222 is invariant under these permutations:
- p=2 (a10): row-swap A = swap coords {0↔2, 1↔3}. myF222(x∘σ2) = myF222(x).
- p=1 (a01): col-swap A + row-swap B = swap {0↔1, 2↔3, 4↔6, 5↔7}. myF222(x∘σ1) = myF222(x).
- p=3 (a11): the composite (both swaps) = {0↔3, 1↔2, 4↔6, 5↔7}. (please sanity-check this composite.)

THE SOUNDNESS QUESTION (what I need you to check — the chart-conjugation, NOT myF222-invariance which
is ring/decide-safe): for the conjugation S(p) = S(0) to hold via the change of variables x = σ·y
(measure-preserving, |det σ| = 1 for a permutation), I need ALL of these to line up simultaneously:
  (1) myF222 ∘ pivotBlowupOn Aact p = myF222 ∘ pivotBlowupOn Aact 0 ∘ (some perm), via σ.
  (2) pivotBlowupOn Aact p (σ y) relates to pivotBlowupOn Aact 0 y (or σ ∘ pivotBlowupOn Aact 0):
      does σ conjugate the blow-up at pivot p to the blow-up at pivot 0? i.e.
      pivotBlowupOn Aact p (x ∘ σ) = (pivotBlowupOn Aact 0 x) ∘ σ   — does this hold for the σ above?
      (KEY: σ must permute Aact among itself sending p↔0, AND fix the pivot-blow-up STRUCTURE.)
  (3) |det(pivotBlowupOnDeriv Aact p (σ y))| = |det(pivotBlowupOnDeriv Aact 0 y)|: both are |y_pivot|^3
      — does the pivot coordinate match up under σ (σ sends pivot-0-slot to pivot-p-slot)?
  (4) chartDomOn Aact p and pivotZeroOn p map correctly: σ⁻¹(chartDomOn Aact p \ pivotZeroOn p) =
      chartDomOn Aact 0 \ pivotZeroOn 0? (chartDomOn bounds the non-pivot ACTIVE coords; σ must send
      "non-pivot active for p" to "non-pivot active for 0".)
  (5) openBox is σ-invariant (it's symmetric univ.pi, so yes for any coordinate perm) — confirm.

CRITICAL SUBTLETY I want checked: σ1 (for p=1) swaps B-coords {4↔6,5↔7} too (not just A-coords). But
pivotBlowupOn Aact p only blows up the A-block (active={0,1,2,3}); the B-coords {4,5,6,7} are
SPECTATORS (pass through). Does swapping B-spectators interfere with (2)/(3)/(4)? Specifically: the
blow-up structure `if i∈active then x_p·x_i` only touches active={0,1,2,3}; the B-swap is outside
active. Does pivotBlowupOn Aact p commute correctly with a σ that ALSO permutes the spectator block?
i.e. is `pivotBlowupOn Aact p (x∘σ) = (pivotBlowupOn Aact 0 x)∘σ` still valid when σ moves spectators?
</task>

<output_contract>
Answer in 4 short sections:
1. VERDICT: is the chart-conjugation S(p)=S(0) SOUND for each of p=1,2,3 with the given σ? (yes / no / yes-with-caveat per pivot)
2. The exact identity (2) `pivotBlowupOn Aact p (x∘σ) = (pivotBlowupOn Aact 0 x)∘σ` — does it hold? Show the per-coordinate check (i=p, i∈active\{p}, i spectator) and flag any slot where it FAILS.
3. The spectator-swap subtlety: does σ1/σ3 permuting B-coords break (2)/(3)/(4)? Yes/no + why.
4. If sound: the cleanest Lean lemma chain to formalize S(p)=S(0) (which measure-preserving-permutation lemma, how to transport the setLIntegral, the det/chartDom/pivotZero rewrites). If NOT sound: the precise failure + whether a DIFFERENT σ fixes it, else recommend falling back to re-deriving each S(p) from scratch (4-cheap-rings).
</output_contract>

<grounding_rules>
Distinguish what you can VERIFY by the per-coordinate algebra (the pivotBlowupOn definition is given
explicitly — you can check identity (2) symbolically) from what you're INFERRING. The pivotBlowupOn
definition and σ permutations are concrete — actually do the per-coordinate substitution, don't hand-wave.
Flag any slot where the conjugation identity breaks.
</grounding_rules>
