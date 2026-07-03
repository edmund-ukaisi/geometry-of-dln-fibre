<task>
I am formalising (Lean 4 + Mathlib) the RLCT of a deep linear network (DLN) at L=2. I need an
INDEPENDENT verdict on whether one flagged step is a genuine analytic obstruction or merely a
stated-ceiling artifact in the existing Lean code.

SETUP (all real analysis, no probability):
- The DLN loss is a POLYNOMIAL: `dlnLoss H B (params) = ‖ prod(params) − B ‖²_Frob`, where `prod`
  is the ordered matrix product of the layers. So the loss and all its charts are C^∞ / real-analytic.
- FIRST PEEL (`dln_hchart_residual`, PROVEN sorry-free): at an optimal params point `v`, using an
  invertible `nReg × nReg` minor of the flat Jacobian, an Inverse-Function-Theorem chart brings the
  loss into the post-chart sum-of-squares form
      rlctAt(loss)(v) = rlctAtOn ( (∑ p.1 i²) + (∑ q(p) i²) ) (0, t0)
  where `q : (Fin nReg → ℝ) × (Fin N → ℝ) → EuclideanSpace ℝ (Fin n)` is a GLOBAL residual. The
  theorem currently CONCLUDES `ContDiff ℝ 1 q` (i.e. C¹).
- SECOND PEEL (`secondPeel_hchart_residual`, PROVEN sorry-free) needs its input residual VECTOR
  `h := q(0, ·) : (Fin N → ℝ) → EuclideanSpace ℝ (Fin n)` to be `ContDiff ℝ 2` (C²), vanishing at
  the basepoint, with an invertible `extra × extra` Jacobian minor. So there is a GAP: the first
  peel outputs C¹, the second peel demands C².

THE CHAIN INSIDE `dln_hchart_residual` (I have read the source; here are the exact facts):
1. `contDiff_chartΦ : ContDiff ℝ 2 chartΦ`. INTERNALLY it proves each coordinate is `ContDiff ℝ ⊤`
   (loss entries are `contDiff_prod_entry` = C^∞ of `gmapAt` which is `ContDiff ℝ ⊤`), then
   DOWNGRADES to `2` via `.of_le`. So the chart is genuinely C^∞; the `2` is the stated conclusion.
2. IFT chart `exists_boundedUnit_chart_of_contDiffAt (Φ) (…) (hΦ : ContDiff ℝ 2 Φ) …` returns
   `ContDiffOn ℝ 2 Ψsymm V`. Internally it uses Mathlib `ContDiffAt.to_localInverse`, whose
   signature is: for `hf : ContDiffAt 𝕂 n f a` with invertible derivative, the local inverse is
   `ContDiffAt 𝕂 n (localInverse)` — i.e. the inverse has the SAME regularity `n` as the map (no
   loss). The `2` is hard-coded in the wrapper's signature/`have hn : (2:…) ≠ 0`, not forced by IFT.
3. `contDiffOn_rawResidVec (hsymmCD : ContDiffOn ℝ 2 Ψsymm V) : ContDiffOn ℝ 2 (rawResidVec …) V`.
   Internally: each residual coordinate = (C^∞ polynomial loss entry) ∘ Ψsymm, so it inherits the
   regularity of Ψsymm. Stated at `2`.
4. Split homeomorph `splitHomeo.symm` is proven `ContDiff ℝ ⊤` (coordinate reindex), downgraded to 2.
5. Bump-globalisation `exists_contDiff_eventuallyEq_of_contDiffOn {n : ℕ∞} (hg : ContDiffOn ℝ n g U)
   : ∃ G, ContDiff ℝ n G ∧ G =ᶠ g near x₀`. This is PARAMETRIC in `n : ℕ∞`. In `dln_hchart_residual`
   it is CALLED with `(n := 1)` and `hg1CD.of_le` downgrading the C² composite to C¹, producing the
   C¹ `q`. This `(n := 1)` is the ONLY place the regularity is fixed to 1.

MY CLAIM: the C¹→C² gap is a stated-ceiling artifact, not a genuine obstruction. To output a C² `q`
(hence C² slice `q(0,·)`), I strengthen the interface `2`s to `k` (or to a parametric regularity) and
call the bump at `(n := 2)`. Concretely: the chart is C^∞, IFT gives inverse at the same regularity,
the residual composes C^∞ with the inverse, and the bump preserves the regularity `n`. So a C² (even
C^∞) residual is attainable with no new analytic content — just plumbing higher `n` through the
already-C^∞ pieces.

QUESTIONS:
(A) Is my claim correct that this is a stated-ceiling artifact, NOT a genuine analytic obstruction?
    In particular: does the IFT (`ContDiffAt.to_localInverse`) genuinely preserve C^n (no loss of one
    derivative)? Is there any step above where regularity is genuinely lost that I have missed (e.g.
    the bump product `χ • g` — does multiplying a C^∞ bump by a C^k map stay C^k? does the germ /
    RLCT-transfer machinery secretly need only C¹, or would C² break some downstream measurability /
    a.e. argument)?
(B) Is there a subtle reason the DLN chart could FAIL to be C² even though the loss is polynomial —
    e.g. the minor-determinant division in the IFT introducing a non-smooth point, or the
    bump-globalisation only agreeing on a neighborhood (does the second peel need C² GLOBALLY or only
    near the basepoint t0)? The second peel takes `ContDiff ℝ 2 h` (GLOBAL C²) as a hypothesis — is a
    global C² attainable by bump-globalising a locally-C² map, or is global C² a real extra demand?
(C) Cheapest concrete route: strengthen `dln_hchart_residual` to output `ContDiff ℝ 2 q` (or a
    parametric `ContDiff ℝ k q` for any `k`). Which of the 4 interface signatures MUST change, and is
    any of them NOT actually C^∞-provable (a real blocker)?
</task>

<output_contract>
Answer in three short sections A, B, C matching the questions. For A: a clear
GENUINE-OBSTRUCTION / STATED-CEILING-ARTIFACT verdict with the one load-bearing reason. For B: yes/no
on each sub-risk (minor-det division, global-vs-local C², bump product regularity), each one line. For
C: the minimal set of signatures to change and any that is a real blocker. Be terse; flag any claim
that is inference vs. a fact you can derive from the Mathlib lemma shapes I gave.
</output_contract>

<grounding_rules>
You do NOT have the repo. Reason from the Mathlib lemma shapes and standard real-analysis facts I
stated. If a verdict depends on a Mathlib lemma detail I did not give, say so explicitly and state
what you are assuming. Distinguish "standard analysis fact" from "inference about their specific Lean
code".
</grounding_rules>
