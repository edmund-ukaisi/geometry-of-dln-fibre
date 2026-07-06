<task>
Lean 4 / Mathlib formalisation. I must decide whether the CRUX lemma of a stalled
proof leg is achievable THROUGH THE CONCRETE OBJECT the current architecture produces,
or whether it is architecturally blocked and needs a different producer. I need your
decorrelated verdict on ONE structural question. Do NOT write Lean; reason about the
mathematics of the construction.

BACKGROUND (deep-linear-network RLCT, Aoyagi). We want the D1 "≥"-leg at L=2:
  rlctAt (dlnLoss H B) deepest  ≤  rlctAt (dlnLoss H B) v      for v optimal.
The current Lean route peels the loss twice with the Implicit Function Theorem:

FIRST PEEL. A lemma `dln_hchart_residual_c2` charts the DLN loss near an optimal point v
into a sum-of-squares normal form. Concretely it invokes an IFT-chart lemma
  `rlctAtOn_eq_of_contDiff_chart_rinv (f) (Φ) (wstar) (f') …`
whose OUTPUT is: `∃ Ψsymm V, IsOpen V ∧ … ∧ (∀ᶠ w near wstar, Φ (Ψsymm w) = w) ∧
  rlctAtOn f wstar = rlctAtOn (fun w => f (Ψsymm w)) wstar`,
where Ψsymm is the abstract IFT inverse obtained from
`exists_boundedUnit_chart_of_contDiffAt` — i.e. an EXISTENCE statement, no closed form.
The first-peel residual `q` is then `q := (bump-globalisation of) [the DLN loss-entry
vector] ∘ Ψsymm`, reindexed. Result:
  rlctAt (dlnLoss H B) v = rlctAtOn (fun p => ∑ p.1² + ∑ (q p)²) ((0), t0).

SECOND PEEL. `secondPeel_hchart_residual` takes the first-peel slice residual
`h(t) := q((0), t)` (a C² vector, h(t0)=0) with an invertible `extra × extra` Jacobian
minor at t0, and applies the SAME IFT-chart machinery again, producing a NEW abstract
IFT inverse `Ψsymm₂` and a bump-globalised C¹ residual
  q₂ := (bump-globalisation of) [ (h ∘ Ψsymm₂), selected components zeroed ] ∘ splitHomeo⁻¹,
with:
  rlctAtOn (fun t => ∑ (h t)²) t0
    = rlctAtOn (fun p => ∑ p.1² + ∑ (q₂ p)²) ((0), t0₂).

THE CRUX LEMMA I must produce (call it `degraded_slice_rlct_eq_lambdaCore`, its content):
  rlctAtOn (fun z => ∑ i, q₂ ((0), z) i ²) t0₂  =  ENNReal.ofReal (lambdaCore M')
where M' = MprimeRect (H−r) a b is a fixed reduced DLN width vector and lambdaCore is
the Aoyagi closed-form. The ONLY tool that computes a DLN-core RLCT is
  `r1_resolution_general M' … : rlctAtOn (fun A => dlnLoss M' 0 A) 0 = ofReal(lambdaCore M')`
i.e. it computes the RLCT of the EXPLICIT polynomial DLN core `dlnLoss M' 0`, NOT of an
abstract residual.

A prior tide already PROVED (with a decorrelated Codex) that the crux is FALSE for an
arbitrary C² residual q₂ satisfying only the chart equation: the counterexample
R = x² + u⁴ peels to q₂-slice = u⁴, RLCT 1/4 ≠ lambdaCore(M'). So the crux can only hold
by IDENTIFYING the concrete q₂-slice with the DLN core `dlnLoss M' 0` up to a bounded-unit
local C¹ diffeomorphism (the "model identification"), then invoking r1_resolution_general
+ RLCT-invariance.

MY STRUCTURAL CLAIM TO RED-TEAM:
"The concrete q₂ produced by `secondPeel_hchart_residual` cannot support the model
identification, because both IFT peels invoke `rlctAtOn_eq_of_contDiff_chart_rinv`, which
REPLACES the explicit DLN polynomial loss `f` by the abstractly-defined composite
`f ∘ Ψsymm` (Ψsymm an existence-only IFT inverse with no closed form and no retained
algebraic relation to the DLN loss). After two such peels, q₂ is defined purely through
Ψsymm, Ψsymm₂ and bump cutoffs; the DLN polynomial structure that would let one recognise
q₂-slice as `dlnLoss M' 0 ∘ φ` has been DISCARDED by the chart lemma. Therefore the RLCT
value of q₂-slice, though well-defined, is inaccessible from the data the producer retains,
and the crux is UNPROVABLE through this q₂. The fix is a different producer that threads the
explicit polynomial residual (Aoyagi's explicit iterated block-elimination / corner atlas)
so the residual IS literally a DLN core, rather than the abstract IFT peel."

QUESTIONS:
1. Is the structural claim CORRECT — i.e. is the crux genuinely blocked through this
   concrete IFT-peel q₂, given that Ψsymm/Ψsymm₂ are existence-only and the chart lemma
   retains no algebraic handle tying f∘Ψsymm back to dlnLoss? Or is there a way to recover
   the value (e.g. some retained-derivative or germ-level handle) that I am missing?
2. Is there any WEAKER route to the D1 ≥-leg that AVOIDS the value identity entirely — e.g.
   only a LOWER bound `lambdaCore(M') ≤ rlctAtOn(q₂-slice)` suffices for the `hCore`
   inequality (the interface currently demands equality, but the downstream only needs
   `lambdaCore M ≤ ∑extra/2 + rlctAtOn(q₂-slice)`). Does a lower bound help, or is it
   equally blocked because ANY nonzero handle on the abstract residual's value is absent?
   (Note a banked Theorem-4 comparison `deepest_le_of_homogeneous_core` exists: the DLN core
   at v dominates the deepest core by homogeneity — could the leg route through THAT
   directly, bypassing residual-RLCT computation?)
3. If blocked: state the MINIMAL architectural change. Is it truly a new explicit-residual
   producer (large, ~600–1500 lines), or is there a smaller surgical fix — e.g. strengthen
   `rlctAtOn_eq_of_contDiff_chart_rinv` to ADDITIONALLY return that `f∘Ψsymm` agrees to
   sufficient order with an explicit model, threaded from the DLN loss?
</task>

<output_contract>
Four short sections:
1. VERDICT on the structural claim — one of {CORRECT-blocked, INCORRECT-recoverable,
   PARTIALLY} + 3–6 sentences of the decisive reasoning.
2. LOWER-BOUND / Theorem-4 route — is there a weaker path that avoids the value identity?
   yes/no + why, and if yes the exact statement to target.
3. MINIMAL FIX if blocked — new producer vs surgical chart-lemma strengthening; name the
   single load-bearing new object.
4. ONE-LINE bottom line for the tide report.
</output_contract>

<grounding_rules>
Distinguish clearly between (a) what follows rigorously from the construction as described
and (b) your inference/speculation. If you need an assumption about a lemma I did not fully
specify, state it explicitly and mark the conclusion as conditional. Do not assert that a
handle exists in the code unless the description implies it.
</grounding_rules>
