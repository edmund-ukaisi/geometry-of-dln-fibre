<task>
DLNFibre Lean 4 formalisation. I'm building the per-node DISPATCHER `routeStep` for the general-M R1
resolution recursion. I need to pin its TYPE correctly before filling it — getting the type wrong makes
the whole recursion mathematically vacuous (the "type-checks but proves nothing" trap).

CONTEXT. The recursion produces a chart family `(ι, d, k, h)` such that `rlctAtOn (dlnLoss M 0) 0 =
⨅ i:ι, monomialThreshold (d i)(k i)(h i)` (R1's resolution_charts). I rebased it onto crux2's banked
`ChainDimSplit M` (a one-step width split {drop, red, hsum : drop+red=M, hdrops : 0<Σdrop}; L fixed;
ΣM-decreasing). My recursion `routeAtlas = WellFounded.fix chainRel_wf` (chainRel = ΣM-decrease) is GREEN
with one sorry — the dispatcher:

    inductive RouteStep (M : Fin (L+1) → ℕ) : Type 1
      | leaf (md : MonoData)
      | branch (cells : Type) (cellsFin : Fintype cells)
          (split : cells → ChainDimSplit M) (codim : cells → ℕ)
    noncomputable def routeStep (M) : RouteStep M := sorry   -- ← THE dispatcher

    routeAtlas := WellFounded.fix chainRel_wf fun M rec =>
      match routeStep M with
      | .leaf md => { ι := PUnit, data := fun _ => md }
      | .branch cells _ split codim =>
          { ι := Σ c : cells, (rec (split c).red (split c).redM_chainRel).ι   -- descends: Σred<ΣM
            data := fun x => ((rec (split x.1).red _).data x.2).appendDivisor (codim x.1) }

crux2's per-step TRANSPORT (the value content) is SEPARATE, consumes a supplied datum:
- `schur_straighten_squeeze_of_data M S flatCore G redEmbed c₁ c₂ (h : IsSchurStraightenSqueeze ...)` :
  rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0. The datum `h` carries the per-node factorisation
  `c₁·Φ ≤ flatCore ≤ c₂·Φ` near 0 (Φ = Σxᵢ² + G², G²=dlnLoss S.red 0) + germ-nonvanishing — i.e. the
  PROOF that THIS split actually factorises the loss.
- `rlctAtOn_reduced_transport S G ...` : rlctAtOn(G²) 0 = rlctAtOn(dlnLoss S.red 0) redZero.

THE WORKED EXAMPLE (2,2,2), hand-built (NOT via ChainDimSplit): node = blow up a pivot (e.g.
step1A = pivotBlowupOn {0,1,2,3} 0), giving myF222 ∘ φ = y0²·Q (pivot k=1,h=3, ratio 2), recurse on Q.
So each node's split is GLUED to a specific factorisation `core ∘ φ = x_p²·(reduced core)`.

MY CONCERN. `RouteStep.branch` carries `split` + `codim` but NOT the per-cell PROOF that the split
factorises the loss (the IsSchurStraightenSqueeze-datum existence). So a `routeStep` returning ARBITRARY
splits type-checks, and `routeAtlas` produces SOME (d,k,h) — but disconnected from `dlnLoss M 0`. The
value identity `rlctAtOn(dlnLoss M 0) 0 = ⨅ monomialThreshold` would then be UNPROVABLE (the (d,k,h) isn't
tied to the loss). I suspect `routeStep` must bundle the factorisation-existence per cell, OR the
dispatcher and the cover-correctness are ONE obligation (can't fill routeStep, then separately prove the
identity — they're entangled through the per-node datum).
</task>

<output_contract>
1. THE TYPE: should `RouteStep.branch` bundle the per-cell `IsSchurStraightenSqueeze`-datum existence (a
   proof field, not just `split`+`codim`)? If yes, give the corrected field list. If the datum's existence
   is what makes (d,k,h) meaningful, it MUST be in the type the recursion threads — confirm or refute.
2. SEPARABILITY: can `routeStep` (the dispatcher) be filled as a TOTAL function INDEPENDENTLY of proving
   the cover identity, or are they one entangled obligation? i.e. is there a clean intermediate theorem of
   the form "routeAtlas's (d,k,h) reconstructs rlctAtOn" that holds GIVEN a routeStep whose branch fields
   carry the factorisation-existence — so the dispatcher's job is "construct the splits + their datums",
   and the identity is a separate fold? Or does the identity proof have to be interleaved into the fix?
3. THE MINIMAL HONEST NEXT STEP: given the type may need the datum-existence field, what's the smallest
   correct thing to build next that is NOT vacuous — e.g. (a) enrich RouteStep with the proof field +
   re-green the skeleton; (b) prove the per-node fold theorem (rlctAtOn at M = the node's contribution +
   recursion) GIVEN the enriched RouteStep, leaving only the dispatcher's split-CONSTRUCTION as the sorry;
   or (c) something else. Rank by "validates the most while staying honest".
4. THE VACUITY TRAP: confirm or refute — is filling routeStep with arbitrary splits strictly WORSE than
   leaving it sorry (it would let a downstream prove a FALSE-flavoured identity)? What's the guard?
</output_contract>

<grounding_rules>
Reason from the structures/signatures given; you don't have the files. Flag where your answer depends on a
fact you can't verify (e.g. "IF schur_straighten_squeeze_of_data's hypotheses fully pin the per-node
contribution THEN ..."). Distinguish "forced by the math" (the identity genuinely needs the datum) from
"cleaner architecture". Do NOT invent Mathlib/Lean lemma names. The key question is whether the dispatcher
is separable from cover-correctness or entangled — be decisive.
</grounding_rules>
