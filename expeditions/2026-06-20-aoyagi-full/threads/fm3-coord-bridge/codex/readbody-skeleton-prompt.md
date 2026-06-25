<task>
Lean 4 + Mathlib formalisation design. I am building the "read body" for a general blow-up
dispatcher (#99 in a deep-linear-network RLCT project). I need the CLEANEST "green-with-named-gaps"
skeleton shape — what to fill now vs what to leave as a single named obligation.

CONTEXT (decl-grounded, all committed GREEN on my branch):
- `structure ChainDimSplit (M : Fin (L+1) → ℕ)` : a width split `drop + red = M`, `0 < Σ drop`
  (termination). `schurState M hlo : ChainDimSplit M` is the UNIFORM split that decrements indices 0,1.
- `structure PivotWitness (M : Fin (L+1) → ℕ) (c : ℕ)` := ⟨T : Fin L → ℕ, hAdm : T ∈ Adm M,
  hCodim : c = (Mval M T).toNat⟩. Purely combinatorial; `Adm M` is a finite admissible cone of exponent
  vectors; `Mval M T : ℤ` is a polynomial (rank-free).
- `structure BranchData (M₀ M : Fin (L+1) → ℕ)` := ⟨cells : Type, [Fintype], [Nonempty],
  split : cells → ChainDimSplit M, codim : cells → ℕ, witness : (c) → PivotWitness M₀ (codim c)⟩.
  This is exactly the payload of a `RouteStep.branch`. My `routeStepOf (M₀ M)(hbranch : ¬isLeafNode M →
  BranchData M₀ M) : RouteStep M₀ M` is GREEN (leaf-first dispatch, no sorry), and the recursion
  `routeAtlasOf` over it is GREEN.
- `achieverPivotWitness (M) : PivotWitness M (minAdm M)` is GREEN — the inf'-achiever T* (via
  Finset.exists_mem_eq_inf') with Mval M T* = minAdm. So the BINDING-cell witness is constructible NOW.
- The value fold `routeM_value_eq` is GREEN: ⨅ over leaves = ½·minAdm, given per-leaf PivotWitness (C≥)
  + ONE achiever leaf i₀ with minAdm in its codim-list (C=∃).

THE READ BODY = produce `BranchData M₀ M` for general NON-LEAF M. A pen-and-paper feasibility cert (exact-
algebra, decorrelated) established:
1. The achiever stratum T* is NEVER the origin; the achiever cell's `ChainDimSplit` is NOT the uniform
   `schurState` (which collapses both front widths and bottoms at codim > minAdm). The binding cell needs
   the split DICTATED BY T*'s rank-drop profile.
2. The genuine residual = constructing, for general M, the per-cell blow-up Schur presentation `hnode`
   (the analytic chart) — formaliser-weeks, the ONLY genuinely-new obligation. Everything else (squeeze,
   transport, termination, value fold, T*) is GREEN.
3. The honest deliverable = the roadmapped read body with that ONE named gap. Do NOT re-aim at full
   stratum-surjectivity (strictly stronger than the value needs).

THE DESIGN QUESTION: what is the cleanest Lean skeleton for the read body so that
(a) it is NON-VACUOUS (the achiever/binding cell is genuinely present, value-correct), AND
(b) the single named gap is PRECISELY the §4 chart obligation (NOT a vacuous `sorry` that smuggles the
    value), AND
(c) it composes with `routeStepOf`/`routeAtlasOf`/`routeM_value_eq` already GREEN.

Two candidate shapes I'm weighing:
- SHAPE A: keep BranchData-producer as a NAMED HYPOTHESIS (`hbranch`), and additionally prove a lemma that
  "IF a BranchData with an achiever cell exists THEN the value folds to ½·minAdm" — i.e. don't construct
  the producer, just prove the value-consequence conditional on it. The named gap = "produce BranchData".
- SHAPE B: define a sharper structure `R1Section4Data M₀ M` that carries the achiever cell EXPLICITLY
  (its T*-profile split + achieverPivotWitness) PLUS the named-gap non-binding cells, and a producer
  `R1Section4Data → BranchData` that's GREEN, leaving only "construct R1Section4Data" (= the §4 chart
  gap) named. This exposes the achiever cell as filled, isolating the gap to the non-binding cover.
</task>

<output_contract>
1. RECOMMEND Shape A, Shape B, or a better Shape C (one paragraph: which, and the single deciding reason).
2. If B/C: the exact Lean structure fields + the producer signature (pin types against the context above).
   Name precisely where the achiever cell's T*-profile `ChainDimSplit` is constructed vs named-gapped —
   is the T*-profile split itself constructible NOW (from T* + a Fin.induction width-drop), or is it part
   of the gap?
3. The SINGLE named obligation, stated as a Lean signature (what exactly is sorried / hypothesised).
4. The non-vacuity guard: what concrete check confirms the skeleton is not the degenerate single-cell
   read (which the controller explicitly flagged as a trap).
5. Flag any place my framing assumes something false about the math.
Keep it under ~400 words. Mark INFERENCE vs FACT where you're guessing about my codebase.
</output_contract>

<grounding_rules>
You do not have my repo. Reason from the decl signatures I gave (treat them as FACT). Anything about
Lean tactic behaviour or Mathlib lemma availability that you cannot ground in what I stated: mark [INFERENCE].
Do NOT emit long proof scripts — I want the SKELETON SHAPE decision + the named-gap signature, not a proof.
