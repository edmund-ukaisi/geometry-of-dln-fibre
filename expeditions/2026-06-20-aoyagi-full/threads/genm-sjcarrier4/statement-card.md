# Statement card — the non-terminal linear-generator carrier + support-faithful block-elimination (Phase-2, piece 1)

Thread `genm-sjcarrier4` (tide, off `origin/expedition/aoyagi-full` @ `c261fb4a`). Branch `genm-sjcarrier4`.
Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJLinGen.lean` (new).
The R1-UPPER final gate → `sjJointResolution` (`RouteMSJResolution.lean:803`), pure R-BLOWUP route.

> **Claim.** The `(S,J)` recursion operates on generators that are still LINEAR FORMS in the active
> (unresolved) block coordinates, not yet monomials; the `SJSupport` ledger (`RouteMSJLedger`) is
> terminal-only data. This module supplies the **non-terminal linear-generator carrier**
> `SJLinGenState` and proves the **support-faithful block-elimination row-mix** — the generator-by-
> generator faithfulness that a `frobSq`/`pref·frobSq` equality cannot certify (the sharp risk Codex
> flagged on `genm-sjcarrier3`). This is Phase-2 **piece 1** (the block-elimination generator map at
> opaque widths). Pieces 2–3 (the recursion + the matrix-box→ledger change-of-variables) remain;
> `sjJointResolution` is UNTOUCHED.

## Lean (all in `DLNFibre.DLN.RLCT`, `RouteMSJLinGen.lean`)

- **Carrier.** `structure SJLinGenState (ζ ν ι) (d)` with `supp : SJSupport ι d` (the accumulated
  exceptional-divisor monomial prefix per generator) and `coeff : ζ → ι → ν → ℝ` (each generator `i`,
  in spectator context `z`, is the linear form `∑ᵥ coeff z i v · x v` in the active variables `x`).
  Evaluations: `residual G z x i = ∑ᵥ coeff z i v · x v`; `gen G u z x i = genMonomial supp i u ·
  residual` (MONOMIAL prefix × LINEAR residual); `loss G u z x = ∑ᵢ (gen …)²`. `ζ` = spectator/unit
  (downstream, absorbed gauge), `ν` = active linear variables, `ι` = generators.
- **Generator-level primitives (outer namespace).** `genMonomial_congr_supp` (a monomial is determined
  by its exponent ROW `e i` — the datum `frobSq` cannot read); `sharedDivisorExp_const` (the shared
  divisor of a constant support `s` is `s`).
- **`loss_ofMatrix` / `loss_ofMatrix_product`** (the base / entry point): the matrix-box loss
  `frobSq (rmatMul A₀ Q)` IS the carrier loss of `ofMatrix` at the active variable `Y = A₀·Q`
  (support `≡ 0`, generators = product entries). The object `gammaPeelIntegral` integrates, now held by
  the carrier.
- **`radialStep` / `gen_radialStep` / `loss_radialStep`** (the Case-2 single radial): prepending a
  fresh fully-shared exceptional divisor `u₀` (`supp ↦ prependColumn (fun _ ↦ 1) supp`) multiplies the
  loss by `u₀²`: `loss (radialStep G) (u₀ ::: u) = u₀² · loss G u`. The generator-level form of
  `corankStep`'s `frobSq((u•Δ)·Q) = u²·frobSq(Δ·Q)`, the divisor now visible PER GENERATOR (generalises
  the ledger's `sjLoss_prependColumn_one` from monomial generators to linear ones).
- **`rowMix` / `residual_rowMix` / `gen_rowMix` / `gen_rowMix_const` / `loss_rowMix`** (the block-elim
  row-mix, precision-scoped after review): under the `Z`-independent det-1 unit block-elimination the
  generators mix by a matrix `R`. `gen_rowMix` is the CONDITIONAL identity `gen (rowMix R s' G) j = ∑ᵢ
  R j i · gen G i` under the support-homogeneity side condition `hsh : R j i ≠ 0 → G.supp i = s' j`.
  **The content is entirely inside `hsh`** — the lemma is the honest reduction "block-elim faithfulness
  ⟺ `hsh` on the step matrix", NOT a proof that a real Step-3 matrix (`invSchurLeft`/`invSchurRight`)
  satisfies `hsh` (that fails for arbitrary `R` and is deferred to the recursion, which synchronises
  supports per fresh block). `gen_rowMix_const` discharges `hsh` UNCONDITIONALLY at a fresh block
  (common support `s` — the post-radial state the elimination acts on): there any `R` mixes only
  equal-support generators. This is the datum `pref·frobSq = …` (`corankStep_prefactor`) cannot read
  (which generators share a divisor). `loss_rowMix`: the loss under the (conditional) mix is `∑ⱼ (∑ᵢ
  R j i · genᵢ)²`.
- **`sharedDivisorExp_rowMix_const`** (constant-support consistency read-back): at a fresh block, both
  sides reduce to `s ℓ` (`sharedDivisorExp (rowMix R (fun _↦s) G).supp = sharedDivisorExp G.supp`). It
  does NOT inspect `R` — it is the generator-level statement that a constant monomial prefix is its own
  shared divisor (the `sharedDivisorExp_prependColumn_succ` family), not a proof that a general
  block-elimination preserves the support (that is the deferred `hsh` discharge).
- **`loss_blockSplit`** (the block-split shape): partitioning the generators over a sum-type index
  `ι_p ⊕ ι_c` splits the loss additively (`∑ pivot² + ∑ corank²`). This is the index-partition SHAPE of
  `frobSq_blockDiag_split` (`RouteMSJStep3`) — true for any sum-indexed state; it carries none of that
  lemma's Schur-complement content (the reindexing into pivot/corank blocks is the deferred recursion).
- **Non-vacuity (in-file `example`).** The row-mix at the genuine `(2,2,2)` Case-2 unit-triangular
  shear `R = [[1,0],[c,1]]`: `gen'₁ = c·gen₀ + gen₁` (a genuine non-trivial mix) with the
  shared-divisor exponents PRESERVED. The faithfulness core fires on the actual mechanism.

## Proved / Assumed / Cited / Deferred

- **Proved.** All the above, sorry-free. Forced `#print axioms` (`lake env lean` scratch,
  force-elaborated): `gen_rowMix`, `loss_rowMix`, `sharedDivisorExp_rowMix_const`, `loss_radialStep`,
  `loss_ofMatrix_product`, `loss_blockSplit`, `genMonomial_congr_supp`, `sharedDivisorExp_const` all =
  `[propext, Classical.choice, Quot.sound]` (clean-three). **S2-FREE — no `monomial_rlct`, no measure
  theory** (pure algebra: `genMonomial`, `frobSq`, finite sums).
- **Assumed (carried as hypotheses, honest — this is where the real difficulty sits).**
  `gen_rowMix`/`loss_rowMix` carry the support-homogeneity hypothesis `hsh : R j i ≠ 0 → G.supp i = s'
  j`. **The reviewer + a fresh decorrelated Codex (`codex/review-rowmix-answer.md`) both flag that `hsh`
  contains the ENTIRE "does the real block-elimination preserve shared divisors" obligation** — a real
  Step-3 matrix generically mixes rows of differing support and does NOT satisfy `hsh` unless the
  recursion has already synchronised supports. So `gen_rowMix` is the honest REDUCTION (faithfulness ⟺
  `hsh`), not a discharge. `gen_rowMix_const` discharges `hsh` UNCONDITIONALLY only at a fresh block
  (constant support — the post-radial state); proving a general `(S,J)` step reaches/preserves that
  configuration is the deferred recursion (piece 2).
- **Cited.** none new. Reuses the banked ledger (`RouteMSJLedger`: `genMonomial`, `sharedDivisorExp`,
  `prependColumn`, `genMonomial_prependColumn`) and `frobSq`/`rmatMul` (`MatMulFibre`).
- **Deferred (Phase 2/3 — the remaining mountain, reported precisely; decorrelated-Codex-confirmed).**
  1. The `(S,J)` RECURSION iterating radial + block-elimination down to the terminal Σbᵢ² (a
     Nat-measure descent on corank / #generators, over the finite `(S,J)` cover).
  2. **Decisively — the matrix-box → ledger CHANGE OF VARIABLES.** Going from `gammaPeelIntegral`
     (an `∫⁻` over MATRIX boxes of `frobSq(A₀·Q)^{−c'}`) to the ledger's
     `sjLoss_terminal_lintegral_lt_top` (an `∫⁻` over the exceptional coordinates `u` of
     `(∑bᵢ²)^{−c'}·Jac`) requires CONSTRUCTING the iterated-blow-up chart maps (each MP up to a
     monomial Jacobian), the finite chart cover, and the per-chart `lintegral` transport. NONE of this
     is banked; the pointwise identities (`corankStep`, STEP-3) and the terminal finiteness cannot
     shortcut it. Codex (`codex/scope-answer.md`, Q1): **~65–75% genuinely-new construction,
     multi-module, hundreds–low-thousands of LoC.**
  3. The measure assembly bounding `gammaPeelIntegral < ⊤` over the finite `pivotChartCover`.

  **`sjJointResolution` UNTOUCHED** (still the single named sorry at `RouteMSJResolution.lean:803`).

## Obstruction check (the WATCHED wall)

No new stratum obstruction: the generator map DOES decompose into iterated single-radial + support-
faithful block-elimination at every `(S,J)` — the row-mix faithfulness is exactly the "which generators
share a divisor" bookkeeping the design green-lit, and it is now proved at opaque widths. The (a)-BOUNDED
verdict is robust (Codex Q3: "I do not see a new stratum obstruction"). The sole barrier is the SIZE of
the unbanked CoV construction (deferred item 2), NOT a mathematical wall.

## Reviewer

**SURVIVED** (independent fidelity + soundness audit, decorrelated Codex xhigh corroborated). No
fidelity mismatch, no soundness break, `sjJointResolution` confirmed untouched (still `sorry` at
`RouteMSJResolution.lean:803`, not laundered). Forced-recompile `#print axioms` reproduced clean-three
on all named results (no `sorryAx`, no `monomial_rlct`). One substantive precision FINDING (addressed
this tide, in-file + card): the original "the faithfulness core / PRESERVES / proved at opaque widths"
language OVERSHOT — `gen_rowMix`'s content is conditional on `hsh` (the real block-elim obligation is
smuggled there), `sharedDivisorExp_rowMix_const` is a constant-support consistency read-back (does not
read `R`), and `loss_blockSplit` is an index-partition tautology (no Schur content). All three docstrings
+ the card were precision-edited to state the conditionality plainly, and `gen_rowMix_const` was added as
the honestly-unconditional fresh-block form. The math was correct and sorry-free throughout; the finding
was naming/overclaim, now corrected.

## Status

sorry-free; clean-three; `scripts/sorries` = 0 for the module. Isolated
`scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJLinGen` green (2710 jobs); FULL `scripts/lb DLNFibre`
green-gated (8748 jobs, no name clashes with siblings — `rg`-checked). Aggregator wired (import added at
the end, worktree copy). ~317 LoC. AxCheck: the load-bearing results' forced `#print axioms` confirmed
clean-three externally (twice — before and after the precision edits); NOT added to `AxCheck.lean`
(controller-owned single-writer) — **controller to add `gen_rowMix` / `gen_rowMix_const` /
`sharedDivisorExp_rowMix_const` / `loss_radialStep` / `loss_ofMatrix_product` to `AxCheck.lean` at
integration** (and, if wiring the SJ chain's axiom gate, `RouteMSJLedger`/`Terminal` too — currently
absent from AxCheck). Branch pushed to `origin/genm-sjcarrier4`.
