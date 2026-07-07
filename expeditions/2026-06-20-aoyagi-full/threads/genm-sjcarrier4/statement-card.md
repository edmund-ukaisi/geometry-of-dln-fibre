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
- **`rowMix` / `residual_rowMix` / `gen_rowMix` / `loss_rowMix`** (the faithfulness core): under the
  `Z`-independent det-1 unit block-elimination the generators mix by a matrix `R`. IF the mix is
  *support-homogeneous* (`R j i ≠ 0 → G.supp i = s' j` — each new generator combines only old
  generators sharing its support), THEN `gen (rowMix R s' G) j = ∑ᵢ R j i · gen G i` row-by-row and
  `loss (rowMix R s' G) = ∑ⱼ (∑ᵢ R j i · genᵢ)²`. The monomial prefix factors cleanly out of the mix
  because the mixed generators share a monomial — precisely what `pref·frobSq = pref·u²·residual`
  (`corankStep_prefactor`) cannot see.
- **`sharedDivisorExp_rowMix_const`** (the passive-prefactor invariant): at a fresh block (common
  support `s`), the block-elimination PRESERVES the shared-divisor exponents
  (`sharedDivisorExp (rowMix …).supp = sharedDivisorExp G.supp`) — the generator-level
  `sharedDivisorExp_prependColumn_succ`.
- **`loss_blockSplit`** (the corank decrement): partitioning the generators over a sum-type index
  `ι_p ⊕ ι_c` splits the carrier loss additively (pivot Morse energy + corank residual) — the
  generator-level shadow of `frobSq_blockDiag_split` (`RouteMSJStep3`).
- **Non-vacuity (in-file `example`).** The row-mix at the genuine `(2,2,2)` Case-2 unit-triangular
  shear `R = [[1,0],[c,1]]`: `gen'₁ = c·gen₀ + gen₁` (a genuine non-trivial mix) with the
  shared-divisor exponents PRESERVED. The faithfulness core fires on the actual mechanism.

## Proved / Assumed / Cited / Deferred

- **Proved.** All the above, sorry-free. Forced `#print axioms` (`lake env lean` scratch,
  force-elaborated): `gen_rowMix`, `loss_rowMix`, `sharedDivisorExp_rowMix_const`, `loss_radialStep`,
  `loss_ofMatrix_product`, `loss_blockSplit`, `genMonomial_congr_supp`, `sharedDivisorExp_const` all =
  `[propext, Classical.choice, Quot.sound]` (clean-three). **S2-FREE — no `monomial_rlct`, no measure
  theory** (pure algebra: `genMonomial`, `frobSq`, finite sums).
- **Assumed (carried as hypotheses, honest).** `gen_rowMix`/`loss_rowMix` carry the support-homogeneity
  hypothesis `R j i ≠ 0 → G.supp i = s' j` — the "mixes only same-support generators" condition Codex
  named; it is DISCHARGED at a fresh block (constant support), which is the state the recursion enters
  each `(S,J)` step (`sharedDivisorExp_rowMix_const` handles that case unconditionally).
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

## Status

sorry-free; clean-three; `scripts/sorries` = 0 for the module. Isolated
`scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSJLinGen` green (2710 jobs); FULL `scripts/lb DLNFibre`
green-gated (no name clashes with siblings — `rg`-checked). Aggregator wired (import added at the end,
worktree copy). AxCheck: the load-bearing results' forced `#print axioms` confirmed clean-three
externally; NOT added to `AxCheck.lean` (controller-owned single-writer) — **controller to add
`gen_rowMix` / `sharedDivisorExp_rowMix_const` / `loss_radialStep` / `loss_ofMatrix_product` to
`AxCheck.lean` at integration** (and, if wiring the SJ chain's axiom gate, `RouteMSJLedger`/`Terminal`
too — currently absent from AxCheck). Branch pushed to `origin/genm-sjcarrier4`.
