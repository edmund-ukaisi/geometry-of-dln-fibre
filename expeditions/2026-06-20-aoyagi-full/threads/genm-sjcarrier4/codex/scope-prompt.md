# Consult — scope + piece-1 formulation for closing `sjJointResolution` (R1-UPPER, Aoyagi DLN)

You are a decorrelated second model on a Lean 4 + Mathlib formalisation of Aoyagi's
RLCT computation for deep linear networks. **Leaning withheld** — give your own read.

## The single named sorry (the target)

`sjJointResolution` (`RouteMSJResolution.lean:803`), goal `gammaPeelIntegral M t ρ κ (c':ℝ) < ⊤` where

```
gammaPeelIntegral M t ρ κ c' :=
  ∫⁻ A' in paramsBoxM (tailChain M) 1,           -- A' : tail-chain layer params (box [-1,1])
    ∫⁻ A0 in matBox (M 0) (M 1) 1 ∩ pivotChart ρ κ,   -- A0 : Fin(M0)→Fin(M1)→ℝ, (ρ,κ)-minor a unit
      ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c'))
```

Hypotheses: strong IH `∀ M' : Fin(L+1+1)→ℕ, RouteMBoxThresholdFinite M'` (box-finiteness for every
ONE-SHORTER chain); `1 ≤ t ≤ min(M0,M1)`; `c' < minAdm M / 2` (the geometric threshold).
`prod (tailChain M) A'` is the layer-product of the remaining chain (a `Fin(M1)→Fin(M_last)→ℝ` matrix).
`frobSq X = ∑ᵢⱼ Xᵢⱼ²`.

## What is BANKED (sorry-free, clean-three axioms)

- **Ledger (`RouteMSJLedger`)** — the TERMINAL normal-crossing carrier at the generator level:
  `SJSupport ι d := ι → Fin d → ℕ` (support map: order to which exceptional divisor `u_ℓ` divides
  generator `bᵢ`); `genMonomial e i u = ∏_ℓ |u_ℓ|^{e i ℓ}`; `sjLoss e u = ∑ᵢ genMonomial²`;
  `sharedDivisorExp e ℓ = ⨅ᵢ e(i,ℓ)`. `sjLoss_terminal_lintegral_lt_top`: below the monomial
  threshold and given a dehomogenised generator, `∫⁻_{unitBox} (sjLoss e u)^{−c'}·∏|u_ℓ|^{h_ℓ} < ⊤`.
  `prependColumn a e` (radial ledger update, fresh divisor u₀ divides bᵢ to order a i);
  `sjLoss_prependColumn_one`: `sjLoss (prependColumn (fun _↦1) e)(u₀:::u) = u₀²·sjLoss e u`;
  `sharedDivisorExp_prependColumn_succ` (old divisors preserved — passive-prefactor invariant).
- **corankStep (`RouteMSJCorankStep`)** — the POINTWISE radial+Schur step (opaque widths):
  `frobSq((u • fromBlocks A B C D)·Q) = u²·(frobSq(A·Q̃_p) + frobSq(C·Q̃_p + Γ·Q_b))`,
  Q̃_p = Q_p + A⁻¹B·Q_b, Γ = D − CA⁻¹B (corank block, dimension decremented). `frobSq_smul_mul`.
- **STEP-3 (`RouteMSJStep3`)** — the Z-independent unit block-elimination at the frobSq level (opaque):
  `step3_blockFactor`: fromBlocks A B C D = invSchurLeft A C · (fromBlocks A 0 0 Γ) · invSchurRight A B
  (both unit factors det 1, functions of (A,B,C) only); `frobSq_step3_absorb` (units absorb into
  adjacent P/Z); `frobSq_blockDiag_split`: frobSq((fromBlocks A 0 0 Γ)·W) = frobSq(A·W_top) +
  frobSq(Γ·W_bot); `frobSq_identityChannel`: frobSq(A₀·fromBlocks 1 0 0 Z) = frobSq(A₀_left) +
  frobSq(A₀_right·Z) (isotropic split, ONLY when downstream has a literal identity channel).
- **PURE peels (`RouteMSJCorankPure`)** — integral-level, ISOTROPIC form only:
  `matBox_corank_dominates_absZ_lt_top`: ∫_z ∫_{Δ∈box}(frobSq Δ + W z)^{−c'} < ⊤ for c'<pq/2, W≥0, μZ<∞.
- **Pivot cover (`RouteMSJPivotChart`)** `pivotLocus_eq_iUnion`; boundary peel `sjBoundaryPeel` (CLOSED,
  reduces box integral to Σ over charts of gammaPeelIntegral). Charge budget `minAdm` recursion CLOSED.
- **NO banked lemma connects `∫⁻ frobSq(A0·Q)^{−c'}` over a matrix box to `∫⁻ sjLoss^{−c'}·Jac` over
  ledger coordinates** (the change-of-variables / constructed resolution map). I have grepped; it is absent.

## The route verdict (settled, do NOT relitigate)

The corank-≥2 core is BOUNDED via Aoyagi's **iterated explicit single-radial blow-up charts (Cases 1&2)**
threaded by the shared-divisor ledger, terminating at the terminal Σbᵢ² — NOT the atom/Gram-det route
(that over-counts the box on the null degenerate locus; DEAD). The ONE watched wall: "if the opaque-width
`corankStep` recursion cannot be made to reach (monomial)²·unit on a finite cover at the generator level,
THAT is the genuine wall."

## The remaining 3 pieces (per the prior tide's report)

1. **Block-elim generator map** (opaque widths): the generator MAP under the Z-independent unit reduction
   — a linear mix of generators = the corank decrement. Codex previously flagged: "`pref·frobSq = pref·u²·
   residual` is TOO COARSE to recover the support matrix; shared-divisor faithfulness must be proved
   row-by-row for generators."
2. **(S,J) recursion to terminal**: iterate Cases 1&2, Nat-measure descent on corank/#generators,
   terminating at the banked terminal.
3. **Measure assembly**: assemble per-chart finiteness into `gammaPeelIntegral < ⊤` over the finite cover.

## MY QUESTIONS (answer each, concise, concrete)

**Q1 (scope — the decisive one).** To go from `gammaPeelIntegral` (an honest `∫⁻` over MATRIX boxes of
`frobSq(A0·Q)^{−c'}`) to the ledger's `sjLoss_terminal_lintegral_lt_top` (an `∫⁻` over the resolution
coordinates `u` of `(∑bᵢ²)^{−c'}·Jac`), one must construct the iterated-blow-up CHANGE OF VARIABLES:
the explicit chart maps `Φ` (each measure-preserving up to a monomial Jacobian `∏|u_ℓ|^{h_ℓ}`), a finite
chart cover, and the `∫⁻` transport (`MeasurePreserving.lintegral_comp` / `lintegral_map` per chart with
the Jacobian weight). None of this is banked (only the POINTWISE identities `corankStep`/STEP-3 and the
TERMINAL `sjLoss` finiteness are). **Is closing `sjJointResolution` in one tide realistic, or is this
CoV/resolution-map construction a genuinely large unbanked build (multi-module, hundreds–thousands of
LoC) that no pointwise brick shortcuts?** Give your honest estimate of what fraction is bankable-plumbing
vs genuinely-new construction. If the latter dominates, say so plainly.

**Q2 (piece-1 formulation).** Given the banked frobSq bricks (`corankStep`, `frobSq_blockDiag_split`,
`frobSq_identityChannel`, `step3_blockFactor`) and the ledger (`prependColumn`, `sjLoss`), what is the
CLEANEST, genuinely-ADVANCING, sorry-free-buildable formulation of the "block-elimination generator map at
opaque widths" that (a) is NOT a mere restatement of a banked frobSq lemma, (b) tracks shared-divisor
faithfulness generator-by-generator, (c) mirrors the (2,2,2) Case111/Case222 mechanism? Concretely: what
Lean structure carries an INTERMEDIATE (non-terminal) generator state (generators are still LINEAR FORMS
in matrix entries, not monomials), and what is the type of the step map? Is there a clean intermediate
carrier, or does the generator level ONLY make sense at the terminal (making piece 1 vacuous until the
CoV of Q1 exists)?

**Q3 (obstruction check).** Is there any (S,J) stratum where the generator map does NOT decompose into
iterated single-radial (which would re-open the bounded-labor verdict)? Or is the (a)-bounded verdict
robust and the only barrier the sheer SIZE of the CoV construction (Q1)?

Be blunt. If the honest answer is "piece 1 is buildable as an algebraic brick but pieces 2+3 need the
large unbanked CoV, so the sorry cannot honestly close this tide," say exactly that.
