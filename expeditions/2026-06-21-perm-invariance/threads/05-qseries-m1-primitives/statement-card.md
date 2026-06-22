# Statement card — M1: `Core.QSeries` primitives

Thread 05 (perm-invariance expedition). The §5 generating-function primitives as `PowerSeries ℤ`
(`ℤ⟦X⟧`, `X` ≙ `q`), plus the basic shape facts that the L1 `(C, θ)`-extraction (M3) will consume.
This is M1 only — **defs + basic properties, NOT the §5 identities** (PEEL / Thm 5.5 / Thm 5.6 / the
extraction itself are later layers).

> **Claim.** The inverse q-Pochhammer `P s = ∏_{k=1}^s (1−q^k)^{-1}`, the Kostant factor
> `Pm N m = ∏_{i≤j} P (m (i,j))`, the multiplicity factor `Pmult h = ∏_i P (h i)`, and the Thm 5.6
> generating function `Qseries d r = ∑_{m ∈ kostantPartitions d r} q^{codimForm(extendℤ m)} · Pm m`
> are well-defined power series over `ℤ`; `P`/`Pm`/`Pmult` have constant term `1` and all coefficients
> `≥ 0`, and `Qseries` has all coefficients `≥ 0`. The geometric factor telescopes:
> `geomFactor k · (1 − X^k) = 1` for `k ≥ 1` (the inverse-Pochhammer reading).
>
> - **Lean:** module `DLNFibre.Core.QSeries` (`lean/DLNFibre/Core/QSeries.lean` @ `<commit-sha>`,
>   staged on branch `expedition/perm-invariance`; SHA to be pinned by the controller at commit).
>   Key names:
>   - defs: `geomFactor`, `P`, `Pm`, `Pmult`, `Qseries`, `upperPairs`, `NonnegCoeffs`
>   - constant term `1`: `constantCoeff_geomFactor`, `constantCoeff_P`, `constantCoeff_Pm`,
>     `constantCoeff_Pmult`  (all `constantCoeff (R := ℤ) · = 1`)
>   - non-negativity: `nonnegCoeffs_geomFactor`, `nonnegCoeffs_P`, `nonnegCoeffs_Pm`,
>     `nonnegCoeffs_Pmult`, `nonnegCoeffs_Qseries`; unfolded `coeff_*_nonneg` companions
>   - closure of the predicate: `nonnegCoeffs_one`, `NonnegCoeffs.mul`, `NonnegCoeffs.prod`
>   - telescoping: `geomFactor_mul_one_sub`
>   - small helpers: `P_zero` (`P 0 = 1`), `Pmult_const_zero`, `P_succ` (peel-top recurrence),
>     `coeff_geomFactor` (`@[simp]` coefficient formula)
> - **Gloss.** `geomFactor k` is the explicit geometric series `mk (fun n ↦ if k ∣ n then 1 else 0)`
>   — coefficient `1` at multiples of `k`, `0` elsewhere (`= (1−q^k)^{-1}`). `P s` is the product of
>   `geomFactor k` over `k ∈ Finset.Icc 1 s` (so `P 0 = 1`). `Pm N m` products `P (m p)` over the
>   upper-triangular pairs `upperPairs N = {p : p.1 ≤ p.2}`. `Pmult h` products `P (h i)` over `i`.
>   `Qseries d r` sums `X^{(codimForm N (extendℤ m)).toNat} · Pm N m` over `kostantPartitions d r`
>   (the real `Core.CTheta` objects). `NonnegCoeffs φ := ∀ n, 0 ≤ coeff n φ`; it holds of `1`, is
>   closed under `*` (antidiagonal sum of products of non-negatives) and `Finset.prod`
>   (`prod_induction`).
> - **Proved.** All of the above, unconditionally, axiom-clean. `#print axioms` of every named
>   result = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `Lean.ofReduceBool`).
>   Telescoping carries the hypothesis `1 ≤ k` (`geomFactor 0 = 1`, not an inverse of `1 − X^0 = 0`).
> - **Assumed.** None. (The `Qseries` exponent uses `(codimForm N (extendℤ m)).toNat`; on Kostant
>   partitions `codimForm ≥ 0`, so `toNat` is faithful — the M3 layer that reads off `cCodim` will
>   carry the `0 ≤ codimForm` fact where it needs the exact exponent; M1 does not assert it.)
> - **Cited.** None — every fact built from Mathlib `PowerSeries`/`Finset`/`Nat` primitives.
> - **Deferred (NOT done here, by design — later layers).** The §5 identities: the PEEL induction
>   (Thm 5.6 `Pmult d = ∑_{m⊢d} q^{codimForm} Pm m`), Thm 5.5, the S1–S4 chain, and the L1
>   `(C, θ)`-extraction (`lowestTerm(Qseries) = numTop · q^{cCodim}`). M1 is the bedrock these stand on.
> - **Status.** sorry-free + **reviewed** (fidelity PASS, reviewer + decorrelated Codex; see
>   `codex/geomfactor-fidelity-{prompt,answer}.md`). One docstring-prose tightening applied
>   post-review (restrict the geometric-series reading of `geomFactor` to `k ≥ 1`); no math change.

## Build / hygiene

- `lake build DLNFibre.Core.QSeries`: green (0 errors, 0 warnings in-file after long-line cleanup).
- `scripts/sorries`: 0 `sorry` / `#exit` / `native_decide` / `axiom` in `QSeries.lean`.
- Aggregator: `import DLNFibre.Core.QSeries` appended at the end of `lean/DLNFibre.lean`.
- Dependency rule honoured: imports only `DLNFibre.Core.CTheta` + Mathlib `PowerSeries`; no `DLN.*`.
- LoC: 227 lines (1 module).

## Reviewer focus (fidelity)

1. **Object match.** Does `Qseries` match the paper's Thm 5.6 LHS? The exponent is the committed
   `codimForm N (extendℤ m)` from `Core.CTheta` (the same form `cCodim`/`numTop` minimise), taken
   `.toNat`. `Pm` runs over `upperPairs` (`i ≤ j`) — matching the Kostant support; off-triangle
   entries of a Kostant `m` are `0`, and `P 0 = 1`, so the choice of index set there is immaterial
   to the value but `upperPairs` is the faithful support.
2. **Non-negativity is the load-bearing M3 input** (no cancellation in the lowest-term extraction):
   confirm `nonnegCoeffs_Qseries` says exactly `∀ n, 0 ≤ coeff n (Qseries d r)`.
3. **`geomFactor` is genuinely `(1−q^k)^{-1}`** — the telescoping `geomFactor_mul_one_sub` pins this
   for `k ≥ 1`; check the `1 ≤ k` hypothesis is the honest one.
