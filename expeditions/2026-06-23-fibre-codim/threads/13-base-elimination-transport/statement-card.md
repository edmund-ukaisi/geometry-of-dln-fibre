# Statement card — G2-2: the localized determinantal base presentation `A_loc/Iad ≅ Sd`

**Status:** reviewed (fidelity PASS — independent reviewer, 2026-06-24; squeeze genuinely earns the
hard direction `Iad ⊆ J`, axiom-clean, non-vacuous, no overclaim. Codex-decorrelated)
**Module:** `lean/DLNFibre/Core/DeterminantalBasePresentation.lean`
**Pinned commit:** `406befdf` on `expedition/fibre-codimension`
**Axioms (headline + key lemmas):** `[propext, Classical.choice, Quot.sound]` (axiom-clean)

## The claim (informal)

On the pivot chart of the rank-`≤ r` determinantal base of a single `p × q` matrix (the `N = 1`
stratum `dStratum q p`), inverting the top-left `r × r` pivot minor `detΔ` forces the bottom-right
block `B22 = B21 Δ⁻¹ B12` (the Schur relation). Hence the localized base ring `A_loc =
Localization.Away detΔ`, modulo its base ideal `Iad`, is the **free Schur localization**
`Sd = Localization.Away detSchurS` of the free coordinates `Δ ⊕ B12 ⊕ B21` — a regular ring of
dimension `δ = r(p + q − r)`. The eliminated block contributes the codimension `C = (p−r)(q−r)`.

## The Lean headline

```lean
noncomputable def basePresentationEquiv [IsAlgClosed k] [CharZero k] (q p r : ℕ)
    (hp : r ≤ p) (hq : r ≤ q) :
    (Localization.Away (detPivotPoly (k := k) q p r hp hq) ⧸ Iad (k := k) q p r hp hq)
      ≃ₐ[k] SchurLoc (k := k) q p r
```

where `Iad q p r hp hq = (sigmaIdeal (dStratum q p) r).map (algebraMap A_eng A_loc)` (the determinantal
base ideal pushed into `A_loc`), and `SchurLoc q p r = Localization.Away (detSchurS q p r)` (the free
Schur localization `Sd`).

## English gloss of each piece

- `A_loc = Localization.Away (detPivotPoly q p r hp hq)`: the engine coordinate ring
  `MvPolynomial (RepCoord (dStratum q p)) k` localized at the pivot minor `detΔ`.
- `Iad`: the (prime) localized determinantal base ideal.
- `Sd = SchurLoc q p r`: the free Schur localization `k[Δ, B12, B21]_detSchurS` (`#SchurVar = δ`).
- The equiv: `A_loc/Iad` is `Sd` as a `k`-algebra.

## Hypotheses

- `k` a field, `[IsAlgClosed k]`, `[CharZero k]` (for the base ideal `sigmaIdeal` to be prime and the
  codimension `= cCodim`, via the landed engine bricks).
- `r ≤ p`, `r ≤ q` (pivot block fits).

## How the hard direction is EARNED (correctness guard)

`A_loc/Iad ≅ Sd` requires the hard inclusion `Iad ⊆ J` (= injectivity of `Sd → A_loc/Iad`). It is
**proved, not assumed**, via the height squeeze (`map_Iad_eq_graphIdeal_forcedB22`):

1. `J = graphIdeal forcedB22` (the genuine forced value `forcedB22 = B21·adjΔ·B12 / detSchurS ∈ Sd`,
   via `IsLocalization.mk'`) and `Ψ(Iad)` are both **prime**.
2. `height J = C = (p−r)(q−r)` (landed `height_graphIdeal_forcedB22_eq`) and `height Ψ(Iad) = height
   Iad = C` (landed `height_map_sigmaIdeal_away_eq_cCodim` + `height_map_algEquiv`).
3. `J ⊆ Ψ(Iad)` (`graphIdeal_forcedB22_le_map_Iad`): each generator `X_b − C(forcedB22 b)`, times the
   unit `C(algebraMap detSchurS)`, is the `Ψ`-image of a bordered `(r+1)`-minor (which lies in `Iad`
   by `borderMinor_mem_sigmaIdeal` + `det_submatrix_multPoly_mem_sigmaIdeal`); unit-cancellation
   (`Ideal.unit_mul_mem_iff_mem`) gives the generator. The bordered-minor identity `(*)`
   (`blockAlgEquiv_borderMinor`): `blockAlgEquiv m_b = C detSchurS · X_b − C(forcedNum_b)`.
4. `height_strict_mono_of_is_prime` rules out `J ⊊ Ψ(Iad)` ⟹ `J = Ψ(Iad)` ⟹ `Iad = Ψ.symm J`.

So if the inclusion were strict, `height J` would be `< C` — contradicting `height J = C`. The squeeze
is load-bearing; nothing is skipped.

## Key supporting definitions/lemmas (this module)

- `blockAlgEquivLoc` (Ψ): `A_loc ≃ₐ[k] MvPolynomial B22block Sd`, localizing the landed `blockAlgEquiv`
  at `detΔ ↦ C detSchurS` (`IsLocalization.algEquivOfAlgEquiv` + the `k → B → Q` scalar tower).
- `borderMinor`, `borderMinor_mem_sigmaIdeal`, `blockAlgEquiv_borderMinor` (`(*)`).
- `graphIdeal_forcedB22_le_map_Iad` (step 2), `map_Iad_eq_graphIdeal_forcedB22` (step 3 squeeze).

## Landed engines reused (g2-2b / threads 11–12)

`blockAlgEquiv` (+ `_detPivot`), `repCoordReindex_{pivot,b22,b12,b21}`, `blockAlgEquiv_X_{pivot,b22,b12,b21}`,
`forcedNum`/`forcedB22`, `height_graphIdeal_forcedB22_eq`, `detSchurS_ne_zero`, `det_fromBlocks_scalar_eq`,
`det_submatrix_multPoly_mem_sigmaIdeal`, `height_map_sigmaIdeal_away_eq_cCodim` (= `height Iad = C`),
`cCodim_stratum_eq`, `graphIdealQuotientEquiv`/`graphIdeal_isPrime`, `height_map_algEquiv`.

## Witness

`(q, p, r) = (2, 2, 1)`: `#B22block = (2−1)(2−1) = 1 = C`, `#SchurVar = 1·(2+2−1) = 3 = δ`. The
presentation equiv is available there (the `example` blocks at the foot of the module).

## Aggregator

Not yet wired (single-writer). Controller to add: `import DLNFibre.Core.DeterminantalBasePresentation`.

## Caveats / scope

- This is the **localized** (pivot-chart) base presentation only — `G2-2`, rung 2 of ~6. The TOTAL
  presentation + flatness (`G2-3`) is the next, genuine wall.
- `Iad` and `J` stay internal to the proof; the exposed interface is `basePresentationEquiv` + the
  reused landed `height Iad = C`. Regularity / dimension `δ` follow from `Sd` being a poly localization.
