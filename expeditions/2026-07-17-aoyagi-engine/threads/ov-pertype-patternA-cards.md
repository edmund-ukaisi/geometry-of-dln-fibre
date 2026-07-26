# Statement cards — over-vanishing per-type CONCRETE facts, PATTERN A (7 leaves, p1=20)

Seat: the PATTERN-A over-vanishing per-type grind. Builds the 7 remaining pattern-A leaves
(`p2 ∈ {1,5}`, `p3 ∈ {1,5,6,7}`; the coinciding `(20,1,1)` is the `a3f030` seat's template
`Corank2OverVanishCanon334`). Each leaf mirrors that PROVEN template; the shared leaf-independent
lemmas `coreGen_eWrap_entry`, `A1_··`, `blockShear_covers_cubic` are REUSED from
`OverVanishCanon334` (not re-derived). Branch `aoyagi-r2ov-patternA` off `8113eb62c`.

Modules (one per leaf), namespace `DLNFibre.DLN.Aoyagi.OverVanishA_<p1>_<p2>_<p3>`:

| leaf `(p1,p2,p3)` | module | `vm` | block | φ degree | cover atom |
|---|---|---|---|---|---|
| (20,1,5) | `Corank2OverVanishA_20_1_5` | `u₁·u₅·u₂₀` | {12,13,14,15} | 2 | **quadratic** |
| (20,1,6) | `Corank2OverVanishA_20_1_6` | `u₁·u₆·u₂₀` | {12,13,14,15} | 3 | **cubic** |
| (20,1,7) | `Corank2OverVanishA_20_1_7` | `u₁·u₇·u₂₀` | {12,13,14,15} | 3 | **cubic** |
| (20,5,1) | `Corank2OverVanishA_20_5_1` | `u₁·u₅·u₂₀` | {16,17,18,19} | 2 | **quadratic** |
| (20,5,5) | `Corank2OverVanishA_20_5_5` | `u₅·u₂₀`     | {16,17,18,19} | 3 | **cubic** |
| (20,5,6) | `Corank2OverVanishA_20_5_6` | `u₅·u₆·u₂₀` | {16,17,18,19} | 3 | **cubic** |
| (20,5,7) | `Corank2OverVanishA_20_5_7` | `u₅·u₇·u₂₀` | {16,17,18,19} | 3 | **cubic** |

All 7 build sorry-free; all load-bearing results (`canon_domination`, `canon_hentry`,
`canon_foldedJac`, the cover supersets) are axiom-clean `[propext, Classical.choice, Quot.sound]`
(force-elaborated `#print axioms`; NO `sorryAx` — the Core Tonelli sorry does NOT enter, since
`canon_domination` rides the pure-algebra `monoSumSqGerm_le_of_regSeq_entries`).

## DEVIATION from the recipe (flagged) — cover-atom criterion is per-φ-DEGREE, not coinciding

The recipe / `a3f030`'s data file said "coinciding `p2=p3` ⇒ cubic cover, else quadratic". This is
WRONG. My INDEPENDENT sympy derivation (decorrelated from `a3f030`; the φ VALUES agree term-by-term)
shows the ACTUAL max-degree of φ per leaf: only `(20,1,5)` and `(20,5,1)` are genuinely quadratic;
`(20,1,6),(20,1,7),(20,5,6),(20,5,7)` carry a degree-3 φ term (e.g. `(20,1,6)`
`φ_12 = -(u₀·u₁₀ + u₁₆·u₅·u₆)`, the `u₁₆·u₅·u₆` cubic). The quadratic atom
`image_comp_blockShear_superset` (needs `‖φ x‖ ≤ C·r²` for all `r`) does NOT apply to a genuinely
cubic φ; those four use the CUBIC atom (`‖φ x‖ ≤ 2r³`, `r ≥ 1`; `leafR ≥ 1`). Same issue in
pattern B (relayed via `main`).

## Setup / conventions (all leaves)

- `idxCanon = ⟨⟨20,_⟩, ⟨p2,_⟩, ⟨p3,_⟩⟩ : Idx` (`NativeFan334.Idx`).
- `gCanon = blockBlowupMap S1 20 (nativeChart1 20 (blockBlowupMap (σC1 20) p2 (blockBlowupMap
  (σC2 20) p3 ·)))`; `gFlat_idxCanon : gFlat idxCanon = gCanon := by funext w; rfl`. All leaves share
  `nativeChart1 20 / nativeSel 20 / nativePerm 20 / t1P20 / t2P20 / cperm20` (only `p2,p3,vm,φ` vary).
- `Ψ = psiCanon = blockShear phiCanon`; `phiCanon` places the negative of each column-`c=1` reg-seq
  entry's correction into the block, reading only kept (outside-block) coords.
- reg-seq drops column `c=2` (pattern A): `pairsCanon = {(r,0),(r,1) : r∈0..3}`,
  `Scanon = pairsCanon.image finProdFinEquiv`; `zc`: `(r,0) ↦ {0,2,3,4}`, `(r,1) ↦ block`;
  `Zcanon = {0,2,3,4} ∪ block`.

The 8 reg-seq entry values per leaf were `sympy`-verified END-TO-END against the Lean `gFlat` (the
faithful `blockBlowupMap`/`nativeSel20`/`nativePerm20`/`blockShear` composite): `E[r][c](gFlat idx
(psiCanon u)) = vm(u)·u_{zc(r,c)}` EXACTLY, all 8 entries, all 7 leaves (independent re-derivation
matching `ov-pertype-16leaf-data.md` @ `4ceface15`).

---

> **Claim (1′) — the 8 reg-seq entry identities.** For each pattern-A leaf, each reg-seq `coreGen`
> entry of the folded chart pulls back to `vm·(single straightened coordinate)`.
>
> - **Lean:** `OverVanishA_<p1>_<p2>_<p3>.canon_hentry` (7 leaves).
> - **Gloss.** `∀ u, ∀ k ∈ Scanon, coreGen dvec eWrap k (gFlat idxCanon (psiCanon u)) =
>   (∏ d, (u d)^(vmExpCanon d)) · u (zcCanon k)`.
> - **Proved.** The 8 identities per leaf, unconditionally, via `coreGen_eWrap_entry` +
>   `Matrix.mul_apply`/`Fin.sum_univ_three` + a `decide`-powered `simp` over the folded composite +
>   `ring`. **Status.** sorry-free, axiom-clean.

> **Claim (piece 4, per-type) — the product-germ domination (PRIMARY deliverable).** The folded loss
> dominates `vm²·∑_Z z²` near every point.
>
> - **Lean:** `OverVanishA_<p1>_<p2>_<p3>.canon_domination` (7 leaves).
> - **Gloss.** `∀ u, monoSumSqGerm vmExpCanon Zcanon u ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
>   (gFlat idxCanon ∘ psiCanon)) u`.
> - **Proved.** Unconditionally, by feeding the 8 entry identities to the (ii)
>   `monoSumSqGerm_le_of_regSeq_entries` (reindex `S ≃ Z` via `hzc_inj`/`hzc_img`). Pure algebra — does
>   NOT touch the Core Tonelli bridge. **Status.** sorry-free, axiom-clean.

> **Claim (2) — the straightening `Ψ`.** `Ψ = psiCanon` is a det-1 unipotent shear fixing
> `supp(vm)`/`supp(jacExp)`.
>
> - **Lean (per leaf):** `jacDet_psiCanon` (`= 1`), `differentiable_psiCanon`,
>   `psiCanon_apply_offblock`, `phiCanon_keep`/`phiCanon_read`, `hzc_inj`/`hzc_img`.
> - **Proved.** All, unconditionally. **Status.** sorry-free, axiom-clean.

> **Claim (3) — the folded Jacobian (`hW`).** Folding `Ψ` leaves the monomial Jacobian weight
> unchanged.
>
> - **Lean:** `OverVanishA_<p1>_<p2>_<p3>.canon_foldedJac` (7 leaves).
> - **Gloss.** `∀ u, |jacDet (gFlat idxCanon ∘ psiCanon) u| = jacWeight (jacExp idxCanon) u` — chain
>   rule (`|jacDet Ψ| = 1`) + `hjac_gFlat` + `jacWeight_fixOn` (`Ψ` fixes every binding axis of
>   `jacExp idxCanon`, all `< 12`, disjoint from the block). **Status.** sorry-free, axiom-clean.

> **Claim (cover) — cover-transport.** The folded chart's image over `closedBall 0 r` sits inside the
> base chart's image over the inflated ball.
>
> - **Lean:** quadratic leaves `image_comp_psiCanon_quad_superset` (inflation `r + 2r²`, via the (ii)
>   generic `image_comp_blockShear_superset`); cubic leaves `image_comp_psiCanon_cubic_superset`
>   (inflation `r + 2r³`, `r ≥ 1`, via the template's generic `blockShear_covers_cubic`). Supporting:
>   `phiCanon_norm_bound`, `psiCanon_cubic_cover` (cubic leaves).
> - **Proved.** Unconditionally (cubic needs `1 ≤ r`; `leafR ≥ 1`). **Status.** sorry-free, axiom-clean.
> - **Caveat.** Per-leaf inflation differs (quadratic `r+2r²` for `(20,1,5),(20,5,1)`; cubic `r+2r³`
>   for the other 5) — see the DEVIATION above. The step-6 assembly transports each chart by its own
>   atom over `native_hcover`, so uniform inflation is not required.

---

## Feeds

Consumed by the `a3f030` σ_{p1}-transport (`p1=20` → all 9 dominants) then the ∀-144 assembly. The
public API name-matches the `(20,1,1)` template verbatim, so the transport can dispatch uniformly
over the 8 pattern-A leaves (7 here + `(20,1,1)`).
