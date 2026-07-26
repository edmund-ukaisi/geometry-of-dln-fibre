# Statement cards — over-vanishing per-type PATTERN-B leaves (`p1=20`, `p2 ∈ {6,7}`)

Seat: the PATTERN-B over-vanishing per-type concrete grind (feeds a3f030's `σ_p1`-transport → ∀-144).
Modules: `lean/DLNFibre/DLN/Aoyagi/Corank2OverVanishB_20_{p2}_{p3}.lean`, one per leaf, namespaces
`DLNFibre.DLN.Aoyagi.OverVanishB_20_{p2}_{p3}`. Base: `expedition/aoyagi-r2overvanish-pertype @8113eb62c`
(the PROVEN `(20,1,1)` template `Corank2OverVanishCanon334`, imported for `coreGen_eWrap_entry`,
`A1_00..A1_32`, and the generic `blockShear_covers_cubic` atom). All results axiom-clean
`[propext, Classical.choice, Quot.sound]` (`#print axioms`; NO `sorryAx` — `canon_domination` rides the
pure-algebra `monoSumSqGerm_le_of_regSeq_entries`, not the step-6 Tonelli bridge).

## The 8 leaves (pattern B = `p2 ∈ {6,7}` = the node-2 pivot; drops reg-seq column `c = 1`)

| leaf `(p1,p2,p3)` | coinciding | `vm` | straighten-block | φ max-deg | cover atom |
|---|---|---|---|---|---|
| `(20,6,1)` | no  | `u₁·u₆·u₂₀`  | `{12,13,14,15}` | 3 | cubic |
| `(20,6,5)` | no  | `u₅·u₆·u₂₀`  | `{12,13,14,15}` | 3 | cubic |
| `(20,6,6)` | yes | `u₆·u₂₀`     | `{12,13,14,15}` | 3 | cubic |
| `(20,6,7)` | no  | `u₆·u₇·u₂₀`  | `{12,13,14,15}` | 2 | quadratic |
| `(20,7,1)` | no  | `u₁·u₇·u₂₀`  | `{16,17,18,19}` | 3 | cubic |
| `(20,7,5)` | no  | `u₅·u₇·u₂₀`  | `{16,17,18,19}` | 3 | cubic |
| `(20,7,6)` | no  | `u₆·u₇·u₂₀`  | `{16,17,18,19}` | 2 | quadratic |
| `(20,7,7)` | yes | `u₇·u₂₀`     | `{16,17,18,19}` | 3 | cubic |

**Cover-atom DEVIATION from the template recipe (flagged to controller, confirmed).** The recipe's
"coinciding→cubic, non-coinciding→quadratic" split is WRONG for pattern B: the atom depends on the
leaf's ACTUAL φ max-degree, not coincidence. Only `(20,6,7)` and `(20,7,6)` are genuinely quadratic; the
other 6 — including the 4 NON-coinciding `(6,1),(6,5),(7,1),(7,5)` — carry a degree-3 φ term (e.g.
`(20,6,1)` `φ₁₂ = -(u₀·u₁₁ + u₁·u₁₆·u₇)`, the `u₁·u₁₆·u₇` is cubic) and use the cubic cover atom
(`r ↦ r + 2r³`, `r ≥ 1`; `leafR ≥ 1`). a3f030's `@4ceface15` φ VALUES are correct (verified end-to-end);
only its quad/cubic LABELS were off — this seat's Lean `ring` and the independent sympy both confirm the
values.

**Independent cross-check (this seat).** `expeditions/…/threads/ov-pertype-patternB/patternB_verify.py`
reconstructs the Lean `gFlat` faithfully (`blockBlowupMap`/`nativeSel 20`/`nativePerm 20`/`blockShear`
composite) and checks each leaf's 8 reg-seq entries collapse to `vm·u_zc` symbolically. It reproduces the
PROVEN `(20,1,1)` template exactly (pipeline-fidelity witness) AND verifies all 8 pattern-B leaves.
`gen_modules.py` emits the 7 sibling modules from the proven `(20,6,7)` template + per-leaf data.

---

## Per-leaf deliverables (identical shape across the 8; `X = 20_{p2}_{p3}`)

> **Claim (1′) — the 8 reg-seq entry identities.** `OverVanishB_X.canon_hentry` :
> `∀ u, ∀ k ∈ Scanon, coreGen dvec eWrap k (gFlat idxCanon (psiCanon u)) = (∏ d, (u d)^vmExpCanon d) · u (zcCanon k)`.
> Pattern B keeps reg-seq columns `c = 0, 2` (`Scanon = {0,2,3,5,6,8,9,11}`); each of the 8 entries of
> the folded chart `gFlat idxCanon ∘ Ψ` equals `vm · u_{zc k}` — proved via `coreGen_eWrap_entry`
> (→ `(A1·A0)` entry) + `Matrix.mul_apply`/`Fin.sum_univ_three` + a `decide`-`simp` unfolding the whole
> folded composite to a polynomial + `ring`. sorry-free, axiom-clean.

> **Claim (piece 4, per-type) — the product-germ domination.** `OverVanishB_X.canon_domination` :
> `∀ u, monoSumSqGerm vmExpCanon Zcanon u ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gFlat idxCanon ∘ psiCanon)) u`.
> The folded loss dominates the product germ `vm²·∑_{Z} z²`. Via
> `monoSumSqGerm_le_of_regSeq_entries` fed the 8 entry identities. Pure algebra (NO Tonelli).
> sorry-free, axiom-clean. **← the headline deliverable feeding a3f030's transport.**

> **Claim (2) — the straightening `Ψ`.** `jacDet_psiCanon` (`= 1`), `differentiable_psiCanon`,
> `psiCanon_apply_offblock`, `phiCanon_keep`/`phiCanon_read`, `hzc_inj`/`hzc_img`. `Ψ = blockShear φ`
> is a det-1 unipotent shear fixing `supp(vm)` and `supp(jacExp)`. All sorry-free, axiom-clean.

> **Claim (3) — the folded Jacobian.** `OverVanishB_X.canon_foldedJac` :
> `∀ u, |jacDet (gFlat idxCanon ∘ psiCanon) u| = jacWeight (jacExp idxCanon) u`. Chain rule
> (`|jacDet Ψ| = 1`) + `hjac_gFlat` + `jacWeight_fixOn` (`Ψ` fixes every binding axis of `jacExp idxCanon`,
> all `⊆ {p2,p3,20}`, outside the block). sorry-free, axiom-clean.

> **Claim (cover) — cover-transport.** Non-coinciding-quadratic leaves `(20,6,7)`, `(20,7,6)`:
> `image_comp_psiCanon_superset` (`g '' closedBall 0 r ⊆ (g ∘ Ψ) '' closedBall 0 (r + 2r²)`) via the
> backbone `image_comp_blockShear_superset` + a quadratic `phiCanon_norm_bound`. Cubic leaves (the other 6):
> `image_comp_psiCanon_cubic_superset` (`… closedBall 0 (r + 2r³)`, `r ≥ 1`) via the template's generic
> `blockShear_covers_cubic` + a cubic `phiCanon_norm_bound`/`psiCanon_cubic_cover`. All sorry-free,
> axiom-clean.

## Wiring note (for the controller / aggregator)

These 8 modules are NOT imported by `DLNFibre.lean` (single-writer aggregator — this seat does not edit
it). To wire: add the 8 `import DLNFibre.DLN.Aoyagi.Corank2OverVanishB_20_{p2}_{p3}` lines at the end of
`DLNFibre.lean`. They feed a3f030's `σ_p1`-transport (`p1=20` canonical → all 9 dominants → ∀-144).
