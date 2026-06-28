import DLNFibre.DLN.RLCT.Validate.RouteMFlatStructV

/-!
# `RouteMFlatLDU` — the LDU-lens structured chart + its decoder-agnostic rate (∀M, sub-tide 1)

The INTERIOR-branch achiever chart needs a **monomial** Jacobian `|det Dφ| = ∏_j |u_j|^{leafH j}`
(the `NodeAchieverChart.cov`/`monomialIntegrand` divergence). The banked FREE-K chart
`phiFlatStructV` (`RouteMFlatStructV`) reads each per-boundary Schur K-core block as a FREE matrix
coordinate, so its frame Jacobian carries `∏_s |det K_s|^{r_s + c_s}` — for a `t × t` K-core with
`t ≥ 2`, `det K_s` is a degree-`t` POLYNOMIAL, NOT a monomial. Hence the FREE-K `phiFlatStructV`
Jacobian is provably NOT a monomial for `t ≥ 2`, and the free-K interior contract
(`RouteMInteriorContract.routeMCore_box_diverges_interiorContract`) is **SUPERSEDED**: its `cov`
hypothesis cannot be satisfied for the general (interior) case. See
`threads/80-genM-nodechart/interior-cov-spec.md` (+ Codex xhigh consult) for the full wall-check.

The fix (Route A): read the K-core through an LDU lens (as the `(3,3,3,3)` `Kparam3333` does — free
coords `(x1,x2,x3,x4) ↦ [x1, x1·x2, x1·x3, x1·x2·x3 + x4]`, K-core det the MONOMIAL `(x1)²`).
Concretely, PRECOMPOSE the structured decoder with a flat reparam `reparam : (Fin N → ℝ) → (Fin N → ℝ)`
LDU-coordinatizing the K-slots — `genBlkFlatStruct M t ha (reparam x)`.

**Sub-tide 1 (this module): the rate transfers under ANY such reparam, decoder-agnostically.** The
rate identity `routeMCore (phiGen v B) = v² · VvalGen v B` (`routeMCore_phiGen`) holds for ANY decoder
`B` with a normalized identity boundary; `genBlkFlatStruct M t ha y` has `Bmat 0 = reindex 1`,
`Rmat 0 = 0` for EVERY decoder argument `y` (`hC0_struct_gen`). So precomposing with any `reparam`
fixing the pivot coordinate (so the radial blow-up axis is preserved) keeps the rate:

  `routeMCore (phiFlatLDU reparam x) = (x p)² · UvalLDU reparam x`.

This banks the LDU-chart SKELETON + confirms the rate is robust to the K-lens, isolating the remaining
obligations: (item-1) the specific LDU `reparam` on the K-slots; (item-3) the `composeFold fs =
phiFlatLDU` map equality over opaque widths (the det-side bottleneck); (item-4) the monomial `cov`.
The SPECIFIC LDU `reparam` and the monomial det are NOT built here — only the rate-transfer contract.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (matrix algebra; the rate engine, no analysis).
-/

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The LDU-lens structured chart + its unit (any pivot-fixing K-reparametrization) -/

/-- **The LDU-lens structured achiever chart** `phiFlatLDU reparam x := phiGen (x p) M t
(genBlkFlatStruct M t ha (reparam x)) hle` — the structured chart with the decoder argument run
through a flat reparam `reparam` (the K-slot LDU lens; identity elsewhere). The radial scalar is read
from the ORIGINAL `x` at the pivot `p = ⟨0,_⟩`, so a pivot-fixing `reparam` keeps the radial axis. -/
noncomputable def phiFlatLDU (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (reparam : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (x : Fin (routeMAmbient M) → ℝ) : Fin (routeMAmbient M) → ℝ :=
  phiGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha (reparam x)) (hleStruct M t ha)

/-- **The LDU-lens unit factor** `UvalLDU reparam x := VvalGen (x p) M t (genBlkFlatStruct M t ha
(reparam x)) hle` — the radial quotient `routeMCore (phiFlatLDU x) / (x p)²`. -/
noncomputable def UvalLDU (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (reparam : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (x : Fin (routeMAmbient M) → ℝ) : ℝ :=
  VvalGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha (reparam x)) (hleStruct M t ha)

/-- **The rate transfers to the LDU-lens chart ∀M, for ANY reparametrization `reparam` (NO bridge)**:
`routeMCore M (phiFlatLDU reparam x) = (x p)² · UvalLDU reparam x`. Directly from the
decoder-agnostic `routeMCore_phiGen` + the general-`x` identity-boundary `hC0_struct_gen` (which
holds for the decoder argument `reparam x` exactly as for any flat vector — it reads only the
x-independent `Bmat 0`/`Rmat 0`). The radial scalar `x p` is unchanged by `reparam` (read from the
ORIGINAL `x`). The `NodeAchieverChart.leaf_integrand` rate factor for the LDU interior chart. -/
theorem routeMCore_phiFlatLDU (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M)
    (reparam : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (phiFlatLDU M t ha hN reparam x)
      = (x (structPivot M hN)) ^ 2 * UvalLDU M t ha hN reparam x :=
  routeMCore_phiGen (x (structPivot M hN)) M t (genBlkFlatStruct M t ha (reparam x))
    (hleStruct M t ha)
    (hC0_struct_gen M t ha (x (structPivot M hN)) (reparam x))

/-- **`0 ≤ UvalLDU`** — sum of squares (banked `VvalGen_nonneg`), for any reparametrization. -/
theorem UvalLDU_nonneg (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M)
    (reparam : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (x : Fin (routeMAmbient M) → ℝ) :
    0 ≤ UvalLDU M t ha hN reparam x :=
  VvalGen_nonneg _ M t _ _

/-- **The identity reparametrization recovers `phiFlatStructV`** — `phiFlatLDU` with `reparam = id`
IS the banked FREE-K chart. Confirms `phiFlatLDU` is a genuine generalization (the free-K chart is
the `id` lens), not a re-definition. -/
theorem phiFlatLDU_id (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M)
    (x : Fin (routeMAmbient M) → ℝ) :
    phiFlatLDU M t ha hN id x = phiFlatStructV M t ha hN x := rfl

/-- **Non-vacuity of the rate transfer**: at the identity lens, `routeMCore_phiFlatLDU` reproduces
the banked free-K rate `routeMCore_phiFlatStructV` (the rate is genuinely transferred, not vacuous). -/
example (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (hN : 0 < routeMAmbient M)
    (x : Fin (routeMAmbient M) → ℝ) :
    routeMCore M (phiFlatStructV M t ha hN x)
      = (x (structPivot M hN)) ^ 2 * UvalStructV M t ha hN x := by
  rw [← phiFlatLDU_id M t ha hN x, routeMCore_phiFlatLDU]
  rfl

end DLNFibre.DLN.RLCT
