import DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

/-!
# `DLN.Aoyagi.Corank2GWrapDecomp` — #112 rung 5b: the DECOMPOSED presentation of the (3,3,4) chart

The (3,3,4) resolution chart `gWrap = sigmaPiv ∘ gFaithful` (`Corank2CoreGenWrap`) is EXACTLY the
banked-atom composite (pen-and-paper `pnp-chartarch`, sympy-verified exact; `chart-architecture-fork.md`,
`gate3-codex/verify_B_decomp.py`):

  `gWrap = sigmaPiv ∘ shearH ∘ permP ∘ bbA0 ∘ bbA1`

| atom | what | `|jacDet|` |
|---|---|---|
| `bbA1` | `blockBlowupMap {1,5,6,7} 1` (α-blow-up, inner) | `u1³` |
| `bbA0` | `blockBlowupMap {0..7} 0` (E-blow-up) | `u0⁷` |
| `permP` | coord permutation `[8,9,10,11,1,5,6,7,0,2,3,4]` on slots 0–11 | `1` (det −1) |
| `shearH` | the unipotent recoord-cancelling shear (reads slots 0–3,12–19) | `1` |
| `sigmaPiv` | `blockBlowupMap {0..7,20} 20` (c₁₁-blow-up) | `u20⁸` |

This is the `GeoStep = shear ∘ blockBlowupMap` form the general-`d` `GeneralGeoAtlas` builds, so the
folded `gFaithful` is the (3,3,4) instance of the decomposed spine. The folded crux
(`crux_radial_monomialise` / `hideal_coreGen_*`) transfers to this presentation VERBATIM — the map is
the same (`gFaithful_decomp`), no monomialisation re-proof. The Jacobian `|jacDet gWrap| = u0⁷·u1³·u20⁸`
then follows by `jacDet_comp` over the banked per-atom Jacobians (rung 5b, next section).

**The load-bearing caveat (pnp-chartarch):** the permutation `permP` is EXPLICIT (det −1, 45 inversions);
omitting it or reversing the composition order breaks both the extensional identity and the det sign. The
shear `shearH` is genuinely LOAD-BEARING (its `−u₈u₁₂−u₉u₁₆…` terms cancel `peeled`'s `Q₂⁻¹` recoord so the
blow-up extracts the exceptional monomial — `peeled∘(blow-up only)` factors 0 of 12 entries).
-/

open Matrix Set
open DLNFibre.Core.Aoyagi (blockBlowupMap)
open DLNFibre.Core.Aoyagi.Corank2FaithfulComposite (gFaithful)
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap (dvec sigmaPiv gWrap)

namespace DLNFibre.DLN.Aoyagi.Corank2GWrapDecomp

/-- `bbA1` — the inner α-blow-up `blockBlowupMap {1,5,6,7} 1` (`|jacDet| = u1³`). -/
noncomputable def bbA1 : (Fin 21 → ℝ) → (Fin 21 → ℝ) :=
  blockBlowupMap ({1, 5, 6, 7} : Finset (Fin 21)) 1

/-- `bbA0` — the E-blow-up `blockBlowupMap {0..7} 0` (`|jacDet| = u0⁷`). -/
noncomputable def bbA0 : (Fin 21 → ℝ) → (Fin 21 → ℝ) :=
  blockBlowupMap ({0, 1, 2, 3, 4, 5, 6, 7} : Finset (Fin 21)) 0

/-- The permutation of slots 0–11 (`[8,9,10,11,1,5,6,7,0,2,3,4]`), fixing 12–20. -/
def permIdx (k : Fin 21) : Fin 21 :=
  if k = 0 then 8 else if k = 1 then 9 else if k = 2 then 10 else if k = 3 then 11
  else if k = 4 then 1 else if k = 5 then 5 else if k = 6 then 6 else if k = 7 then 7
  else if k = 8 then 0 else if k = 9 then 2 else if k = 10 then 3 else if k = 11 then 4 else k

/-- `permP` — the coordinate permutation chart map (reindex by `permIdx`). -/
def permP : (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun w k => w (permIdx k)

/-- `shearH` — the unipotent recoord-cancelling shear (reads slots 0–3,12–19; adds the bilinear terms
to slots 4–11 that cancel `peeled`'s `Q₂⁻¹`/Schur recoord). Its Jacobian is unit-triangular (`|det| = 1`)
since the modified slots 4–11 never appear in the added terms. -/
def shearH : (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun w k =>
  if k = 4 then w 4 + w 0 * w 2 else if k = 5 then w 5 + w 1 * w 2
  else if k = 6 then w 6 + w 0 * w 3 else if k = 7 then w 7 + w 1 * w 3
  else if k = 8 then w 8 - w 0 * w 12 - w 1 * w 16 else if k = 9 then w 9 - w 0 * w 13 - w 1 * w 17
  else if k = 10 then w 10 - w 0 * w 14 - w 1 * w 18 else if k = 11 then w 11 - w 0 * w 15 - w 1 * w 19
  else w k

set_option maxHeartbeats 2000000 in
/-- **The extensional identity** `gFaithful = shearH ∘ permP ∘ bbA0 ∘ bbA1` (funext + `fin_cases` on the
21 degree-≤4 coordinate polynomials; sympy-verified 21/21). The folded (3,3,4) chart IS the decomposed
banked-atom composite — so the folded crux/`hideal` transfer to this presentation verbatim. -/
theorem gFaithful_decomp : gFaithful = shearH ∘ permP ∘ bbA0 ∘ bbA1 := by
  funext u k
  fin_cases k <;>
    simp only [Function.comp_apply, gFaithful, shearH, permP, permIdx, bbA0, bbA1, blockBlowupMap,
      Finset.mem_insert, Finset.mem_singleton, Fin.isValue] <;>
    norm_num [Fin.ext_iff] <;> ring

/-- **The decomposed chart** `gWrap = sigmaPiv ∘ shearH ∘ permP ∘ bbA0 ∘ bbA1` (from `gFaithful_decomp`
and `gWrap = sigmaPiv ∘ gFaithful`). The banked two-sided `hideal_coreGen_*` holds for this presentation
verbatim (same map); this decomposed form is what the rung-5b Jacobian (`jacDet_comp` over the atoms) and
the general-`d` `GeoStep` templating consume. -/
theorem gWrap_decomp : gWrap = sigmaPiv ∘ shearH ∘ permP ∘ bbA0 ∘ bbA1 := by
  show sigmaPiv ∘ gFaithful = sigmaPiv ∘ shearH ∘ permP ∘ bbA0 ∘ bbA1
  rw [gFaithful_decomp]

end DLNFibre.DLN.Aoyagi.Corank2GWrapDecomp
