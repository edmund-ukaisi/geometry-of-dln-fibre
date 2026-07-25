import DLNFibre.DLN.Aoyagi.Corank2UpperBound334
import DLNFibre.DLN.Aoyagi.LearningCoefficient
import DLNFibre.DLN.RLCT.Validate.MinAdmCCodim

/-!
# `DLN.Aoyagi.Corank2CiteFree334` — the (3,3,4) Watanabe upper bound, CITE-FREE

Wires the banked reductions to the built single-chart RLCT upper bound to replace
`cited_watanabe_upper_ax` at the `(3,3,4)`, `B = 0` instance, cite-free:

* **reduction (a)** `coreReduction` — `rlctGlobal (lossDLN dvec 0) = rlctAt (∑(coreGenᵢ)²) 0`
  (deepest-point + measure-preserving flatten). Needs `MeasurePreserving eWrap` (the SOLE un-banked
  input, carried as a hypothesis — the transpose flatten is a linear coordinate reindex).
* the built upper `rlctAt_coreGen334_le_four` — `rlctAt (∑(coreGenᵢ)²) 0 ≤ 4` (single-chart CoV
  from `chart334`, cite-free, `Corank2UpperBound334`).
* **reduction (b)** `codimRealFibre_334_zero_toNat` — `(codimRealFibre ![3,3,4] 0).toNat = 8`, from
  `minAdm ![3,3,4] = 8` (`decide`) via the banked `minAdm_eq_cCodim` + the base-change transfer.

Result: `rlctGlobal (lossDLN ![3,3,4] 0) ≤ ½·codimRealFibre ![3,3,4] 0 = 4`, WITHOUT
`cited_watanabe_upper_ax`. Single un-banked residual: `MeasurePreserving eWrap` (a linear coordinate
reindex — the eWrap↔canonFlatten transport, on the consume-build's plan).
-/

open MeasureTheory
open DLNFibre.Core DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi

open DLNFibre.DLN (codimRealFibre lossDLN)
open DLNFibre.DLN.RLCT (minAdm minAdm_eq_cCodim)

/-- **Reduction (b): `(codimRealFibre ![3,3,4] 0).toNat = 8`.** The real zero-product fibre's
codimension is the combinatorial `minAdm ![3,3,4] = 8` (`decide`), via the banked `minAdm_eq_cCodim`
and the base-change transfer `codimRealFibre = codimRepCanonical (ℂ) = cCodim`. Field-independent
`C = 8`. -/
theorem codimRealFibre_334_zero_toNat :
    (codimRealFibre dvec
      (0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ)).toNat = 8 := by
  have h : (kostantPartitions dvec 0).Nonempty :=
    kostantPartitions_nonempty_of_le (by norm_num) (fun _ => Nat.zero_le _)
  have hbridge : codimRealFibre dvec (0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ)
      = codimRepCanonical (k := ℂ)
          (fibre (k := ℂ) dvec (((0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ)).map
            (Complex.ofRealHom))) :=
    DLNFibre.DLN.codimRealFibre_eq_codimRepCanonical_baseChange (K := ℂ) (ι := Complex.ofRealHom)
      (by norm_num) 0 Matrix.rank_zero h
  have hmap : ((0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ).map (Complex.ofRealHom))
      = (0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℂ) :=
    Matrix.map_zero _ (map_zero _)
  rw [hbridge, hmap]
  have hcc := codimRepCanonical_fibre_zero_eq_cCodim (k := ℂ) dvec h
  have hminadm : (minAdm dvec : ℤ) = cCodim dvec 0 h := minAdm_eq_cCodim dvec (by norm_num) h
  have hm8 : minAdm dvec = 8 := by decide
  omega

/-- **The (3,3,4) Watanabe upper bound, CITE-FREE (modulo the flatten's measure-preservation).**
`rlctGlobal (lossDLN ![3,3,4] 0) ≤ ½·codimRealFibre ![3,3,4] 0` — the `(3,3,4)`, `B = 0` instance of
`cited_watanabe_upper_ax`, PROVED (no cite): reduction (a) `coreReduction` localises the global RLCT
to `rlctAt (∑(coreGen dvec eWrap)ᵢ²) 0`, the built `rlctAt_coreGen334_le_four` caps it at `4`, and
reduction (b) evaluates the RHS to `8/2 = 4`. The sole un-banked input is `MeasurePreserving eWrap`
(the transpose flatten is a linear coordinate reindex; carried as a hypothesis here). -/
theorem rlctGlobal_lossDLN_334_zero_le_half_codimRealFibre (hmp : MeasurePreserving eWrap) :
    RLCT.Global.rlctGlobal
        (lossDLN dvec (0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ))
      ≤ ((codimRealFibre dvec
          (0 : Matrix (Fin (dvec (Fin.last 2))) (Fin (dvec 0)) ℝ)).toNat : ℝ) / 2 := by
  have hred := coreReduction dvec (by norm_num : (0 : ℕ) < 2) eWrap hmp eWrap_zero
  rw [codimRealFibre_334_zero_toNat, hred]
  have hle := rlctAt_coreGen334_le_four
  have h8 : ((8 : ℕ) : ℝ) / 2 = 4 := by norm_num
  rw [h8]
  exact hle

end DLNFibre.DLN.Aoyagi
