import DLNFibre.DLN.Aoyagi.BlowupArithmetic
import DLNFibre.DLN.Aoyagi.Lemma5SuppliedFamily

/-!
# Supplied terminal-candidate bridge for Aoyagi's Lemma 5

This file connects the supplied Lemma 5 branch family to the existing
terminal-exponent certificate API.  The bridge is deliberately conditional:
the identification of a source terminal-exponent numerator with the Lemma 3
free-count expression is supplied as a hypothesis.  No displayed branch
construction, chart coverage, pole-order count, normal-crossing theorem, or
RLCT extraction is proved here.
-/

open scoped BigOperators

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- The free high-count parameter used in Aoyagi Lemma 3.

For total increment length `n+1`, this counts only the first `n` Lemma 4
increments and excludes the final increment `Fin.last n`. -/
def aoyagiLemma4FreeHighCount (n : ℕ) (M : ℤ)
    (m H : Fin (n + 2) → ℤ) : ℕ :=
  (Finset.univ.filter fun j : Fin n ↦
    aoyagiLemma4F (n + 1) m H j.castSucc = M).card

/-- Every tagged branch in a supplied full Lemma 5 family attains the isolated
Lemma 3 numerator minimum, stated with the named free high-count parameter. -/
theorem AoyagiLemma5SuppliedAdmissibleFamily.fullBranch_freeHighCountMin
    {β : Type*} [DecidableEq β] {n a : ℕ} {M : ℤ}
    {m : Fin (n + 2) → ℤ}
    (F : AoyagiLemma5SuppliedAdmissibleFamily β (n + 1) a M m)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    {x : Option β} (hx : x ∈ F.fullBranches) :
    aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
        (aoyagiLemma4FreeHighCount n M m (F.fullH x) : ℤ) =
      (a : ℤ) * ((n + 1 : ℕ) : ℤ) *
        (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  simpa [aoyagiLemma4FreeHighCount] using
    F.fullBranch_freeHighCount_lemma3A_eq_min ha hselected hx

/-- Supplied terminal-exponent numerator bridge for a tagged Lemma 5 branch.

If an introduced-label exponent certificate has a numerator supplied to be the
Lemma 3 free-count expression of a tagged supplied Lemma 5 branch, then its
terminal exponent is the isolated Lemma 3 minimum numerator.

The hypothesis `hnumer` is the missing terminal-exponent normalisation.  This
theorem does not construct the source label, prove terminal `\tilde t=0`,
identify the numerator with `lambda`, prove pole order, or perform RLCT
extraction. -/
theorem IntroducedLabelExponentCertificates.terminalExponent_eq_suppliedLemma5MinNumerator
    {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J s k : ℕ}
    {t : ℕ → ℕ → ℕ → ℤ}
    {numerator leastValue : ℕ → ℕ → ℤ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    (certs : IntroducedLabelExponentCertificates L width S J t numerator leastValue)
    (F : AoyagiLemma5SuppliedAdmissibleFamily β (n + 1) a M m)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    {x : Option β} (hx : x ∈ F.fullBranches)
    (hintro : introducedLabel L width S J s k)
    (hnumer :
      numerator s k =
        aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
          (aoyagiLemma4FreeHighCount n M m (F.fullH x) : ℤ)) :
    terminalExponent L (widthZ width) (t s k) =
      (a : ℤ) * ((n + 1 : ℕ) : ℤ) *
        (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  have hc := certs.certificate hintro
  calc
    terminalExponent L (widthZ width) (t s k) = numerator s k :=
      hc.terminalExponent_eq
    _ =
        aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
          (aoyagiLemma4FreeHighCount n M m (F.fullH x) : ℤ) := hnumer
    _ = (a : ℤ) * ((n + 1 : ℕ) : ℤ) *
        (((n + 1 : ℕ) : ℤ) - (a : ℤ)) :=
      F.fullBranch_freeHighCountMin ha hselected hx

end Aoyagi
end DLN
end DLNFibre
