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

/-- Supplied terminal-candidate data over a full Lemma 5 branch family.

The fields attach each tagged supplied branch to a source label in the generic
introduced-label exponent-certificate API, supply terminality as least value
zero, and supply the missing numerator normalisation to the Lemma 3 free-count
expression.  This is still a supplied boundary: it does not construct these
labels from Aoyagi's printed equations and does not assert there are no other
terminal minimizers. -/
structure AoyagiLemma5SuppliedTerminalCandidateFamily (β : Type*) [DecidableEq β]
    (L : ℕ) (width : ℕ → ℕ) (S J : ℕ)
    (n a : ℕ) (M : ℤ) (m : Fin (n + 2) → ℤ)
    (t : ℕ → ℕ → ℕ → ℤ)
    (numerator leastValue : ℕ → ℕ → ℤ) where
  family : AoyagiLemma5SuppliedAdmissibleFamily β (n + 1) a M m
  certs : IntroducedLabelExponentCertificates L width S J t numerator leastValue
  branchS : Option β → ℕ
  branchK : Option β → ℕ
  introduced :
    ∀ {x : Option β}, x ∈ family.fullBranches →
      introducedLabel L width S J (branchS x) (branchK x)
  terminal_leastValue_zero :
    ∀ {x : Option β}, x ∈ family.fullBranches →
      leastValue (branchS x) (branchK x) = 0
  numerator_eq_lemma3A :
    ∀ {x : Option β}, x ∈ family.fullBranches →
      numerator (branchS x) (branchK x) =
        aoyagiLemma3A ((n + 1 : ℕ) : ℤ) (a : ℤ)
          (aoyagiLemma4FreeHighCount n M m (family.fullH x) : ℤ)

namespace AoyagiLemma5SuppliedTerminalCandidateFamily

/-- The tagged branch set of a supplied terminal-candidate family. -/
def fullBranches {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue) :
    Finset (Option β) :=
  C.family.fullBranches

/-- The supplied terminal-candidate branch set has Aoyagi's Lemma 5 supplied
finite count. -/
theorem fullBranches_card {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    (n a : ℕ) (M : ℤ) (m : Fin (n + 2) → ℤ)
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (hell : 1 ≤ n + 1) (ha : a ≤ n + 1) :
    C.fullBranches.card = a * (n + 1 - a) + 1 := by
  exact AoyagiLemma5SuppliedAdmissibleFamily.fullBranches_card
    (n + 1) a M m C.family hell ha

/-- Every tagged supplied terminal candidate has terminal least value zero. -/
theorem branch_terminalLeastValue_zero {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    {x : Option β} (hx : x ∈ C.fullBranches) :
    leastValue (C.branchS x) (C.branchK x) = 0 :=
  C.terminal_leastValue_zero hx

/-- Every tagged supplied terminal candidate has terminal exponent equal to
the isolated Lemma 3 minimum numerator.

The source-label realisation, terminal least-value zero, and numerator
normalisation are supplied fields of the structure. -/
theorem branch_terminalExponent_eq_minNumerator {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    {x : Option β} (hx : x ∈ C.fullBranches) :
    terminalExponent L (widthZ width) (t (C.branchS x) (C.branchK x)) =
      (a : ℤ) * ((n + 1 : ℕ) : ℤ) *
        (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  exact C.certs.terminalExponent_eq_suppliedLemma5MinNumerator
    C.family ha hselected hx (C.introduced hx) (C.numerator_eq_lemma3A hx)

/-- Branchwise supplied terminal-candidate package: introduced label,
terminal least value zero, and terminal-exponent minimum numerator. -/
theorem branch_terminalCandidateData {β : Type*} [DecidableEq β]
    {L : ℕ} {width : ℕ → ℕ} {S J : ℕ}
    {n a : ℕ} {M : ℤ} {m : Fin (n + 2) → ℤ}
    {t : ℕ → ℕ → ℕ → ℤ} {numerator leastValue : ℕ → ℕ → ℤ}
    (C : AoyagiLemma5SuppliedTerminalCandidateFamily β L width S J n a M m
      t numerator leastValue)
    (ha : a ≤ n + 1)
    (hselected :
      (∑ j : Fin (n + 2), m j) = ((n + 1 : ℕ) : ℤ) * (M - 1) + a)
    {x : Option β} (hx : x ∈ C.fullBranches) :
    introducedLabel L width S J (C.branchS x) (C.branchK x) ∧
      leastValue (C.branchS x) (C.branchK x) = 0 ∧
        terminalExponent L (widthZ width) (t (C.branchS x) (C.branchK x)) =
          (a : ℤ) * ((n + 1 : ℕ) : ℤ) *
            (((n + 1 : ℕ) : ℤ) - (a : ℤ)) := by
  exact ⟨C.introduced hx, C.branch_terminalLeastValue_zero hx,
    C.branch_terminalExponent_eq_minNumerator ha hselected hx⟩

end AoyagiLemma5SuppliedTerminalCandidateFamily

end Aoyagi
end DLN
end DLNFibre
