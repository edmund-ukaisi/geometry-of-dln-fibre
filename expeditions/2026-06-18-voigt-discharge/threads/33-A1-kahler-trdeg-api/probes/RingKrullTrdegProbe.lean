import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Basic
import DLNFibre.Core.PolynomialDimension

/-!
Scratch: can `ringKrullDim(f.g. domain) = trdeg k A` be assembled from the LANDED Noether engine
(`ringKrullDim_quotient_eq_noetherRank` gives an integral injective `k[y_1..y_s] →ₐ A` with dim = s)
plus the trdeg API? Pin the connecting lemmas.
-/

open Algebra

section
variable (k : Type*) [Field k] {n : ℕ}

-- The bridge we want: an integral algebraic extension preserves trdeg.
-- candidate: trdeg of A over k, when A is algebraic over a polynomial subring k[y_1..y_s].
-- `MvPolynomial.trdeg_of_isDomain` gives trdeg_k k[y_1..y_s] = s.
#check @MvPolynomial.trdeg_of_isDomain
-- For an integral (hence algebraic) injective B →ₐ A with B = k[fin s], is trdeg_k A = s?
-- Need: trdeg additivity across B → A with A algebraic over B (so trdeg_B A = 0).
-- `trdeg_add_eq`: trdeg R S + trdeg S A = trdeg R A  (R=k, S=B image, A).
#check @trdeg_add_eq
-- algebraic ⟹ trdeg = 0:
#check @trdeg_eq_zero          -- [Algebra.IsAlgebraic R A] : trdeg R A = 0
#check @trdeg_eq_zero_iff
-- the ABSENT direction we'd still need: trdeg (as a Cardinal/Nat) = ringKrullDim (as WithBot ℕ∞).
-- there is NO lemma equating these two; the bridge is the *content*.
end
