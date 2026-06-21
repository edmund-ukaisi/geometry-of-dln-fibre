# Sizing two commutative-algebra bridges in Lean 4 + Mathlib (pin v4.29.0)

I am de-risking a kill-condition. I need an HONEST size for each of two targets: is it a
SINGLE MODULE (a handful of lemmas on existing Mathlib bricks), or a genuine SUB-LIBRARY
(a multi-week effort building absent foundational theory)? Do not be optimistic; if it needs
absent theory, say so and name the missing theory precisely.

Context: I have already PROVED, as `Core` lemmas at this pin:
- `height_add_ringKrullDim_quotient_eq`: for a prime `p` of `R = MvPolynomial (Fin n) k` (k a field),
  `(p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = n`. (Affine-SPACE equidimensionality only — for the
  polynomial ring R itself, NOT for an arbitrary affine domain R/I.)
- `ringKrullDim_eq_of_integral_injective`: ringKrullDim invariance under an injective integral ring hom.
- `ringKrullDim_quotient_eq_coheight`, `ringKrullDim_mvPolynomial_fin_field` (= n).

Mathlib bricks confirmed PRESENT at this pin:
- `IsLocalization.AtPrime.ringKrullDim_eq_height (I) (A) : ringKrullDim A = I.height` (A = localization at prime I).
- `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`, `Ideal.exists_isMaximal_height` (a max ideal of dim = dim R exists).
- `IsRegularLocalRing` (class: `(maximalIdeal R).spanFinrank = ringKrullDim R`) and
  `IsRegularLocalRing.iff_finrank_cotangentSpace` (iff `finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R`,
  where CotangentSpace = m/m² ⊗ residue field). **`IsRegularLocalRing` appears NOWHERE in Mathlib except its own Defs.lean** —
  no theorem produces it, none consumes it beyond the iff.
- Smooth-locus theory: `Algebra.smoothLocus R A = {p | FormallySmooth R (Localization.AtPrime p)}`, `isOpen_smoothLocus`,
  `smoothLocus_eq_univ_iff` (FinitePresentation). `Algebra.FormallySmooth.of_perfectField` (field extensions).
  Jacobian/standard-smooth cotangent: `SubmersivePresentation.rank_kaehlerDifferential` (rank of Ω = relative dimension),
  `Module.Free`/projective `Ω[A/R]` for smooth. `H1Cotangent`, `Ω[A/R]` theory is rich.
- CONFIRMED ABSENT: `rg ringKrullDim` over all of RingTheory/Kaehler, RingTheory/Smooth, RingTheory/Etale returns NOTHING.
  There is ZERO link between the Kähler-differential / smoothness theory and ringKrullDim anywhere in Mathlib.

## TARGET L4(a) — smooth ⟹ regular local ring.
For a finite-type k-algebra A (k a field, may add IsAlgClosed/perfect), m a maximal ideal at which A is smooth
(FormallySmooth k (Localization.AtPrime m), i.e. m ∈ smoothLocus), prove `IsRegularLocalRing (Localization.AtPrime m)`.
Standard math: at a smooth point the local ring is regular — its m/m² has dimension = Krull dim. The classical proof:
(i) smooth ⟹ Ω[A/k] locally free of rank = dim near m; (ii) the conormal/cotangent sequence + smoothness gives
finrank_k(m/m²) = rank Ω = dim; (iii) so cotangent dim = Krull dim = regular. The bridge "rank Ω = ringKrullDim" is the
crux and is ABSENT.

## TARGET L4(d) — local↔global dim at a closed point.
For a finite-type DOMAIN A over k and a maximal ideal m, `ringKrullDim (Localization.AtPrime m) = ringKrullDim A`.
Via `AtPrime.ringKrullDim_eq_height` this reduces to `m.height = ringKrullDim A` for EVERY maximal m of an affine domain
(i.e. affine domains are equidimensional / all closed points have full height). I have the polynomial-RING formula
(height + coheight = n) but NOT for A = R/I. The question: how hard is lifting equidimensionality from k[x] to an arbitrary
affine domain R/I? Does it need: Noether normalization + going-up/going-down per maximal ideal + the dimension formula
`dim A = trdeg`? Is `m.height = dim A` for maximal m even TRUE without normality, and what is the minimal Mathlib-buildable route?

## What I need from you
For EACH target, decorrelated from my own estimate:
1. Module or sub-library? If sub-library, what is the absent foundational theory, in Mathlib terms?
2. The minimal correct proof route at this pin, naming the load-bearing lemmas (present or to-build).
3. For L4(d): is there a route avoiding the R/I lift entirely (e.g. via integral extension + my ringKrullDim_eq_of_integral_injective + a height-transport)? Is the per-maximal-ideal equidimensionality the real obstruction?
4. Any trap that makes the "obvious" route unsound at a non-normal / non-equidimensional ring.
