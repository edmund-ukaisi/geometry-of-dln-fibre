<task>
I am formalising in Lean 4 + Mathlib (v4.29 pin) an "affine-domain equidimensionality"
dimension formula, network-free general commutative algebra. I need the cleanest proof route
and a sanity check on the ℕ∞/WithBot arithmetic, before I write Lean.

SETTING. k a field. R := MvPolynomial (Fin n) k (so dim R = n). I a PRIME ideal of R; set
A := R ⧸ I (a domain, finite-type over k). Let p be a prime ideal of A.

ALREADY PROVED (my Lean library, reusable, exact statements):
  (L5-poly)  height_add_ringKrullDim_quotient_eq :
       for any prime P of R = MvPolynomial (Fin n) k (k any field),
       (P.height : WithBot ℕ∞) + ringKrullDim (R ⧸ P) = (n : WithBot ℕ∞).
  (L5.1)     ringKrullDim_quotient_eq_coheight :
       for a prime point p of Spec R',  ringKrullDim (R' ⧸ p.asIdeal) = (coheight p : WithBot ℕ∞).
  (L5.4)     ringKrullDim_eq_of_integral_injective :
       integral + injective ring hom f : A' →+* S'  ⟹  ringKrullDim S' = ringKrullDim A'.
  (L5.5)     ringKrullDim_quotient_eq_noetherRank : Noether normalization of a quotient of R,
       giving ∃ s ≤ n with dim(R⧸P) = s and an injective integral k[y_1..y_s] →ₐ[k] R⧸P.
  Also available: exists_integral_inj_algHom_of_quotient (Noether normalization of R⧸P over k).
  Mathlib: IsLocalization.AtPrime.ringKrullDim_eq_height I A = I.height ;
           primeSpectrumQuotientOrderIsoIci (order iso PrimeSpectrum(R⧸p) ≃o Set.Ici p) ;
           Order.coheight, Order.height on PrimeSpectrum (a complete lattice / order).

GOAL (the headline I must deliver, zero sorry/axiom):
  affine_domain_height_add_quotient :
     for A = R⧸I domain (I prime), p prime of A :
       (Ideal.height p : WithBot ℕ∞) + ringKrullDim (A ⧸ p) = ringKrullDim A.
  Corollary (what downstream consumes): for m MAXIMAL in A,  Ideal.height m = ringKrullDim A,
  and ringKrullDim (Localization.AtPrime m) = ringKrullDim A.

TWO CANDIDATE ROUTES I am weighing:

ROUTE Q (quotient-chain / prime-correspondence).
  Primes p of A=R⧸I ↔ primes P ⊇ I of R (P = comap of mk; A⧸p ≅ R⧸P by third iso).
  Then coheight_A(p) = coheight_R(P) [via ring iso A⧸p ≅ R⧸P and L5.1], dim A = dim(R⧸I) = coheight_R(I).
  And height_A(p) = "height_R(P) − height_R(I)" (chains between I and P ↔ chains below p in A).
  Combine with the two L5-poly equalities height_R(P)+dim(R/P)=n, height_R(I)+dim(R/I)=n.
  Worry: the subtraction in ℕ∞. I want to keep it ADDITIVE and lossless.

ROUTE N (direct double Noether-normalize).
  Noether-normalize A itself (dim A = s, some s ≤ n) and A⧸p (dim = t). I do NOT see how this
  alone yields the HEIGHT relation height_A(p) = s − t without the chain/coheight identity, so I
  suspect Route N gives the dims but not the equidimensionality (height+coheight=dim) without
  re-deriving the catenary content. Confirm or refute.

KEY ADDITIVE REFRAMING I intend to use (please verify it is valid and lossless in WithBot ℕ∞ /
avoids any truncated subtraction). I want to prove, purely additively:
   height_A(p) + dim(A⧸p) = dim A.
   I have: dim(A⧸p) = coheight_A(p) = coheight_R(P)        [P the corresponding prime of R]
           dim A      = coheight_R(I).
   So GOAL ⟺  height_A(p) + coheight_R(P) = coheight_R(I).               (*)
   From L5-poly on P:  height_R(P) + coheight_R(P) = n.     (using dim(R/P)=coheight_R(P))
   From L5-poly on I:  height_R(I) + coheight_R(I) = n.
   Subtract: height_R(P) − height_R(I) = coheight_R(I) − coheight_R(P).
   And the chain identity Route Q gives: height_A(p) = height_R(P) − height_R(I).
   So (*) ⟺ height_A(p) = coheight_R(I) − coheight_R(P), still subtraction.

   QUESTION 1: What is the cleanest ADDITIVE formulation that needs NO ℕ∞ subtraction? In particular,
   is the right lemma to prove the *additive chain split*:
        height_R(P) = height_R(I) + height_A(p)                         (**)
   directly (a chain ⊥<...<I<...<P in Spec R splits at I into a chain below I of length height_R(I)
   and a chain I<...<P which corresponds to a chain below p in A of length height_A(p))? Then GOAL
   follows additively:  height_A(p) + coheight_R(P) = (height_R(P) − height_R(I)) + coheight_R(P),
   but I'd rather get GOAL from (**) + the two L5 equalities with NO subtraction at all. Show the
   exact additive chain of equalities that proves height_A(p) + dim(A⧸p) = dim A from:
        (**) height_R(P) = height_R(I) + height_A(p)
        (E_P) height_R(P) + coheight_R(P) = n
        (E_I) height_R(I) + coheight_R(I) = n
        dim A = coheight_R(I), dim(A⧸p)=coheight_R(P).
   Watch ℕ∞ is NOT cancellative under +? Actually ℕ∞ addition: is a+c=b+c ⟹ a=b valid for FINITE c
   in ℕ∞? All these heights/coheights are ≤ n hence finite (< ⊤). Confirm cancellation is available
   (e.g. via ENat / WithTop add-left-cancel for finite elements), since I'll need to cancel.

   QUESTION 2: For (**), the additive height split: is there Mathlib API for
   "height of P = height of (P/I in R/I) + height of I" when I ≤ P are primes? Candidates I should
   grep: Order.height on Set.Ici, the order-iso PrimeSpectrum(R⧸I) ≃o Set.Ici I (I have
   primeSpectrumQuotientOrderIsoIci), and any "height in an interval" / relative height lemma. If
   absent, what is the minimal hand-proof? The crux: height_A(p) = the length-sup of chains in
   [I, P] ⊆ Spec R. Is it cleaner to prove (**) via the order-iso transporting Order.height, or via
   a localization/AtPrime argument?

   QUESTION 3 (the catenary worry): does (**) ITSELF secretly need catenary-ness of R beyond what
   L5 gives? My instinct: NO — (**) for the *specific* split at I along a chain to P is just
   "height_A(p) = relative height of P over I", which is a tautology of how Order.height transports
   along the order-iso PrimeSpectrum(A) ≃o Set.Ici I (a closed-interval order embedding into
   Spec R). The CATENARY content (that this relative height plus coheight = n−height_R(I)) is what
   L5 already supplies for the whole ring. Confirm that the only genuinely new ingredient is the
   order-iso transport of height (no new catenary induction), OR identify precisely where catenary
   re-enters.

   QUESTION 4 (the maximal corollary): for m maximal in A=R⧸I domain, I want height m = dim A.
   From the GOAL: height m + dim(A⧸m) = dim A, and A⧸m is a field (m maximal) so dim(A⧸m)=0. Is
   "ringKrullDim (field) = 0" exactly ringKrullDim_eq_zero_of_field? And does dim(A⧸m)=0 require
   A⧸m to be a field — i.e. m maximal — which holds since A is a finite-type k-algebra and Jacobson,
   OR do I just take m maximal as a hypothesis (A⧸m field is then immediate)? I plan to take m
   maximal as hypothesis (no Nullstellensatz needed). Confirm dim(A⧸m)=0 ⟸ m maximal is immediate
   (A⧸m field). Then local↔global via IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization
   .AtPrime m) = m.height = dim A. Confirm the instance [IsLocalization.AtPrime (Localization.AtPrime m) m]
   fires by inferInstance.
</task>

<output_contract>
  Answer Q1–Q4 in order, each ≤ 8 lines. For Q1 give the EXACT additive equality chain (no prose
  padding) that derives the goal, and state the precise cancellation lemma needed and its hypothesis
  (finiteness). For Q2 name concrete Mathlib lemma candidates (best guesses at names) or say "likely
  absent, hand-prove via X". Be explicit about inference vs. known-fact: prefix any lemma name you
  are NOT sure exists with "GUESS:". End with a one-line route recommendation (Q vs N) and the single
  riskiest step.
</output_contract>

<grounding_rules>
  You may reason from standard commutative algebra (catenary-ness of affine domains, dimension
  theory) as established mathematics. For Lean/Mathlib lemma NAMES, mark each as GUESS: unless it is
  one of the exact names I listed as "already proved" / "Mathlib" above. Do not fabricate certainty
  about Mathlib API. Flag any step where the standard math is true but the Lean formalisation is
  likely to fight (e.g. ℕ∞ subtraction, order-iso height transport defeq).
</grounding_rules>
