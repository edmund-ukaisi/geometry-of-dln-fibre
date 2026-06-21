<task>
I am formalising in Lean 4 + Mathlib (v4.29 pin) the Nullstellensatz bridge that lets a *geometric*
codimension of an affine variety be read off from its Krull dimension, for the DLN-fibre paper.

SETTING. Field `k`, `[IsAlgClosed k]`, `[Fintype σ]`. Affine space is `σ → k`. Mathlib's
`MvPolynomial.zeroLocus K I : Set (σ → K)` and `MvPolynomial.vanishingIdeal k V : Ideal (MvPolynomial σ k)`
(I use `K := k`). The Nullstellensatz I have:
  - `vanishingIdeal_zeroLocus_eq_radical (K:=k) I : vanishingIdeal k (zeroLocus k I) = I.radical`
  - `IsPrime.vanishingIdeal_zeroLocus (K:=k) P : vanishingIdeal k (zeroLocus k P) = P`  (P prime)
  - GaloisConnection `zeroLocus_vanishingIdeal_galoisConnection` (l = zeroLocus, u = vanishingIdeal, on Setᵒᵈ).
There is NO Zariski topology instance on `σ → k` in Mathlib — only on `PrimeSpectrum R`. There IS
`PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime` for subsets of `PrimeSpectrum R`.

ALREADY PROVED (a separate module, network-free): for `R = MvPolynomial (Fin n) k`, any field, prime `p`:
  `height_add_ringKrullDim_quotient_eq : (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = n`.
Plus transport lemmas across a k-algebra equiv: `height_map_algEquiv`, `ringKrullDim_quotient_map_algEquiv`.
And `MvPolynomial.ringKrullDim_of_isNoetherianRing` gives `ringKrullDim (MvPolynomial σ k) = Nat.card σ`
(field ⟹ ringKrullDim 0).

GOAL. A "bridge" lemma the geometry layer consumes. The consumer is `codimRep coord Z :=
Ideal.height (vanishingIdeal (coord '' Z))` and `codimRepCanonical Z := codimRep (canonicalCoord d) Z`,
where `coord '' Z ⊆ (RepCoord d → k)` and `RepCoord d` is a `Fintype`. They want, for an irreducible
Zariski-closed `Z`: `codimRep (canonicalCoord d) Z = #(RepCoord d) − dim Z`, where `dim Z` is the Krull
dimension of the coordinate ring `MvPolynomial σ k ⧸ vanishingIdeal Z` (the standard variety dimension).

The transport from `Fin n` to `Fintype σ` is via `Fintype.equivFin` + `MvPolynomial.renameEquiv`, mapping
the prime, applying the `Fin n` headline, transporting height/quotient-dim back. I have pinned all the API
(it type-checks). The headline over σ will read:
  `(vanishingIdeal Z).height + ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal Z) = Nat.card σ`
for `(vanishingIdeal Z).IsPrime`.

DESIGN QUESTION. How should I phrase "irreducible Zariski-closed Z" so the bridge is (a) faithful to the
informal claim, (b) maximally usable by the geometry layer, (c) self-contained at this pin without inventing
a topology instance Mathlib lacks? Two candidate framings:
  (A) Make the hypothesis purely algebraic: `[(vanishingIdeal k Z).IsPrime]` (this IS the algebraic content
      of "irreducible variety"), plus a separate `IsZariskiClosed Z := Z = zeroLocus k (vanishingIdeal k Z)`
      predicate. Provide a dictionary lemma connecting `.IsPrime` to a topological/irreducibility notion if
      cheap, else omit it. State `dim Z := ringKrullDim (R ⧸ vanishingIdeal Z)` as a def.
  (B) Build a Zariski topology on `σ → k` (e.g. pulled back via `pointToPoint : (σ→k) → PrimeSpectrum R`,
      or as `TopologicalSpace.induced`) and phrase `IsClosed`/`IsIrreducible Z` topologically, then connect
      to `.IsPrime` via the existing `PrimeSpectrum` dictionary.

Note `pointToPoint x = ⟨vanishingIdeal k {x}, _⟩` and `vanishingIdeal_pointToPoint :
PrimeSpectrum.vanishingIdeal (pointToPoint '' V) = MvPolynomial.vanishingIdeal k V`. This might give a cheap
bridge from the σ→k irreducibility to PrimeSpectrum irreducibility.
</task>

<output_contract>
1. Recommend (A) or (B) or a hybrid, in 3-5 sentences, judged on faithfulness + usability + cost at v4.29.
2. If a topological irreducibility dictionary is cheaply reachable via `pointToPoint` and
   `vanishingIdeal_pointToPoint` + `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime`, sketch the 3-5
   step proof outline (lemma names only, no full Lean). If it is NOT cheap, say so plainly and say to omit it.
3. Name any soundness trap in equating `ringKrullDim (R ⧸ vanishingIdeal Z)` with "the variety dimension of Z":
   in particular, does this require Z nonempty? closed? reduced? Flag the minimal hypotheses for the equation
   `height (vanishingIdeal Z) = Nat.card σ − dim Z` to be a faithful statement of "codim = ambient − dim".
4. Flag whether `Nat.card σ − dim Z` should be stated as a subtraction (ℕ∞ truncated subtraction is lossy) or
   as the additive identity `height + dim = card` (cleaner). Recommend the headline's exact algebraic form.
</output_contract>

<grounding_rules>
You are reasoning about Mathlib v4.29 API and standard commutative algebra. Distinguish: (i) facts you are
confident hold in Mathlib v4.29, (ii) standard math facts, (iii) inferences/guesses about exact lemma names
you are unsure exist. Mark (iii) explicitly — I will verify every name locally. Do not invent lemma names
with false confidence.
</grounding_rules>
