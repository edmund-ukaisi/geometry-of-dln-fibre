<task>
Algebraic-geometry / commutative-algebra design question (Lean 4 + Mathlib formalization, but
answer at the math level — no Lean code). I need to discharge a "localization no-drop" obligation
and decide which of two coordinate rings to state it over.

SETUP (exact). Over an algebraically closed field k of characteristic 0, in the affine space
Rep_d = (a fixed finite-dimensional vector space of "composable matrix tuples" A = (A_1,...,A_N),
A_i a matrix), there is a regular "multiplication" map mult(A) = A_N···A_1, a matrix. Fix r. Define:

  - Σ^r  := { A : rank(mult A) = r }        (rank-EXACTLY-r locus; NOT closed in general)
  - Σ̄^r := { A : rank(mult A) ≤ r }         (rank-≤r locus; this IS Zariski-closed —
                                              cut out by vanishing of all (r+1)×(r+1) minors of mult)
  - I_eq  := vanishingIdeal(Σ^r)   ⊆ k[Rep_d]     ;   O_eq  := k[Rep_d]/I_eq
  - I_le  := vanishingIdeal(Σ̄^r)  ⊆ k[Rep_d]     ;   O_le  := k[Rep_d]/I_le
  - δ      : a known nonnegative integer (a "fibre-dimension shift").
  - detΔ ∈ k[Rep_d]: a specific polynomial = the top-left r×r minor of the PRODUCT matrix mult(A).

ESTABLISHED FACTS (all proved/landed in the formalization):
  (F0) Σ^r ⊆ Σ̄^r, hence I_le ⊆ I_eq, hence the closed set Σ̄^r = Zariski closure of Σ^r as SETS
       is NOT yet proved — the set-closure identity "closure(Σ^r) = Σ̄^r" would require an unbuilt
       "rank-raising / density" theorem and is deliberately NOT assumed.
  (F1) DIMENSION equality: ringKrullDim O_eq = ringKrullDim O_le. (Proved via a codimension
       sandwich that does NOT prove the ideal equality I_eq = I_le; it only shows the two rings
       have equal Krull dimension. The variety-dim of a set Z is defined as
       ringKrullDim(k[Rep_d]/vanishingIdeal Z), so this is exactly varietyDim(Σ^r)=varietyDim(Σ̄^r).)
  (F2 = "Fact A") Every TOP-DIMENSIONAL minimal prime p of I_le (i.e. a minimal prime with
       ringKrullDim(O_le/p) = ringKrullDim O_le) is the vanishing ideal of a single irreducible
       "orbit closure" component whose generic product-rank is EXACTLY r (corner = r).
  (F3 = "Fact B") For each such top component / minimal prime p of I_le, detΔ ∉ p
       (detΔ does not vanish identically on that component) — because the component is stable under
       a GL×GL endpoint group action and a permutation in that group moves some nonzero r×r minor
       of the rank-r product to the top-left slot.
  (F4) A LANDED lemma: "no-drop from a top prime avoiding g": for a finite-type Noetherian
       k-algebra R, if p₀ is a prime of R with ringKrullDim(R/p₀) = ringKrullDim R and g ∉ p₀,
       then ringKrullDim(Localization.Away g R) = ringKrullDim R. (NOTE: p₀ need only be a PRIME
       carrying the full dimension — MINIMALITY is NOT required.)
  (F5) The free general identity vanishingIdeal(Zariski-closure S) = vanishingIdeal(S) is available.

THE OBLIGATION ("hsig"): I must prove
      ringKrullDim(Localization.Away (image of detΔ in O_eq)) = ringKrullDim O_eq.
A downstream wrapper that produces the final dimension count currently consumes this over O_eq
(the =r ring). I could instead restate the wrapper (cheap to restate) over O_le (the ≤r ring) and
prove the analogous no-drop there:
      ringKrullDim(Localization.Away (image of detΔ in O_le)) = ringKrullDim O_le.

CONSTRAINTS: I must NOT use the unbuilt set-closure / rank-raising / density theorem
(F0's missing identity), and I must NOT assume I_eq = I_le.

WHAT I ALREADY TRIED / am weighing:
  Route A: get a top-dim prime p₀ of O_eq directly (so F4 applies over O_eq with g = detΔ),
           somehow transporting Facts A/B (which are stated over I_le / O_le).
  Route B: apply F4 over O_le (where Facts A/B are clean: a top minimal prime of I_le avoids detΔ),
           getting the no-drop over O_le, then restate the wrapper over O_le and transport to the
           final count using the F1 dimension equality only at the end.
</task>

<output_contract>
  1. RING VERDICT: which ring should the localized-chart equivalence + the no-drop be stated over,
     O_eq (=r) or O_le (≤r)? One line, then the single decisive reason.
  2. Can the no-drop "hsig" be discharged over O_eq WITHOUT the set-closure/density theorem and
     WITHOUT assuming I_eq = I_le? Specifically: does a top-dimensional prime p₀ of I_eq with
     detΔ ∉ p₀ exist and is it constructible from the landed facts (F1–F5)? If a minimal prime of
     I_le is also a prime of O_eq carrying the full dimension, say exactly how (or why it fails).
     Be explicit about the relationship between Spec(O_eq) and Spec(O_le) given only I_le ⊆ I_eq.
  3. Give the exact lemma chain to discharge the obligation over whichever ring you chose, each step
     tagged [LANDED]/[cheap]/[must-build], with NO step being the density theorem.
  4. State whether the downstream wrapper must be restated over the other ring, and if so, flag it.
  5. The single most likely thing that breaks your chosen route.
</output_contract>

<grounding_rules>
  - Treat F0–F5 as given facts; do not re-derive them. Do not propose using the density theorem.
  - Distinguish clearly between what is a FACT (given) and what is your INFERENCE.
  - Keep it tight; this is a design adjudication, not an exposition.
  - Note carefully: I_le ⊆ I_eq, so Spec(O_eq) ⊆ Spec(O_le) as a closed subscheme inclusion; a
    prime of O_le need NOT come from a prime of O_eq, and vice versa. Reason about which primes
    transport in which direction.
</grounding_rules>
