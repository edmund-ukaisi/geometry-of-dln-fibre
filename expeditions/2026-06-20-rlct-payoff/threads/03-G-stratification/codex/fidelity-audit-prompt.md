You are a decorrelated second-opinion mathematician reviewing a Lean 4 formalisation for FIDELITY to a paper.

PAPER: Lehalleur–Rimányi 2024, "Geometry of the fibers of the multiplication map of deep linear neural networks", §4.

PAPER OBJECTS (verbatim from §4 source):
- mult : Rep_d → Mat_{d_N, d_0}, (A_1,...,A_N) ↦ A_N · A_{N-1} ... A_1.
- Σ^r_d := { A | rk(mult A) = r }.
- The source DEFINING display writes the overline locus as cSigma^r_d := { A | rk(mult A) ≥ r }, BUT the paper's digest footnote flags this as a transcription error: the component/codimension statements (Cor 4.4) use the CLOSURE convention Σ̄^r = { A | rk(mult A) ≤ r }, which is the genuine Zariski closure of Σ^r (rank is lower-semicontinuous, so the closure of {rk=r} adds limit points of rank ≤ r).
- Stratification (paper §4): Σ̄^r_d = ⋃_{m : m_{0N} ≤ r} Ō_M, where Ō_M is the orbit closure of the orbit with rank pattern m, m_{0N} is the CORNER rank-pattern entry (the (0,N) entry = rank of the full product), and the union is over rank patterns / Kostant partitions with corner ≤ r.
- Orbit closure (Thm 3.8, Abeasis–Del Fra): O_{rk=s} ⊆ Ō_{rk=r} ⟺ s ≤ r entrywise (∀ i ≤ j, s_{ij} ≤ r_{ij}).

THE LEAN UNDER REVIEW (set equality, over an arbitrary [Field k]):
  productRankLocusLE d r := { A | (mult d A).rank ≤ r }       -- claimed = Σ̄^r
  orbitRankLocus M := { A | ∀ i j (h:i≤j), rankPattern A i j ≤ rankPattern M i j }  -- claimed = Ō_M, determinantal
  rankPattern A i j := (submult A i j).rank                    -- the (i,j) rank-pattern entry; corner (0, last N) = rank(mult A)

  HEADLINE: productRankLocusLE d r = ⋃ (M : Tuple d) (_ : (mult d M).rank ≤ r), orbitRankLocus M

  PROOF of the two inclusions:
  - ⊇ : if A ∈ orbitRankLocus M and rank(mult M) ≤ r, then rank(mult A) = rankPattern A (0,last) ≤ rankPattern M (0,last) = rank(mult M) ≤ r.  [corner-entry monotonicity]
  - ⊆ : every A with rank(mult A) ≤ r lies in its OWN orbit closure orbitRankLocus A (since rankPattern A ≤ rankPattern A reflexively), whose corner rank(mult A) ≤ r.  [takes M := A]

  Separately delivered (NOT used in the ⊆ proof above): a brick that every A lies in orbitRankLocus M for a Gabriel NORMAL FORM M (interval direct sum) with the SAME rank pattern as A.

FIDELITY QUESTIONS — answer each crisply:
1. Is { A | rank(mult A) ≤ r } the correct encoding of the paper's Σ̄^r, given the ≥-in-source / ≤-in-digest discrepancy? Is calling it "the genuine Zariski closure of Σ^r" honest for a SET-LEVEL equality that does NOT prove closure = {rk ≤ r} (which would need the rank-raising density fact, valid only for r ≤ min d)?
2. Is taking M := A for the ⊆ direction a GENUINE proof of the paper's stratification, or a TRIVIALISATION that under-delivers? The paper's RHS is implicitly a FINITE union over distinct orbit closures (Gabriel finiteness); the Lean RHS is a union over ALL tuples M. Are these the same SET? Does the all-M union faithfully equal Σ̄^r as a set, even though it is not the finite/canonical index?
3. Is it a fidelity PROBLEM that the headline set equality does not itself use the Gabriel normal form (it is a separate brick), given that a downstream "irreducible components = maximal Ō_M" thread (G3) will need the finite canonical index? Or is separating the bare set equality from the canonical-representative brick defensible?
4. Over an arbitrary [Field k] (NO algebraically-closed, NO char-0): is the SET equality { rk(mult) ≤ r } = ⋃_{corner ≤ r} orbitRankLocus M actually TRUE? (It is a purely rank-pattern / linear-algebra identity; the topology/irreducibility is explicitly deferred.) Any field-dependence hiding in "orbitRankLocus M = Ō_M as the orbit closure" (which over a non-closed / finite field might fail as the literal Zariski closure of an orbit)? The Lean only uses orbitRankLocus as the determinantal SET it is defined to be — does the headline OVERCLAIM "= orbit closure"?

Be precise and adversarial. A specific counterexample beats a vague worry. Distinguish your INFERENCES from FACTS you are confident of.
