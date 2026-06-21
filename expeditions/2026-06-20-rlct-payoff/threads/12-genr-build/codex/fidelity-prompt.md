<task>
You are an independent reviewer adjudicating whether a Lean formalisation's Proved/Cited split is HONEST,
and whether a rank-≤r vs rank=r set-mismatch breaks FIDELITY to a cited paper lemma. Reason from the facts
below only; do not assume access to the repo. Flag inference vs stated fact.

PAPER (Lehalleur–Rimányi 2024, "Geometry of the fibers of the multiplication map of deep linear networks").
- Rep_d = composable matrix tuples; mult(A) = product matrix; d_0, d_N are the outer dims; N+1 vertices.
- Σ^r_d := {A | rank(mult A) = r}   (rank EXACTLY r).
- cSigma^r_d := closure-notation \overline{Σ}^r := {A | rank(mult A) ≥ r}  (rank ≥ r).
- Cor 4.4(a): cSigma^r_d is the Zariski closure of Σ^r_d.
- Lemma 4.5 (rank_0) line 826: codim_{Rep_d} cSigma^r_d = codim_{Rep_d} Σ^r_d = codim_{Rep_{d−r}} Σ^0_{d−r}.
- Lemma 4.6 (rank_vs_fibers, "lem:rank_vs_fibers"): for 0 ≤ r ≤ min d and B of rank r,
  codim_{Rep_d} mult^{-1}(B) = codim_{Rep_d} Σ^r_d + r(d_0 + d_N − r).
  Proof is over k=ℂ: mult restricted to Σ^r is a locally-trivial bundle over the rank-r matrix orbit
  Mat^{rk=r}_{d_N,d_0} (an orbit of G_out = GL_{d_N}×GL_{d_0}, of dimension r(d_0+d_N−r)).

LEAN FORMALISATION (the target under audit).
- productRankLocusLE d r := {A | rank(mult A) ≤ r}   (rank ≤ r). The module docstrings call this "Σ̄^r".
- fibre d B := {A | mult A = B}.
- cCodim d r := inf' over kostantPartitions d r of codimForm; kostantPartitions d r requires corner
  m(0, last N) = r EXACTLY r. cCodim is proved equal to the inf of genuine geometric orbit-closure
  codimensions over corner-exactly-r orbits.
- Brick A (claimed PROVED, zero-cited, axiom-clean [propext, Classical.choice, Quot.sound]):
  theorem codimRepCanonical_productRankLocusLE_eq_cCodim : codim(productRankLocusLE d r) = cCodim d r.
  Proof: codim {rk≤r} = height(sigmaIdeal d r) = ⨅ over corner-≤r orbit closures of their codim = cCodim d r.
  Lower bound uses cCodim_le_codimRepCanonical_of fed ONLY the weak monotonicity cCodim_zero_mono
  (e ≤ e' pointwise ⟹ cCodim e 0 ≤ cCodim e' 0). Upper bound: a minimising corner-r Kostant partition's
  realizer is a corner-r orbit (rank exactly r), attaining cCodim. Uses sigmaIdeal = sInf orbitIdeals
  (general in r), minimalPrimes_sigmaIdeal_eq (general in r). Σ̄^r={rk≤r} is GL_d-stable (finite union of
  orbit closures).
- Brick B (claimed CITED to Lemma 4.6, carried as a STRUCTURE FIELD, not a global axiom):
  BundleShiftInterface.cited_bundle_shift_lemma46 : ∀ B r, B.rank=r → (∀k', r ≤ d k') →
    codim(fibre d (B.map ι)) = codim(productRankLocusLE d r) + (r*(d_0 + d_N − r) : ℕ).
- R2-general (transport): rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi
  (I : RlctInterface)(J : BundleShiftInterface)(hB:B.rank=r)(hr:∀k', r≤d k')(h) :
    I.rlct(lossDLN d B) = ((cCodim d r).toNat + r*(d_0+d_N−r))/2.
  I.cited_aoyagi_dln (a separate carried field, Aoyagi) gives rlct = ½·codim(fibre); J rewrites the fibre
  codim by the shift; Brick A rewrites codim Σ̄^r = cCodim d r.

THE TWO QUESTIONS:
1. The Lean Σ̄^r is {rk ≤ r}; the paper's Σ^r is {rk = r} and cSigma^r is {rk ≥ r}. These are three
   DIFFERENT sets for 0 < r < min d. Brick A proves codim{rk≤r} = cCodim d r (corner-exactly-r partitions),
   and Brick B/Lemma 4.6 wants codim Σ^r = codim{rk=r}. Does codim{rk≤r} = codim{rk=r} = codim cSigma^r here,
   so that the Lean shift interface (stated with {rk≤r}) faithfully transcribes Lemma 4.6 (stated with
   {rk=r})? Or is there a real codimension mismatch that makes the carried Brick B interface NOT the paper's
   Lemma 4.6? Consider whether r ≤ min d (the ∀k', r≤d k' guard) is what guarantees agreement.
2. Is anything in Brick A secretly assuming the bundle shift (Lemma 4.6) or fibre-dimension content?
   I.e., is the Proved/Cited boundary honest, or does the "proved" codim Σ̄^r = cCodim d r covertly depend on
   a fibre-dimension fact that should be Cited?
</task>

<output_contract>
Three short sections, no preamble:
A. RANK-MISMATCH VERDICT — does codim{rk≤r}=codim{rk=r}=codim cSigma^r hold here (state the reason: which
   stratum dominates the codim of a finite union, and the role of the r≤min d guard); is the Brick B
   interface a faithful transcription of Lemma 4.6 or a mismatch? One paragraph.
B. PROVED/CITED HONESTY — is Brick A free of hidden fibre-dimension/bundle assumptions, given its stated
   proof route (orbit-closure ideal height + weak combinatorial monotonicity)? Is the split honest? One
   paragraph.
C. ANY OTHER FIDELITY RED FLAG you see in the setup (e.g. the ℕ-subtraction d_0+d_N−r, the .toNat casts,
   B.rank over ℝ vs codim over K). Bullet list; "none" is acceptable.
For each, mark [FACT] vs [INFERENCE].
</output_contract>

<grounding_rules>
You have only the facts above; do not invent Lean lemma behaviour. If a claim depends on a fact not given
(e.g. whether {rk=r} is nonempty under r≤min d), say so explicitly and mark it [INFERENCE]. Do not produce
Lean code. The diagnosis is what is wanted, not a proof.
</grounding_rules>
