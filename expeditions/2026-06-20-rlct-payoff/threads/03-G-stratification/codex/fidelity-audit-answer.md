# Codex (gpt-5-codex, xhigh, read-only, decorrelated) — G2 fidelity audit answer

Consult run during the AUDIT-gate fidelity review of `Core.SigmaStratification`. Decorrelated:
Codex was given the paper objects + the Lean statement and proof sketch, NOT the reviewer's verdict.

## Verdict (4 fidelity questions)

1. **`{rank(mult) ≤ r}` = Σ̄^r:** FAITHFUL at the set level. Matches the *corrected* §4 reading
   (closure of the constant-rank stratum is the rank-≤r determinantal locus; rank is
   lower-semicontinuous). "Genuine Zariski closure" is honest as a rephrasing of lower-semicontinuity;
   the module does NOT assert the density/irreducibility lemma (correctly flagged absent elsewhere).

2. **`M := A` for `⊆`:** GENUINE, not a trivialisation. The all-`M` union intersected with any point
   `A` picks out `orbitRankLocus A`, so the union equals `{rank ≤ r}` literally — set-theoretically
   faithful. Not yet the paper's *finite* stratification, but the collapse lemma
   (`orbitRankLocus_eq_of_rankPattern_eq`) + the normal-form brick
   (`exists_orbitRankLocus_mem_rankPattern_eq`) are exactly the tools to contract to canonical Gabriel
   reps. No logical gap — an intermediate, redundant index.

3. **Separating the canonical-rep brick from the bare set equality:** DEFENSIBLE. The headline does not
   misstate what is proved; it delays invoking the classification. Downstream (components = maximal
   `Ō_M`) cites both pieces.

4. **Arbitrary `[Field k]`, no IsAlgClosed/CharZero:** the SET equality is TRUE — `{rank ≤ r}` is the
   intersection of minor-vanishing conditions, `orbitRankLocus M` is the determinantal rank-pattern
   locus, no orbit-closure topology used; NO hidden field dependence. CAVEAT: the docstrings writing
   "`Ō_M = orbitRankLocus M`" are forward references to the algebro-geometric interpretation (the
   genuine orbit closure, over alg-closed/infinite fields, proved separately in `OrbitClosure` over
   `[Infinite k]`); the Lean OBJECT is the rank-pattern locus. As long as the reader keeps that, the
   *code* does not overclaim.

## Reviewer note on the one nuance
The headline theorem statement is stated purely in `orbitRankLocus`/`productRankLocusLE` terms — it
does NOT carry "= orbit closure" in its statement, so no overclaim in the proved object. The `Ō_M`
naming lives in docstrings and is backed by `OrbitClosure.image_orbitRankLocus_eq_repClosure_orbitSet`
(over `[Infinite k]`), which this module does not re-import or re-prove. Honest.
