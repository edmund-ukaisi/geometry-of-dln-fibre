<task>
I am formalising in Lean 4 + Mathlib (v4.29) the explicit closed-form for the combinatorial
codimension C of the zero-product locus of a deep-linear-network multiplication map
(Lehalleur–Rimányi 2024, Theorem 7.10, rank r=0). I have these COMMITTED, sorry-free Lean facts
and need a PROOF STRATEGY (not code) for the final assembly theorem `qipMin d = cValue d`.

NOTATION (all over ℤ unless noted; d : Fin (N+1) → ℕ weakly increasing, i.e. Monotone d; write
d_i := d i, indices 0..N):
- Feasible set: e : Fin N → ℕ with ∑_{i:Fin N} e_i = d_0.  (Lean e i = paper e_{i+1}.)
- s_i := d_0 - d_{i+1}  (the "qipShift"; i : Fin N so d_{i+1} = d i.succ).
- Phi(e) := ∑_{i:Fin N} (e_i - s_i)^2     [Phi d (↑e), over ℤ]
- Gqip(e) := ∑_{1≤j≤i≤N} e_i (e_j + d_j - d_{j-1})   [the QIP objective, over ℤ]
- qipMin d := min over feasible e of Gqip(e)   [Finset.inf' over the antidiagonal]

COMMITTED LEMMAS I can use:
(A) two_Gqipℤ_sub_sq:  2*Gqip(e) - (∑ e)^2 = ∑_i (e_i - s_i)^2 - ∑_i s_i^2   (all e:Fin N→ℤ).
    On the feasible face ∑e = d_0 this gives  2*Gqip(e) = Phi(e) + d_0^2 - ∑_i s_i^2.
    So minimising Gqip ⟺ minimising Phi, and qipMin = (min Phi + d_0^2 - ∑ s_i^2)/2.
(B) isLeast_sumSq (m:ℕ) (δ:ℤ) (|δ| ≤ m):  IsLeast { v | ∃ t:Fin m→ℤ, ∑ t = δ ∧ ∑ t^2 = v } |δ|.
    i.e. min { ∑ t_i^2 : t:Fin m→ℤ, ∑ t = δ } = |δ|, attained.
(C) drop-to-m (qip_minimiser_support_le_m): for Monotone d, every Phi-minimiser e* over the feasible
    face has e*_i = 0 for all 0-based i ≥ m, where m := qipM d (an explicit Nat.findGreatest threshold,
    1 ≤ m ≤ N). Also have qipS d = S := ∑_{i=0}^m d_i, and qip_separation: m·d_{m+1} > S when m<N.

CLOSED FORM to prove equal to qipMin:
  a := (2S + m) / (2m)   (Int division = ⌊S/m + ½⌋),   δ := S - m·a   (have: |δ| ≤ m, proven).
  cValue := ½( d_0^2 - ∑_{i=1}^m (d_i - d_0)^2 + m(a-d_0)^2 + 2(a-d_0)δ + |δ| ).

The intended math (verified numerically, brute=closed on 7 vectors incl. paper Ex6.2/6.3): on the
m-face, set w_i := e_i + d_{i+1} (so e_i - s_i = w_i - d_0 and ∑_{i<m} w_i = S), then t_i := w_i - a
(so ∑_{i<m} t_i = S - m·a = δ); then ∑_{i<m}(e_i - s_i)^2 = ∑ t_i^2 + 2(a-d_0)δ + m(a-d_0)^2, and
min ∑ t_i^2 = |δ| by (B). The i≥m coords contribute the fixed ∑_{i≥m} s_i^2 = ∑_{i≥m}(d_0-d_{i+1})^2.

KEY DIFFICULTY: qipMin is an inf' over the FULL feasible set (e : Fin N → ℕ, ∑ e = d_0, e ≥ 0),
but the closed form is derived on the m-FACE. (C) says every *minimiser* drops to the m-face, but I
need the VALUE equality min = cValue, which is a two-sided bound:
  (≤) exhibit a feasible attaining e with Gqip(e) = cValue (the explicit rounded witness on the m-face);
  (≥) every feasible e has Gqip(e) ≥ cValue.
For (≥): is it cleanest to (i) show min is attained at some e* (Finset.inf' attained), apply (C) to put
e* on the m-face, then lower-bound Phi(e*) via (B)'s lower bound on the t-coordinates — OR (ii) avoid
(C) entirely and prove ∑_{i<m}(e_i-s_i)^2 ≥ stuff directly plus the i≥m terms ≥ ∑ s_i^2 trivially
(each (e_i - s_i)^2 ≥ s_i^2 fails since e_i≥0 can reduce it)? The e≥0 / ℕ-vs-ℤ and the
"t ranges over ℤ but e over ℕ" gap is the crux: (B) is over ℤ-valued t with NO sign constraint, but my
e_i are ℕ. Does the unconstrained-ℤ minimum |δ| actually get attained by a NON-NEGATIVE e on the
m-face? (Certificate claims yes: in-face nonnegativity a ≥ d_i for i ≤ m, from the within-prefix bound
m·d_i ≤ S.) I need the cleanest logical route that a Lean formaliser can follow without ℚ.
</task>

<output_contract>
1. The single cleanest decomposition of `qipMin d = cValue d` into ≤ and ≥ (or into an IsLeast on the
   Phi-values), naming which committed lemma discharges each piece. Be explicit about whether to route
   the ≥ direction through (C) drop-to-m + attainment, or through a direct per-coordinate bound.
2. The exact handling of the ℕ-vs-ℤ / e≥0 gap: state precisely what must be proven about nonnegativity
   of the attaining witness (the rounded e on the m-face), and whether the LOWER bound (≥) needs e≥0 at
   all or follows from the unconstrained-ℤ bound (B). This is the part most likely to hide a hole.
3. A numbered Lean-shaped proof skeleton (lemma statements + one-line tactic intent each), flagging the
   2–3 steps most likely to be hard in Lean v4.29 (Finset reindexing Fin N ↔ m-face, the t-substitution
   sum algebra, attainment of inf').
4. Any place where my intended derivation has a GAP or an unstated hypothesis (e.g. does the witness
   need d_0 ≥ 1? does (B)'s ℤ-min equal the ℕ-constrained min only because of in-face nonnegativity?).
</output_contract>

<grounding_rules>
Flag explicitly which of your claims are mathematical FACTS you have verified by reasoning vs INFERENCES
about what Mathlib v4.29 provides (you may be wrong about exact lemma names — I will check locally; give
the mathematical content, not just a name). If you think my numeric verification could mask a boundary
bug (e.g. δ=0 vs δ≠0, or m=N no-drop vs m<N), say so and name the discriminating case.
</grounding_rules>
