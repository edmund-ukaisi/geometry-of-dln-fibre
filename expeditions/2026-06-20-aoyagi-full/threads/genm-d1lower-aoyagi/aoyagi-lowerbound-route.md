# D1 ≥-leg: does the DLN RLCT LOWER bound admit an elementary DLN-specific route? (genm-d1lower-aoyagi)

Read-only pen-and-paper adjudication. Distinct angle from genm-d1scope (which scoped the *Lean plumbing*
and found the general-v Morse-Bott chart is Mathlib-lacking = WALL). This traces **Aoyagi's actual
lower-bound method** from the primary source, to decide whether the ≥-leg is really general parametrized
Morse-Bott or a DLN-specific bounded explicit-blow-up build.

Primary source (IN REPO): `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`
(= Aoyagi 2024, Neural Networks 172 106132, the cited DLN RLCT paper). Extracted to `/tmp/aoyagi-2024-dln.txt`
via `pdftotext -layout`. Also read: LR paper §8 (main.tex 1782-1937); Aoyagi 2025 follow-up (arXiv 2501.12747);
Aoyagi 2019 Vandermonde (Entropy 21(6):561).

---

## VERDICT: WALL SUBSTANTIALLY DOWNGRADED — the ≥-leg is a BOUNDED explicit-blow-up build, NOT general Morse-Bott.

genm-d1scope's WALL verdict was about the *specific Lean chart route currently wired* (the general-v
constant-rank/Morse-Bott IFT chart, which Mathlib lacks). It is correct **about that route**. But the
mathematics of Aoyagi's ≥-leg does **not** use general parametrized Morse-Bott at all. It uses:
- explicit linear-algebra block reduction (Lemma 2 + Theorem 3),
- a **homogeneity / deepest-singular-point** comparison lemma (Theorem 4),
- an **explicit, constructive, recursive sequence of monomial blow-ups along named submanifolds**
  (Cases 1/1(1)/1(2)/2), indexed combinatorially by the reduced dimensions M^(s),
- from which the RLCT is read off the normal-crossing exponents (= the S2 `monomial_rlct` extraction) +
  an elementary arithmetic minimization (Lemma 3).

There is **no non-constructive Hironaka step, no Morse-Bott, no constant-rank-splitting, no
IFT-with-parameters** inside the proof of the main theorem (Section 5). Hironaka is cited only in the
general Section-2 framing, not used for the DLN function itself.

So the operator's option **(a) "charge the Morse-Bott formalisation"** is mis-scoped: the honest general
machinery Aoyagi uses is NOT Morse-Bott. The real from-scratch cost is the **explicit blow-up
combinatorics** — bounded but intricate (spans preprint pages 14-27).

---

## The exact source method (Section 5, "Proof of Main Theorem")

Notation: L layers; widths H^(1),…,H^(L+1); true product rank r; reduced dims M^(s) = H^(s) − r.
The loss RLCT to compute: `λ⟨ ∏_{s=1}^L A^(s) − ∏ A*^(s) ⟩` = `rlct(K)`, K the square loss.

**Step 0 — reduce integral loss to the pure algebraic function (Aoyagi 2025 Thm 3, the Gram sandwich).**
`K(w) = ∫ (h(x,A,B) − h(x,A*,B*))² q(x) dx` is sandwiched `α₁·Σ h̃² ≤ K ≤ α₂·Σ h̃²`, where h̃ are the
polynomial coefficients (= entries of the product-difference matrix) and α₁,α₂ = min/max eigenvalues of a
positive-definite Gram matrix `∫ C(x)q(x)dx`. RLCT is invariant under multiplication by such a
bounded-above-and-below positive factor (ideal-equality Lemma 1). ⟹ `rlct(K) = rlct(||∏A^(s) − ∏A*^(s)||²)`.
[Aoyagi 2025, Theorem 3 lines 494-536, Theorem 4 lines 719-908; the Lean D1 skeleton's "loss → algebraic
fibre defining function" reduction is exactly this.]

**Step 1 — block-diagonal linear-algebra normal form (Lemma 2 + Theorem 3).** By explicit regular row/col
operations (Lemma 2, lines 861-958: elimination via a regular r×r corner) iterated through the product
(Theorem 3, lines 982-1223), `P1(∏A^(s))P2 = diag(C1, ∏C^(s))` with P1,P2 regular, C^(s) the reduced
M^(s)×M^(s+1) matrices. The RLCT SPLITS additively (lines 1226-1267):

    λ⟨ ∏A^(s) − ∏A*^(s) ⟩ = [ −r² + r(H^(1)+H^(L+1)) ]/2  +  λ⟨ ∏ C^(s) ⟩.

The first term = RLCT of the **regular/transverse** block (the C1−E_r, F2, F3 coordinates — a full-rank
sum of squares, RLCT = ½·(#coords)). This is precisely the "regular part + degraded core" peel the Lean
D1 skeleton reflects, and it is elementary linear algebra + smooth-part RLCT additivity.

**Step 2 — reduce to the DEEPEST singular point (Theorem 4, THE key lemma).** The entries of ∏C^(s) are
**homogeneous of degree L** in the C-variables. Theorem 4 (lines 1282-1297): for homogeneous F_i with a
C^∞ weight φ, `λ_{(0,…,0,w*)}⟨F⟩ ≤ λ_{(w*_1,…,w*)}⟨F⟩` — the RLCT at the origin (all homogeneous coords → 0,
the DEEPEST point) is a LOWER bound for the RLCT anywhere. Applied immediately (lines 1307-08) to set
r^(s)=r WLOG. **This is the DLN-specific resolution of the sub-wall** (rlct-runway memory point 3): the
worry "a deeper stratum could have SMALLER rlct" is exactly what Theorem 4 controls — for a homogeneous
sum-of-squares the deepest point is the WORST (smallest) rlct, so computing it there gives the global inf,
and it turns out to equal codim/2. NOT a general Morse-Bott statement — a homogeneity comparison.

**Step 3 — explicit recursive monomial blow-up of ∏C^(s) (Cases 1/1(1)/1(2)/2).** "We prove the main
theorem by developing blow-up method along submanifolds … a recursive blow-up process" (lines 1321-1333).
Explicit blow-ups along NAMED submanifolds `{d_ij=0, u_{s,k}=0}` (Case 1, lines 1496-1503) / `{d_ij=0}`
(Case 2, lines 1999-2005), with explicit monomial coordinate substitutions (d_ij = u_{s,k}·d'_ij, etc.)
and explicit Jacobian determinant `∏ u_s^{(exponent)}` (lines 1382-1454). Induction on (S,J) with ordered
vectors T_{s,k}. Terminates in the diagonal monomial ideal `⟨∏C^(s)⟩ = ⟨diag(b_1,…,b_{M^(L+1)})⟩`
(lines 2334-2339) — a NORMAL-CROSSING form. Bottoms out on the reduced-rank-regression base case
(Theorem 1 = Aoyagi-Watanabe 2005b [12], lines 499-542), "completes the proof by induction" (line 1222).

**Step 4 — read off RLCT from the monomial exponents (= S2) + arithmetic min (Lemma 3).** The threshold
candidates are read from the exponents M_{s,k} (lines 2342-2360) — this is EXACTLY the S2/`monomial_rlct`
extraction `min_j (h_j+1)/(2k_j)`. Lemma 3 (lines 2596-2631) is a pure arithmetic minimization
`min_b A(b) = a·ℓ(ℓ−a)`, giving the closed value 2λ = codim (Theorem 2, lines 743-830), and θ = a(ℓ−a)+1.

---

## What "cite-only-S2" would need — the residual from-scratch content

Assuming the target Lean library has (i) S2 = `monomial_rlct` (monomial normal form → RLCT), (ii) RLCT
invariance under a bounded-±-positive analytic factor (Step 0's Gram sandwich + ideal-equality), (iii)
RLCT additivity over disjoint variable blocks (smooth-part), the residual ≥-leg content is:

1. **The homogeneity/deepest-point comparison (Theorem 4).** The ONE extra analytic lemma beyond
   S2+linear-algebra. NOT a resolution/Morse-Bott existence theorem — a self-contained statement:
   for homogeneous F, `rlct_origin ≤ rlct_nearby`. **This is the honest general lemma to formalize**
   (bounded, classical; likely feasible in Mathlib, unlike Morse-Bott). Cost: 1 named analytic atom.
2. **Lemma 2 + Theorem 3** (block-diagonal normal form + additive RLCT split): explicit linear algebra.
3. **The recursive blow-up combinatorics** (Cases 1/1(1)/1(2)/2, the (S,J) induction, T_{s,k} ordering,
   Jacobian exponent bookkeeping): the LARGE bounded piece. Explicit but intricate (pages 14-27). This is
   where the from-scratch labour lives — but it is combinatorial/algebraic, not a Mathlib-lacking analytic
   existence theorem.
4. **Lemma 3** arithmetic minimization: elementary.

The DLN engine already banks large parts of this (the R1-LOWER `monomial_rlct`-carrying (2,2,2) cover, the
det-Jacobian achiever charts, the deepRank=0 atom) — these ARE realizations of Step-3-style explicit blow-ups
for small dimension vectors. So the general-v ≥-leg is the ∀-dimension-vector LIFT of already-charged
explicit-blow-up machinery, NOT a new analytic wall.

---

## Kill-conditions a formaliser would check
- **KC-1 (Theorem 4 homogeneity).** Confirm the DLN reduced-core defining functions are genuinely
  homogeneous in the blow-up coordinates so Theorem-4's `rlct_origin ≤ rlct_nearby` applies (degree-L
  monomials in the C^(s) entries — yes for the pure product; the bias terms are absorbed by the Step-0
  change of variables B'^(1), Aoyagi 2025 lines 896-907). If the homogeneity fails at a MIDDLE stratum
  (a,b)≠(0,0), Theorem 4 must be applied to the SHIFTED/degraded core M' (the same recursion) — check the
  recursion covers the rectangular M' widths (LR §8 rectangular M', matches Item-109's rectangular hCore).
- **KC-2 (blow-up terminates in normal crossing for all M^(s)).** The (S,J) induction must reach
  `⟨diag(b_i)⟩` for EVERY reduced dimension vector, not just the small cases — this is the exhaustiveness
  the ∀-v lift needs. A single checked (2,2,2)/(3,3,3) instance is NOT the ∀-v proof.
- **KC-3 (S2-cleanliness).** The final RLCT extraction (Step 4) must go through `monomial_rlct` ONLY — no
  second analytic axiom. Theorem 4 (KC-1) must be PROVED, not axiomatized, else the "cite-only-S2" headline
  degrades to "cite S2 + cite Theorem 4". Both are classical; Theorem 4 is the honest additional target.

## Registers
- **Claim (most load-bearing):** the DLN ≥-leg is a homogeneity-reduction (Thm 4) + explicit recursive
  monomial blow-up + S2 extraction, NOT general parametrized Morse-Bott. The Mathlib-lacking "constant-rank
  split with parameters" that genm-d1scope identified is an artefact of the *particular IFT chart route
  currently wired in Lean*, not of Aoyagi's actual argument.
- **Most likely to break the bounded verdict:** if the explicit blow-up combinatorics, when lifted to ∀
  dimension vector, hides a case where the normal-crossing form is NOT reachable by the named submanifold
  blow-ups (i.e. the induction is not actually uniform) — then a genuine resolution step would re-enter.
  The source presents it as uniform (one induction, two cases) but the Vandermonde-companion papers (2019)
  do H=1,2,3,4 case-by-case — a tension worth a formaliser's scrutiny (KC-2). Aoyagi 2024 claims the
  uniform induction closes; verify it does before committing to ∀-v.
- **Next construction that would settle the open part:** formalize Theorem 4 (the homogeneity comparison)
  as a standalone lemma — it is the single non-linear-algebra ingredient, and its feasibility in Mathlib
  is the pivotal de-risk for whether option (a) should be "charge Theorem-4 + blow-up combinatorics"
  (bounded) rather than "charge Morse-Bott" (a research-level Mathlib contribution). If Theorem 4 is
  Mathlib-feasible, D1 de-conditionalizes to a large-but-bounded build.

## Decorrelated Codex (PDF-grounded, web-search OFF)
`codex/aoyagi-route-answer2.md` — independent read of the SAME primary PDF from scratch, reached the SAME
structural verdict with line citations, and independently flagged the SAME nuance (Theorem 4 is the one
extra lemma beyond S2+linear-algebra; "no wall from missing general resolution or Morse-Bott/IFT"). A
first web-search-enabled consult (`codex/aoyagi-lowerbound-answer.md`) spun on empty sandbox web searches
and was stopped without a final answer (infra limitation, not a substantive result).

---
*(Captured to canonical by the controller, 2026-07-03, from genm-d1route's report. The decorrelated Codex
artefacts remain in the main-checkout worktree at `.../genm-d1lower-aoyagi/codex/`; capture them at
expedition close if the operator wants the full Codex trail durable.)*
