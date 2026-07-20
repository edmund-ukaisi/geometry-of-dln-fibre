# Paper-read cert — Aoyagi 2023 DLN preprint, proof architecture (2026-07-17)

*Two decorrelated full reads (external controller read + the aoyagi-tree-reader seat), cross-checked
against `theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex` (week-one reproduction, formula
level red-team PASS). PDF: `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/
aoyagi-2023-neural-networks-preprint.pdf` (31 pp). Verified-by-reading unless marked [I]nferred.*

## Architecture (all page cites to the preprint)
Main = Theorem 2 (p.9). Chain: Def 3 (p.8, TYPO — see T-D) → Lemma 2 (p.10, block elimination,
PROVEN elementary) → Theorem 3 (pp.11–13, rank-r product reduction by induction, PROVEN, explicit
unit-triangular P/Q + variable transforms; yields the RLCT split regular-part + λ⟨∏C⟩) →
Theorem 4 (p.14, deepest point — STATED; proof cited to [22] = Entropy 2013) → the recursive
blow-up (pp.14–22, Cases 1(1)/1(2)/2, PROVEN constructions; inductive invariant: ⟨∏C⟩ =
⟨diag(b₁..b_{M(S)})·[E_J 0; 0 D_J]·∏_{s>S+1}C⟩ with b's a divisibility chain and monomial measure
Jacobians ∏u^{M_{s,k}−1}du) → full monomialization at S=L+1 (p.22) → candidates ½min{M_{s,k}}
(p.22) → Lemma 3 (p.24, PROVEN half-page integer minimization) → Theorem 2's closed form →
Lemmas 4–5 + Eqs (1)–(5) (pp.25–27, θ and the explicit achiever charts; Eqs (1)–(5)
assertion-dense).

**Transform-only: VERIFIED.** Integration appears exactly twice: the top Hironaka/CoV pullback
(p.6) and the leaf monomial rule (p.6, cited). §5's body is 100% coordinate changes.

## The decisive completeness findings
- **No "future research" caveat on the construction.** Conclusion (p.27): "we use the inductive
  method and a recursive blow-up method and obtain a manifold with a resolution map." The only
  future-work line (p.28) is applications. (The predecessor's "his stated future work" line came
  from the 2013 general-Vandermonde paper — a class-level statement, NOT about this construction.)
- **Theorem 1 (3-layer, cited to Aoyagi–Watanabe 2005) is NOT load-bearing** — quoted as prior
  work; the general-L proof is self-contained (both reads independently).
- **≤ (achiever) direction: constructed** (Eqs (1)–(5) realize the minimum). **≥ (coverage)
  direction: assertion-level** — "by a blow-up process"; the paper never proves the chart family
  exhaustive / no untracked smaller-ratio divisor. THIS is the one genuine reconstruction
  (map node: coverage-theorem). For hbox it is the ONLY direction needed (the ≤/divergence half is
  already banked natively upstream).
- **External delegations, complete list:** Lemma 1 (ideal-lct invariance, cited [30,31,32] —
  half elementary; banked analogue rlctAt_mono); the monomial rule + Hironaka framework (p.6 —
  monomial rule banked natively, S2 retired); Theorem 4's proof ([22] — transcribe or dissolve
  into coverage+IH; adjudicate at skeleton); θ's count=multiplicity (meromorphic continuation —
  OUT OF SCOPE).
- **Def 3 typo (T-D, image-confirmed):** the printed non-member inequality forces empty selection
  at ℓ=1. Never transcribe; use the geometric ½·min_t Mval(t) (battery: g-def3-broken.py).

## §6-relevant: how her proof handles the product-corank structure
Ideal-theoretically — the RLCT is intrinsic to the ideal (Lemma 1), so non-submersivity of the
multiplication map never arises; the zero-fibre ideal is resolved directly. The recursion's value
is route-independent, but the MECHANISM is coupled at corank ≥ 2: the carried b-monomials couple
across generators; a threshold-only invariant provably breaks (lct(δ²(x²+y²)) = ½ vs
lct(δ₁²x²+δ₂²y²) = 1); certified coupled-binding witness (3,3,4): minAdm = 8 reached only through
a corank-2 cut (battery: g-coupled-binding-334.py, g-delta-flatten.py). DESIGN CONSTRAINT: the
tree datatype carries divisor-support maps (Gen → Finset DivVar) + sharing up to unit.

## Recursion data (for the architect)
Double induction (S = 0..L+1 layer index, J = 0..min(M(S),M^{(S+1)}) cleared pivots). Node carries:
b-monomial vector with divisibility chain; residual block D_J of size (M(S)−J)×(M^{(S+1)}−J);
per-divisor type vector T_{s,k} and exponent M_{s,k} (Jacobian power M_{s,k}−1). Branch on the
equal-run pattern of b's above J: Case 1 (partial run, two sub-cases: divisible-by-existing-u vs
new pivot) / Case 2 (full run). Finite tree; leaves indexed by admissible rank profiles; depth
≤ Σ_s M^{(s+1)}. Representable as an inductive datatype with symbolic divisor support. [I: exact
Lean encoding is the architect's design freedom; the sharing data is not.]
