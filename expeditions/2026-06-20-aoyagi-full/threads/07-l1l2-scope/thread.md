# Thread 07 — L1/L2 scope: block elimination + product reduction (pp, read-only)

- **Seat:** `pp`. **Read-only + /tmp scratch** (`/tmp/l2_*.py`, `/tmp/codex-l2-*.md`); controller integrates.
- **Status:** scoped — the last unscoped critical-path rung. Design now COMPLETE below R1.

## L1 — block elimination (Lemma 2, p.10) — MODERATE

For `A` (h₁×h₂) with regular `r×r` top-left block `A₁`, `rank A = r₁ ≥ r`: unitriangular regular
`Q₁=[[E_r,0],[F₃,E]]`, `Q₂=[[E_r,F₂],[0,E]]` (analytic in A's entries) with
`Q₁ A Q₂ = diag(A₁, C₄)`, `C₄ = A₄ − A₃A₁⁻¹A₂` (Schur complement), `rank C₄ = r₁−r`. Proof: clear
lower-left then upper-right; variable changes `F₃=−A₃A₁⁻¹`, `F₂=−A₁⁻¹A₂` regular. Pure block algebra over
the analytic local ring (A₁ an analytic unit). Lean: `block_elimination`. No measure theory.

## L2 — product reduction (Theorem 3, pp.11–13) — MODERATE

Regular `P₁,P₂` (built by induction over layers via L1) with `P₁(∏A^(s))P₂ = diag(C₁, ∏C^(s))`, `C₁`
regular `r×r`, `C^(s)` size `M^(s)×M^(s+1)` (`M^(s)=H^(s)−r`), core `∏C` vanishing at the deepest point.
Lean: `product_reduction`. Induction over layers, each an L1 step + a regular variable change.

## The additivity (assembly, p.13 — the load-bearing point)

It's the transformed **error** matrix (not just the product) that splits:
`P₁(∏A − diag(E_r,0))P₂ = [[C₁−E_r, −F₂],[−F₃, ∏C − F₃F₂]]`. So `⟨∏A − B⟩ = ⟨C₁−E_r, F₂, F₃, ∏C−F₃F₂⟩`;
`F₃F₂ ∈ ⟨F₂,F₃⟩` ⇒ the core reduces to `⟨∏C⟩` modulo the regular generators (uses S1.3 ideal-invariance).
The regular generators `{C₁−E_r, F₂, F₃}` are in variables DISJOINT from the core ⇒ RLCT ADDS:
> `λ(‖∏A − ∏A*‖²) = [−r² + r(H¹+H^{L+1})]/2 + λ_core(⟨∏C^(s)⟩)`.
(r=0 ⇒ reg=0 = all ground-truth cases.) **Needs the new S1.5 (below).**

## NEW LEMMA — S1.5: RLCT additivity over disjoint variable blocks

`λ(F(x)²+G(y)²) = λ(F²)+λ(G²)` for disjoint `x,y` (Aoyagi 2013 App C Lemma 2). NOT derivable from
S1.1–S1.4 — the engine of the regular/core split. Codex's clean proof: Laplace/Mellin
`(F+G)^{−c}=Γ(c)⁻¹∫t^{c−1}e^{−tF}e^{−tG}dt`, `L_F(t)~t^{−λ(F)}(log t)^{m_F−1}` ⇒ product
`~t^{−(λ_F+λ_G)}(log)^{m_F+m_G−2}` ⇒ converges iff `c<λ_F+λ_G`; **orders add too** (`m_F+m_G−1`).
- **The L2 USE only needs the smooth-block case** (the regular generators are already coordinates), the
  light monomial case — the fully-general S1.5 (which would need resolution to reach normal-crossing) is
  not required just for L2. Add S1.5 to the S1 suite; flag whether the Laplace-asymptotic `L_F~t^{−λ}(log)`
  is cited or (prove-all-but-S2) derived from R1's normal-crossing + the monomial Laplace asymptotic.

## Terminology correction (fold into design-spec)

The regular term `r(H¹+H^{L+1}) − r² = r(H¹+H^{L+1}−r)` is the **DIMENSION of the rank-r stratum** =
the number of transverse smooth coordinates to fix (C₁−E_r: r²; F₂: r(H^{L+1}−r); F₃: (H¹−r)r), each
contributing ½ (via S1.5). It is **NOT** the determinantal codim `(H¹−r)(H^{L+1}−r)`. Identity:
`r(m+n−r) = mn − (m−r)(n−r)`. So "reg = ½·codim" was wrong; it's `½·(rank-r stratum dimension)`. The
encoded `aoyagiLambda` reg term `(−r²+r(H⁰+H^{last}))/2` already uses the CORRECT value — description fix
only. Verified symbolically + differential-rank at an r=1 point (H=(3,2,3): error-map rank 5 = r(H¹+H³−r)).

## Ordering (confirmed) + difficulty

`L1 → L2 (→ reg + λ_core) → D1 (inf attained at core's deepest point) → R1 (resolve core) → A1`.
L1, L2: MODERATE (block algebra + induction; no measure theory — most Lean-tractable after the defs). The
additivity's analytic content is entirely S1.5 (new) + S1.3. S1.5: MODERATE (smooth-block case for L2).
