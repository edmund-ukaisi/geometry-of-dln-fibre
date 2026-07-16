# Decorrelated soundness review: a Lean "full-block finiteness" argument

You are a red-team reviewer. I give you a self-contained MATH argument (extracted
from Lean 4 / Mathlib code, but judge the MATH, not the syntax). Hunt for a
soundness hole. Concrete counterexample beats vague doubt. Distinguish
INFERENCE (your reasoning) from FACT (standard theorem).

## Setup (real matrices, Lebesgue/lintegral over boxes)

Fix naturals u ≥ 1, a = M0−u ≥ 0, b = M1−u ≥ 0, n. Let N = (u+a)(u+b).
- `matBox p q 1` = { p×q real matrices with every entry in [−1,1] } (volume (2)^{pq}).
- `genBox` = same thing (entrywise [−1,1]).
- `frobSq X = Σ_ij X_ij²` (squared Frobenius norm).
- Q : (u+b) × n real matrix (rows indexed by u+b, columns by n). "the shell" on
  Q is the condition (Q·Qᵀ − ε²·I_{u+b}) is positive semidefinite, i.e. the
  smallest eigenvalue of the (u+b)×(u+b) Gram Q·Qᵀ is ≥ ε², with ε>0 fixed.
- B ranges over the (u+a)×(u+b) block box (each entry in [−1,1]); B = [[P,B12],[C,D]].

There are two quantities, both `ℝ≥0∞`-valued lintegrals, with c' ≥ 0 a real exponent:

LHS(c') := ∫_z ∫_{A_cor ∈ box ∩ shell(z)} ∫_{x∈outerDom} ∫_{D∈genBox}
             ( frobSq( B(x,D) · Q(z,A_cor) ) )^{−c'}
   where on the shell, Q(z,A_cor)·Q(z,A_cor)ᵀ ⪰ ε²·I. (outerDom restricts P invertible.)

RHS(c') := ∫_z ∫_{v∈[0,1]} |v|^{m0−1} ∫_{A∈matBox b M2 1} ∫_{Γ∈genBox a b 1}
             ( v²·P0(z) + frobSq( Γ·(A·Z(z)) ) )^{−c'}
   where m0 = minAdm(redChain u M) ≥ 1, P0(z) = frobSq(prod z) > 0 for a.e. z,
   a·b = (M0−u)(M1−u).

## The claimed lemmas (judge each for soundness)

(1) Loewner floor: if Q·Qᵀ ⪰ ε²·I_{u+b}, then for ANY (u+a)×(u+b) matrix B:
       ε²·frobSq(B) ≤ frobSq(B·Q).
    [proof idea: per row v of B, ‖v·Q‖² = vᵀ(QQᵀ)v ≥ ε²‖v‖²; sum over rows.]

(2) Shell bound: on the shell, LHS(c') ≤ ε^{−2c'} · ∫_{matBox (u+a)(u+b) 1} frobSq(A0)^{−c'}.
    [from (1): frobSq(B·Q)^{−c'} ≤ (ε²·frobSq(B))^{−c'} = ε^{−2c'}·frobSq(B)^{−c'}
     since −c' ≤ 0; drop the invertible-P restriction by enlarging to the full box;
     reindex block box → matBox.]

(3) Pure-box finiteness: for 0 < c' < N/2, ∫_{matBox N-shaped box} frobSq^{−c'} < ⊤.
    [∫_{[−1,1]^N} ‖X‖^{−2c'} dX < ∞ iff 2c' < N.]

(4) RHS divergence: if 2c' ≥ m0 + a·b, then RHS(c') = ⊤.
    [per a.e. z with P0(z)>0, the v-fibre integral is ⊤: restrict Γ to a box of
     radius ρ = v·√(P0/K) so frobSq(Γ·(A·Z)) ≤ v²·P0, then inner ≥ D·v^{ab−2c'},
     integrand ≥ C·v^{(m0−1)+ab−2c'}, and (m0−1)+ab−2c' ≤ −1 ⟺ m0+ab ≤ 2c', so
     the 1-D monomial ∫_0^δ v^{≤−1} = ∞.]

(5) Nat chain: m0 + a·b ≤ N = (u+a)(u+b), given the hypothesis m0 ≤ u·tailMinWidth
    and tailMinWidth ≤ M1 (so u·tailMinWidth ≤ u·(u+b) since M1 ≤ u+b).

## The assembled claim (THE THING TO RED-TEAM)

Theorem: RHS(c') < ⊤  ⟹  LHS(c') < ⊤   (for 0 ≤ c', u ≥ 1).
Proof: contrapositive of (4) gives RHS<⊤ ⟹ 2c' < m0+ab. Chain (5): m0+ab ≤ N.
So 2c' < N, i.e. c' < N/2. Then (2)+(3) give LHS < ⊤ (c'=0 handled separately,
trivially finite). ∎

## Questions

Q1. Is lemma (1) correct as stated (the whole-block Frobenius floor from the
    row-Gram Loewner floor on Q)? Any dimension/transpose subtlety?
Q2. Is the assembled implication SOUND? In particular: is the region {c' < N/2}
    (where LHS is shown finite) genuinely a SUPERSET of {RHS < ⊤} (⊆ {c' <
    (m0+ab)/2})? I.e. is (m0+ab)/2 ≤ N/2 the right direction?
Q3. A soundness note elsewhere warns: "dropping the corank over-estimates LHS to
    ⊤ for c' ∈ (uρ/2, (m0+ab)/2)" — does the full-block route (which does NOT drop
    the corank; it keeps the whole block B including corank rows C,D) evade that
    trap? Or does keeping the whole block introduce a DIFFERENT over/under-estimate
    that could make (2) FALSE (LHS actually larger than the bound)?
Q4. Any regime of c' ≥ 0 where the argument silently fails (c'=0, c' exactly N/2,
    empty boxes a=0 or b=0, degenerate ε)? Is the bound VACUOUS anywhere it claims
    content?
Q5. Any hidden assumption that Q has full row rank / n ≥ u+b? Does the shell
    condition Q·Qᵀ ⪰ ε²·I already guarantee everything (2) needs, with NO extra
    rank hypothesis on Q?

Answer each Q crisply. If you find a hole, give the minimal failing scenario.
