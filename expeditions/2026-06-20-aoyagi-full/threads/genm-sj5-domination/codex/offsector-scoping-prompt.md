<task>
Adjudicate a SCOPING question in a Lean/measure-theory formalisation of a real-log-canonical-threshold
(RLCT) finiteness recursion for deep linear networks. I withhold my own conclusion; give yours independently.

SETUP (exact objects).
- A "chain" is a width vector M : Fin (L+3) → ℕ. `prod M A` is the ordered product of the layer matrices
  A_s (A_s : ℝ^{M_s × M_{s+1}}); `prod M A` is M_0 × M_{last}. `frobSq X = ∑ X_ij²`.
- `Params M` = the box of all layer tuples. `dropHead M : Fin (L+2) → ℕ` drops the first vertex; its
  product `prod(dropHead M)` is the DEEPER tail, M_1 × M_last.
- A "decoration" D on M carries: exceptional coords u ∈ unitBox (dim d), an accumulated Jacobian monomial
  ∏_ℓ |u_ℓ|^{jac_ℓ}, and a loss `decLoss(u,z)`. Its integral is
      D.integral c' = ∫_{z ∈ dom} ∫_{u ∈ unitBox} (∏|u_ℓ|^{jac_ℓ}) · decLoss(u,z)^{-c'}.
  `carrierThreshold M = ½·minAdm M` (minAdm M = a combinatorial codimension, ≤ M_0·M_1).
- The ADMISSIBLE decorations we care about have the "γ' form":
      decLoss(u,z) = commonDivisor(u)² · frobSq( Γ(z) · Z_tail(z) ),
  where z splits (measure-preservingly) as (Γ, r): Γ is a FREE front block (M_0 × M_1), and
  Z_tail = prod(dropHead M)(r) is the deeper tail (M_1 × M_last), r ∈ Params(dropHead M).

THE RECURSION CONTRACT (`DecoratedStepHyp`). For a chain M of arity L+2 (L+3 vertices), GIVEN the strong IH
    (∀ chains M' of arity L+1, ∀ admissible D' on M', D'.integral c'' < ⊤ for all c'' < carrierThreshold M'),
prove: every admissible D on M has D.integral c' < ⊤ for all c' < carrierThreshold M.

THE INTENDED PROOF (domination, verified by pen-and-paper at the anchor (3,3,2,2) → (2,2,2)):
1. Binding cut t★. Partition the front block Γ (M_0×M_1) by t★ into pivot rows/cols and an a×b freed corner
   (a = M_0−t★, b = M_1−t★, peelCharge = a·b). Partition Z_tail's rows into pivot rows Q_p (t★ rows) and
   corank rows Q_b (b rows).
2. Integrate the FREED a×b corner first. A banked lemma gives, for c' > ab/2 and Q_b·Q_bᵀ PosDef and pivot
   energy w>0:
       ∫_{corner} freedSchurLoss^{-c'}  ≤  det(Q_b Q_bᵀ)^{-a/2} · Cresid · (w + residual)^{-(c'-ab/2)},
   where w = frobSq( Γ_top · Z_tail ) (Γ_top = top t★ rows of Γ; this is the reduced-chain product loss),
   residual ≥ 0, Cresid a constant.
3. Drop the nonneg residual: (w+residual)^{-(c'-ab/2)} ≤ w^{-(c'-ab/2)} (needs c'>ab/2, w>0).
4. w = frobSq(Γ'·A_tail'), the loss of a genuine admissible comparator D' on the reduced chain
   redChain t★ M (arity L+1). So on the region where the units interface holds, the parent integrand is
   ≤ [det(Q_b Q_bᵀ)^{-a/2}] · const · [D'-integrand at exponent c'-ab/2].
5. carrierThreshold_shift: c' < carrierThreshold M ⟹ c'-ab/2 < carrierThreshold(redChain). Apply the IH to
   D' on redChain (arity L+1). Done — IF the divisor det(Q_b Q_bᵀ)^{-a/2} is controlled.

THE FACTS I AM SURE OF.
F1. det(Q_b Q_bᵀ)^{-a/2} ≤ ε^{-ab/2} on the SECTOR {σ_min(Q_b)² ≥ ε} (elementary: b×b Gram ≽ ε·I ⟹ det ≥ ε^b).
    This is pure linear algebra — no metric transversality rate needed, and ONE ε gives one uniform constant.
F2. On {σ_min(Q_b)² ≥ ε}: ∫_sector ≤ ε^{-ab/2}·const·(D'.integral (c'-ab/2)) < ⊤ by the IH. Clean.
F3. Q_b = corank rows of Z_tail = prod(dropHead M)(r). It drops rank on a positive-codim locus of r.
F4. As r → that rank-drop locus, det(Q_b Q_bᵀ)^{-a/2} → ∞. It is NOT a monomial in the current exceptional
    coords u (it varies with the tied tail r at fixed u), so it CANNOT be absorbed into D'.jac.
F5. The base case (width-2 chain) has Z_tail = identity (empty deeper product), so NO rank-drop there; the
    base's units interface holds with a fixed constant. The rank-drop is genuinely a STEP-only phenomenon.
F6. Available machinery: (i) elementary Gram eigenvalue bound (F1); (ii) a pointwise units bridge
    "Z full-row-rank ⟹ ∃c>0, Z Zᵀ ≽ c·I" (c depends on the point, not uniform); (iii) an ALGEBRAIC-GEOMETRY
    rank locus (Zariski-closed determinantal locus) — but NO metric transversality lemma of the form
    "σ_{last}(prod)² ≍ dist(·, rank-drop locus)²". The IH is on arity-(L+1) chains only.

THE QUESTIONS.
Q1. Does closing D.integral over the WHOLE domain (not just the sector) require controlling the integral of
    det(Q_b Q_bᵀ)^{-a/2} · [reduced integrand] over the OFF-SECTOR {σ_min(Q_b) < ε} near the deeper rank-drop?
    Or is there a way the sector bound (F1/F2) plus the IH alone suffice for the whole domain?
Q2. If the off-sector must be controlled: is its integrability a QUANTITATIVE transversality question (the RATE
    at which σ_min(prod(dropHead M)) → 0 near the rank-drop locus, i.e. something like σ² ≍ dist²)? Or can it be
    discharged by the arity-(L+1) IH alone (note: {σ_min < ε} is a subset of Params(dropHead M), and dropHead M
    IS an arity-(L+1) chain — could a DIFFERENT decoration/peel reduce the off-sector to the IH)?
Q3. Concretely at the anchor (3,3,2,2): the deeper tail is prod(3,2,2) (a 3×2 matrix), corank rows b=1.
    Is ∫ det(Q_b Q_bᵀ)^{-1/2}·[reduced (2,2,2) integrand] over a neighbourhood of {rank(prod(3,2,2)) drops}
    finite for c' just below carrierThreshold(3,3,2,2), WITHOUT a transversality rate? Give the cheapest
    concrete check (a 1-parameter degeneration r(t) → rank-drop, integrate in t) that would DISCRIMINATE
    "needs a rate" vs "converges from the sector bound alone".
Q4. Net verdict: does the single-corner-peel + arity-(L+1) IH CLOSE the whole step, or does the off-sector
    genuinely require additional machinery (a metric transversality rate OR a second/nested resolution CoV of
    the deeper rank-drop locus) not implied by F1/F2 + the IH?
</task>

<output_contract>
Answer Q1–Q4 in order, terse. For Q3 give the explicit 1-parameter test and its convergence verdict with the
exponent arithmetic. For Q4 give a one-line NET: "closes from sector+IH alone" OR "off-sector needs a rate / a
further CoV". Flag any place my facts F1–F6 are wrong.
</output_contract>
