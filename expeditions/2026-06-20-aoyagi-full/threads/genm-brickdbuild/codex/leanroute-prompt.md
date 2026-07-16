<task>
Design a Lean 4 / Mathlib formalization route for a matrix-integral FINITENESS bound whose exact-math proof is DONE (pen-and-paper). I need the cheapest formalizable decomposition and the single hardest Lean sub-step. My own plan is WITHHELD.

THE BOUND (proven true; formalize `< ⊤`): fix widths M0,M1,M2, cut u, a=M0−u, b=M1−u, n=M2, WITH SCOPE a+b ≤ n. q = c'−ab/2, ab/2 < c' < T1 := ½·minAdm(M). z ranges a box of "deep" params; Qp=Qp(z) is u×n (poly in z, generic rank u); A_cor ranges box [-1,1]^{b×n}, Qb:=A_cor (b×n); hsQ=(Qp;Qb) is (u+b)×n; Πb=proj onto row(Qb). Front P(u×u), B(u×b), C(a×u). Show
  G := ∫_z ∫_{A_cor box} det(Qb Qbᵀ)^{−a/2} · [ ∫_{P,B,C box} (‖P·Qp+B·Qb‖²_F + ‖C·Qp·(I−Πb)‖²_F)^{−q} ] < ⊤   for c'<T1.

THE PEN-AND-PAPER PROOF (to formalize): on a b×b minor chart Qb=D·[I_b|X] (D∈GL_b, X∈ℝ^{b×d}, d=n−b), then Qp=[U|UX+W], and:
- transverse Schur monomializes: ‖Qp(I−Πb)‖²_F = tr(W(I+XXᵀ)^{−1}Wᵀ) ≍ ‖W‖²_F.
- output shear H=PU+BD (det-1): E_top+E_tr ≍ ‖H‖²_F + ‖Y·W‖²_F, Y=(P;C)∈ℝ^{M0×u}.
- Jacobians: dQb=|det D|^d dD dX; det(QbQbᵀ)^{−a/2}=|det D|^{−a}det(I+XXᵀ)^{−a/2}; dB=|det D|^{−u}dH. Net |det D| power = n−b−a−u.
- incidence strata: rank W ≤ u−h has codim h(n−b−u+h); on the rank-ℓ chart of W (h=u−ℓ) and rank-s chart of the Y-block, normal codim C_{ℓ,s}=ub+M0·ℓ+(M0−s)(u−ℓ−s)+s(d−ℓ), and the per-stratum piece is a monomial radial ∫₀^δ r^{C_{ℓ,s}−1−2q}dr, finite for q<C_{ℓ,s}/2. min_{ℓ,s}C_{ℓ,s}/2 = T1−ab/2 (exhaustively verified). Sum finitely many strata ⟹ G<⊤ for c'<T1.

BANKED Lean lemmas I can feed (all sorry-free, Mathlib v4.29):
- matBox_frobSq_neg_lintegral_lt_top: ∫_{[-1,1]^{p×q}} ‖T‖_F^{−2c'} < ⊤ for c' < pq/2 (via reshape to ℝ^{pq} + a banked pi-cube ‖·‖^{−2c'} finiteness).
- detGram_lintegral_box_lt_top: ∫_{[-1,1]^{r×n}} det(XXᵀ)^{−a/2} < ⊤ for a+b≤n-type Wishart threshold (r≤n).
- uniformWenn_proj_le, shell_corankPivot_coupled_le (the corank Γ-peel producing det^{−a/2} + shift q + coupled transverse-Schur residual).
- Matrix-space Haar CoV via the RAW pi type (Fin p → Fin q → ℝ), NOT Matrix.module (instance-diamond); LinearMap.det factors by det_pi. Measure-preserving reindex/reshape lemmas exist.
- GL_b minor charts, det, submatrix rank exist; NO general resolution-of-singularities / blow-up / stratified-CoV framework in Mathlib.
</task>

<output_contract>
Four terse sections:
1. FEASIBILITY: is this formalizable as BOUNDED labour (finite explicit charts + banked box-integrals + explicit Jacobian CoVs), or does it need frontier infra Mathlib lacks? One-line verdict + the single deciding reason.
2. DECOMPOSITION: the minimal ordered list of Lean lemmas (≤ ~8) from the banked pieces to G<⊤, each one line (name-ish + statement shape). Mark which are banked vs new.
3. HARDEST SUB-STEP: the single hardest Lean lemma and WHY (the specific Mathlib-API friction — minor-chart CoV Jacobian? the finite stratification/partition-of-domain? the |det D| power CoV? the per-stratum radial monomial finiteness?). Is it labour or a genuine Lean wall?
4. CHEAPER ALTERNATIVE: is there a route AVOIDING the explicit stratification — e.g. a global CoV to (D,X,H,Y,W) coordinates + a single joint box-integral finiteness with the |det D|^{n−b−a−u} weight, dominating without partitioning into rank strata? If so sketch it; if not, why the stratification is unavoidable.
</output_contract>

<grounding_rules>
Distinguish "standard Mathlib CoV/measure labour" from "missing Mathlib primitive". If you claim a step is bounded labour, name the Mathlib lemma family it uses. If a Lean wall, name the missing primitive. Flag inference vs fact.
</grounding_rules>
