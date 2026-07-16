<task>
Adjudicate one MATH question (not Lean): does an "interior front-charge integrand" reduce to a
"charged rectangular Schur core" via dropping one nonneg term + a projector identity, and is there a
loss-model MISMATCH that blocks the reduction?

Setup (all real matrices; dims: a := M0-u pivot/output rows, b := M1-u corank rows, deep width p).
Fix reduced params z and a corank matrix A_cor. Let:
- Z_deep = Z_deep(z)  (deep factor, b'×p-ish, a function of z only),
- Q_b := A_cor · Z_deep   (the "corank block", b×p; assume full row rank so Q_b Q_bᵀ is PosDef),
- Q_inl, Q_inr  = two row-blocks of a stacked matrix hsQ (Q_inr = Q_b is the corank block; Q_inl the
  "pivot" block),
- front block x = (P, B12, C) integrated over a BOUNDED box outerDom: P is a×a (invertible on the box),
  B12 is a×b, C is (something)×(pivot),
- Qtp := Q_inl + P⁻¹ · B12 · Q_inr   (the "tilde" pivot block),
- E_top(x) := frobSq( P · Qtp )        [pivot energy]
- proj := Q_bᵀ (Q_b Q_bᵀ)⁻¹ Q_b       [orthogonal projector onto row-space of Q_b = Q_inr]
- E_tr(x)  := frobSq( C · Qtp · (1 - proj) )   [transverse Schur energy]
- q := c' - a*b/2  > 0.

The FRONT-CHARGE integrand (per fixed (z, A_cor)) is:
  frontCharge(z,A_cor) = det(Q_b Q_bᵀ)^(-a/2) · Cresid · ∫_x (E_top(x) + E_tr(x))^(-q) dx
Note det(Q_b Q_bᵀ) is x-INDEPENDENT so it factors out of the x-integral.
The BOX integral adds ∫ over (z, A_cor).

schurB's target "ChargedRectSchurCore" bounds a DIFFERENT integral (S plays the role of Z_deep):
  ∫_Δ ∫_Acor ∫_S  det((Acor·S)(Acor·S)ᵀ)^(-a/2) · frobSq(Δ·S)^(-c')  dS dAcor dΔ
i.e. the loss is a SINGLE frobSq(Δ·S)^(-c') where the SAME S appears in charge and loss.

My proposed bridge (verify or refute each step):
(S1) Projector identity: since proj projects onto row-space of Q_b = Q_inr, we have Q_inr·(1-proj) = 0
     EXACTLY (when Q_b Q_bᵀ invertible). Hence Qtp·(1-proj) = Q_inl·(1-proj) + P⁻¹B12·Q_inr·(1-proj)
     = Q_inl·(1-proj). So E_tr = frobSq( C · Q_inl · (1-proj) ) — independent of P, B12.
(S2) Since E_top ≥ 0 and q>0: (E_top+E_tr)^(-q) ≤ E_tr^(-q). So ∫_x (E_top+E_tr)^(-q)
     ≤ ∫_x E_tr^(-q) = Vol(P,B12) · ∫_C frobSq(C · Q_inl(1-proj))^(-q).
(S3) Hence frontCharge ≤ det(Q_bQ_bᵀ)^(-a/2)·Cresid·Vol · ∫_C frobSq(C·W)^(-q), W := Q_inl(1-proj).
(S4) The resulting BOX integral is ∫_{z,Acor,C} det((Acor·Z_deep)(Acor·Z_deep)ᵀ)^(-a/2)·frobSq(C·W)^(-q),
     with W = Q_inl(z)·(1-proj(z,Acor)) the TRANSVERSE PIVOT part — which is NOT the deep factor Z_deep
     that appears in the charge. schurB's ChargedRectSchurCore requires loss-S = charge-S (same S).
</task>

<output_contract>
Four sections, terse:
1. VERDICT on S1 (projector kills Q_inr): SOUND / FLAWED + one-line why.
2. VERDICT on S2 (drop E_top for an UPPER bound on finiteness): SOUND / FLAWED. In particular is
   dropping E_top safe for FINITENESS, or does it destroy convergence (make ∫_x E_tr^(-q) DIVERGE where
   ∫(E_top+E_tr)^(-q) converged)? This is the crux — answer directly.
3. VERDICT on S4 (loss-model mismatch): is the transverse-pivot loss frobSq(C·W), W=Q_inl(1-proj),
   genuinely a DIFFERENT integrand than schurB's frobSq(Δ·Z_deep) (charge-tied S)? Does that block using
   schurB's ChargedRectSchurCore, or is there a clean reconciliation (e.g. W absorbs into a change of
   variables / W and Z_deep have matching rank so the frobSq-integral thresholds coincide)?
4. BOTTOM LINE: is the bridge "frontCharge ≤ Cresid·Vol·[charge]·[single-frobSq C-integral]" a SOUND
   pointwise inequality I can formalize now (yes/no), and is the loss-model mismatch (S4) the real
   remaining architectural question (yes/no)?
</output_contract>

<grounding_rules>
Pure linear algebra + measure theory. Flag any step where you're inferring vs certain. If S2's drop-E_top
is the failure mode (E_tr can vanish on a LARGER set than E_top+E_tr, breaking integrability), say so
explicitly and rank whether keeping E_top is necessary. Do not assume the interior rank regime a+b ≤ ρ
unless you invoke it explicitly to make a threshold work.
</grounding_rules>
