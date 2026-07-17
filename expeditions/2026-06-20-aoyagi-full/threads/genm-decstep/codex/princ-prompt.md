<task>
Design/verify the exceptional-power budget of a c×c joint log-resolution (principalization) step in an
RLCT induction. Deep-linear-network Frobenius loss; the arithmetic budget is given/verified, the question
is the ANALYTIC normal form and whether its exceptional powers reach the threshold.

SETUP. Square chain (n,n,n,n), box integral I(c') = ∫ frobSq(P Z0 W)^{-c'}, threshold c* =
(1/2)minAdm(n,n,n,n). Peel the first layer at the binding cut t* (invertible t*×t* pivot); corank
c = n−t* = ceil(n/3) (so c≥2 for n≥4). After a measure-preserving Schur weld, on the invertible-pivot
chart the loss is frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Q_b), with C (a×t*) and Γ (a×b) the FREE coupling and
corank blocks (a=b=c), Q̃ₚ (t*×q) the pivot tail (full row rank u=t* generically), Q_b (c×q) the corank
tail. Q̃ₚ and Q_b are built from the deeper layer variables; the reduced chain is (t*, n, n).

BANKED (exact lemmas, may cite):
  (i) gammaAtom: for R full row rank (R Rᵀ posdef), any shift S, c' > pq/2, w>0:
      ∫_Γ (w + ‖Γ·R + S‖²)^{-c'} dΓ = det(R Rᵀ)^{-p/2} · Cresid · (w + ‖S·(I − P_R)‖²)^{-(c'−pq/2)},
      P_R = Rᵀ(R Rᵀ)⁻¹R the row-space projector.  [general p,q — NOT just rank-1 S]
  (ii) qbox (Wishart): ∫_{X box, m×q} det(X Xᵀ)^{-s} dX < ∞  iff  2s < q − m + 1.
  (iii) the plain / decorated arity box-finiteness IH for any shorter chain.

THE STEP (my proposed decomposition — verify or correct it).
  1. Integrate the coupling block C via gammaAtom (R=Q̃ₚ, S=Γ·Q_b, p=a, q=u): yields the PIVOT Gram
     det(Q̃ₚ Q̃ₚᵀ)^{-a/2} (full row rank u — SAFE) times the residual (w + ‖(Γ·Q_b)·(I − P_{Q̃ₚ})‖²)^{-(c'−au/2)}.
     Write Q_b^perp := Q_b·(I − P_{Q̃ₚ}) (the corank tail projected OFF the pivot row space).
  2. The PIVOT Gram det(Q̃ₚ Q̃ₚᵀ)^{-a/2} is carried as a DECORATION and disposed by qbox (per level) +
     the reduced-chain recursion when qbox is marginal (a = q−u+1). It is NOT the corank Gram det(Q_b Q_bᵀ)
     (which would be the divergent "trap": at edge dims a<q−b+1 is a<a=FALSE).
  3. The residual frobSq(Γ·Q_b^perp), with Γ STILL FREE (c×c), is treated as the reduced chain
     (t*,n,n)'s loss (Γ its free leading layer, Q_b^perp its deeper tail), closed by the decorated
     arity-IH. We do NOT integrate Γ via a second gammaAtom (that would produce the corank Gram
     det(Q_b^perp Q_b^perpᵀ)^{-c/2} = the trap).

  Q1. Is frobSq(Γ·Q_b^perp) [Γ free c×c, Q_b^perp = Q_b·(I − P_{Q̃ₚ}) the pivot-rowspace-projected corank
      tail] a CLEAN reduced-chain (□)-instance — i.e. is Q_b^perp a genuine layer-product so the reduced
      object is a bona fide DLN box integral the arity-IH closes — OR does the projector (I − P_{Q̃ₚ}),
      which couples the corank tail to the pivot, BREAK the chain structure, so that frobSq(Γ·Q_b^perp)
      is a genuinely coupled (Γ, pivot, deeper) determinantal incidence needing its own bespoke resolution?

  Q2. The exceptional-power budget (the crux). After the FULL resolution (C-integration → pivot Gram
      via qbox → residual to the reduced-chain recursion), do the accumulated exceptional powers give
      RLCT ≥ c*? Concretely: the C-integration spends au/2; the pivot Gram is qbox-integrable iff
      a < q − u + 1; the reduced chain contributes (1/2)minAdm(t*,n,n). Show whether
      au/2 + [pivot-Gram charge] + (1/2)minAdm(t*,n,n) ≥ c* = c²/2 + (1/2)minAdm(t*,n,n), i.e. whether
      the corank+coupling blocks together spend exactly c²/2, with the pivot-Gram exceptional powers
      NONNEGATIVE (the a_i − 2c'·N_i > −1 sign holding up to the threshold). Give the arithmetic for
      n=4 (t*=2, a=b=c=2, u=2, q=?). If a piece has a NEGATIVE net exceptional power (sign fails), say
      where.

  Q3. Is the qbox gate a < q − u + 1 satisfiable at the c≥2 binding cut, or is it violated (forcing the
      pivot-Gram recursion / D-cert §3bis marginal fold)? For the pivot tail Q̃ₚ (t*×q), what is the
      effective q (the tail column count) — and does 2c ≤ q−u type gates hold, recurse, or fail?

  Q4. Net: is this decomposition (C-integration → pivot Gram → residual-to-reduced-chain, NO second
      gammaAtom) a SOUND Lean-friendly design for the c≥2 principalization step, with the exceptional
      powers reaching c*? Or is there a genuine gap (then name the minimal missing piece)?
</task>

<output_contract>
Answer Q1-Q4 in order, short paragraphs. Q1 (chain-clean vs coupled-incidence) and Q2 (the exceptional-
power sign/budget) are load-bearing. For Q2 SHOW the n=4 arithmetic. Flag PROVEN (from the banked lemmas +
arithmetic) vs INFERENCE. End with a one-line verdict:
SOUND-DECOMPOSITION / GAP-AT-<piece> / SIGN-FAILS-AT-<n,piece>.
I have withheld my own tentative verdict; do not assume it.
</output_contract>

<grounding_rules>
The load-bearing crux: (a) whether the pivot-rowspace projection breaks the reduced chain into a coupled
incidence (Q1), and (b) the SIGN of the net exceptional powers a_i − 2c'·N_i in the monomial normal form
(Q2) — whether they stay above the threshold. Distinguish the exact-arithmetic budget (given: min over
strata = minAdm) from the analytic normal-form claim. State the Wishart/qbox exponent you use. Do not
paste Lean or long code.
</grounding_rules>
