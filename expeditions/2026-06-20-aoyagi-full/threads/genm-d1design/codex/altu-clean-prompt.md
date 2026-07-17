<task>
Adjudicate ONE soundness question for a Lean formalisation (Lehalleur–Rimanyi DLN): is a corank-one integral
CLEAN (reduces to plain undecorated box-finiteness) or does it carry a Gram DECORATION? I withhold my leaning.
WITHHOLD nothing.

SETUP (exact). frobSq(X)=sum of squared entries. Plain hIH = box-finiteness of any SHORTER chain:
INT_{layers in [-1,1] box} frobSq(prod)^{-c'} < inf for c' < minAdm/2. A "decoration" = a leftover weight
det(GG^T)^{-w} with G a deeper PRODUCT on the reduced box — PROVEN NOT absorbable by plain hIH (diverges near
a nonzero rank-deficient G). "Clean" = reduces to plain hIH + finite banked factors, NO product-Gram weight.

THE ARM (d=1, corank-one, b=1, a<u=t). Variables integrated: P (u×u, INVERTIBLE box), B12 (u×1, free box),
C (a×u, free box), gamma (a-vector, free box), and A' (the deeper tail params, free box). Derived:
  Q = tail product (rows indexed, q=M_last cols); Q_p = top u rows (u×q); Q_b = bottom row (1×q). BOTH products.
  Qtil = Q_p + P^{-1} B12 Q_b   (u×q, the pivot-shifted tail).
  W = frobSq(P·Qtil) = frobSq([P|B12]·Q)  (the pivot energy; NOTE depends on B12).
  omega = Q_b/||Q_b|| (unit q-vector), sigma = ||Q_b||, v = Qtil·omega^T (u-vector).
KEY ALGEBRA (verify): v = Qtil·omega^T = Q_p·omega^T + P^{-1}B12·(Q_b·omega^T) = Q_p·omega^T + sigma·P^{-1}B12.
So v = c0 + sigma·(P^{-1}B12), c0 = Q_p·omega^T FIXED (given P,A'); B12 FREE ⟹ P^{-1}B12 ranges over R^u ⟹
v ranges over R^u (an affine shift by the free B12). CRUCIAL: B12 appears in BOTH v AND W (via Qtil).

The corank-one a<u reduction (after dropping the transverse term ≥0, and integrating C, gamma via the BANKED
edge lemma edge_C_shift_bound): the C-integral is bounded by
  INT_C (W + ||C·v + beta||^2)^{-c'} dC  ≤  2^{au}·|v_{j0}|^{-a} · INT_{R^a}(W+||x||^2)^{-c'} dx
  = 2^{au}·|v_{j0}|^{-a} · B_a · W^{a/2 - c'}   (c' > a/2; |v_{j0}| = max_j |v_j| = ||v||_inf),
beta = sigma·gamma (β-INVARIANT). So after (C,gamma) the residual over (P,B12,A') is
  K · |v_{j0}|^{-a} · W^{a/2 - c'}      [K a banked constant].
The claim to be built: this reduces to plain frontCollapse(X=[P|B12], reducing W=frobSq(X·Q) to hIH of the
shorter chain redChain u M) at exponent c'-a/2, with NO leftover Gram decoration. Charge: peelCharge(u)=a·b=a
(b=1), and cut-soundness gives c'-a/2 < minAdm(redChain u M)/2 (transfers). frontCollapse itself is clean
(bounded-w M2<=b: a free-front det(XX^T)-qbox × hIH).

THE QUESTION (load-bearing). Is  INT_{(P,B12,A')} |v_{j0}|^{-a} · W^{a/2-c'}  reducible to plain
frontCollapse(X)+hIH (bounded plumbing, NO product-Gram), given that B12 appears in BOTH |v_{j0}|^{-a} AND W?
Consider these sub-questions:
(a) The |v_{j0}|^{-a} disposal: integrating over the FREE B12 (v = c0 + sigma·P^{-1}B12), does
    INT_{B12 box}|v_{j0}|^{-a} dB12 factor cleanly? Via CoV B12↦v (Jacobian sigma^{-u}|det P|), it becomes
    sigma^{-u}|det P|·INT_{v-box}||v||_inf^{-a} dv, and INT_{R^u}||v||^{-a} (u-dim ball) converges iff a<u.
    But W = frobSq(P·Qtil) ALSO depends on B12 (Qtil = Q_p+P^{-1}B12 Q_b) — so B12 canNOT be disposed for
    |v|^{-a} independently of W. Does the JOINT (B12 in both) integral still factor, or does the coupling
    produce a residual conditioning weight (e.g. sigma^{-u}=||Q_b||^{-u}, or a Gram of Qtil / of the product Q_b)?
(b) If a sigma^{-u}=||Q_b||^{-u} factor appears (Q_b a PRODUCT row), is INT_{A'}||Q_b||^{-u}·[reduced] clean
    (Q_b→0 is a separate corner) or a decoration? Recall Q_b is a deeper product row, not a free box.
(c) NET: is d1-a<u bounded-w genuinely CLEAN-plain-hIH, or does it secretly carry a decoration (a product-Gram
    / ||Q_b||^{-u} / conditioning weight) — i.e. is it actually in the SAME decorated class as b=0 and d1-a≥u,
    NOT a clean arm? If clean, give the exact factorization + which banked lemmas dispose each factor. If
    decorated, name the exact leftover weight and the smallest cell exhibiting it.
</task>

<output_contract>
  Sections (a),(b),(c). PROVEN/ARGUED/GUESS per claim. (c) one-line VERDICT {CLEAN-PLAIN-HIH / DECORATED /
  MIXED}. If DECORATED or MIXED, name the exact leftover weight + smallest cell. If CLEAN, the exact
  factorization (which factor each banked lemma disposes: edge_C_shift_bound, scaledRadialEuclid, a qbox for
  ||Q_b||^{-u} if present, frontCollapse, hIH) + confirm no product-Gram survives. End with the cheapest
  discriminating computation. Concrete dims/charges; no hedging.
</output_contract>

<grounding_rules>
  B12 is a genuine FREE variable shared between v and W; do not assume it can be disposed twice. A factor
  ||Q_b||^{-u} with Q_b a product row, or det(Qtil Qtil^T)^{-w}, on the reduced box, is a DECORATION unless
  disposed by a FREE-box qbox at a single level or provably bounded. State inference vs fact; do not
  rubber-stamp CLEAN — if the B12 coupling leaves a conditioning weight, say DECORATED.
</grounding_rules>
