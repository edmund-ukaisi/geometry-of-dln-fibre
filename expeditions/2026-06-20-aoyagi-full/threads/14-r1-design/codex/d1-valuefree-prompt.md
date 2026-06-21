<task>
Adjudicate ONE truth-value with exact reasoning. Do NOT write or run code. Reason on paper.

SETTING. Deep-linear-network square loss. Widths H:{0,...,L}->N, layer s is a matrix A^(s) of size
H^s x H^{s+1}. prod(A) = A^(1)...A^(L). Loss F(A) = ||prod(A) - B||^2_Frobenius (sum of squared entries).
Fibre = optimalSet = {A : prod(A)=B}, the zero-set of F. Fix B of rank r.

We have a real log canonical threshold (RLCT) lambda_w*(G) = local learning coefficient of G at w*
(sSup of exponents c with |G|^{-c} locally integrable near w*). We have, PROVEN and green in Lean:
- rlctAt_mono: if on a nbhd of w*, |G|<=|F| and (G=0 => F=0), then lambda_w*(G) <= lambda_w*(F).
  (This is EXACTLY Aoyagi 2013 Entropy Lemma 1(1): g^2<=f^2 => lambda(g^2)<=lambda(f^2), SAME point w*.)
- S1: RLCT invariance under analytic changes of variable / blow-ups (the change-of-variables substrate).
- "deepestPoint": a constructed fibre point with every layer A^(s) at rank exactly r (all partial
  products at minimal rank). The core generators (entries of the reduced product after the rank-r split)
  are HOMOGENEOUS (multilinear, degree L) in the layer variables -- verified symbolically.

THE LEMMA WE WANT (call it D1>=): for EVERY fibre point v (prod(v)=B),
        lambda_deepest(F) <= lambda_v(F).
(Then the fibre-infimum of the local RLCT is attained at deepestPoint.) This is Aoyagi 2013 Theorem 2
("method for finding a deepest singular point"), whose proof: blow up w_i = t w_i' along the core
directions; homogeneity gives f_i(tw')=t^{n_i}f_i(w'); then Sum t^{2n_i} f_i'^2 <= Sum f_i'^2 for |t|<1;
then Lemma 1(1). Aoyagi also gives Example 3: D1>= is FALSE for a general critical point lacking the
homogeneity (x(x-1)^2 etc.) -- so homogeneity is essential.

There is a SEPARATE, much heavier result in this project, R1 ("the resolution"): an explicit chart family
giving rlctAtOn(core) 0 = inf_i monomialThreshold(d_i,k_i,h_i), i.e. the VALUE of the core RLCT equals
Aoyagi's closed form lambdaCore = (1/2) min_{T in Adm} Mval. R1 is the singular-resolution VALUE
computation. It is a big separate rung.

FACTS I have established by exact symbolic computation (sympy, generic entries):
- (2,1,2) r=0: core F=(a0^2+a1^2)(b0^2+b1^2). Scaling all 4 core vars by t: F(t.)=t^4 F. So
  Sum t^{2n_i}f_i^2 = t^4 F <= F for |t|<1. The blow-up inequality is PURE homogeneity, no value.
- (2,2,2) r=0, deepest=origin, lambda_deepest=3/2 (known). A non-deepest fibre point v (A^(1),A^(2) each
  rank 1 with product 0): the generator-map Jacobian at v has rank 3 => 3 nondegenerate quadratic
  ("regular") directions, each contributing 1/2, plus a HIGHER-ORDER residual generator. So the loss germ
  at v splits as [nondegenerate quadratic block, dim 3] + [homogeneous residual core], giving
  lambda_v = 3/2 + lambda(residual) > 3/2 = lambda_deepest. The deepest is STRICTLY minimal.
</task>

<sub_question>
Is the two-point domination D1>= (lambda_deepest <= lambda_v for every fibre point v) provable from:
  (i)   the EXISTENCE of a homogeneous normal form / local split at each fibre point v
        (loss germ = nondegenerate-quadratic regular block + homogeneous residual core),
  (ii)  the homogeneous scaling inequality Sum t^{2n_i} f_i'^2 <= Sum f_i'^2 (|t|<1),
  (iii) rlctAt_mono (= Lemma 1(1)), and
  (iv)  S1 change-of-variables RLCT-invariance,
WITHOUT ever invoking R1's resolution VALUE (the equality rlctAtOn(core)=inf monomialThreshold=lambdaCore)?

In particular:
(A) Does Aoyagi's Thm 2 proof, as a route to D1>=, use the VALUE of any RLCT, or only the SCALING
    inequality + the same-point monotonicity lemma? Be precise about every step.
(B) The structural concern: at a NON-deepest fibre point v the core generators are NOT homogeneous in the
    local coordinates (they have a nonzero LINEAR leading part -- v is a smooth point in those directions).
    Aoyagi's Thm 2 literally requires the f_i homogeneous. How does the reduction handle a non-deepest v?
    Does casting v's loss germ into [regular block + homogeneous residual] require R1's resolution value,
    or just a local Morse/implicit-function split + the homogeneity of the residual core?
(C) Does the "covers all fibre strata + deepest in each stratum's specialization closure" obligation
    (needed so the SAME deepest point dominates every v) require the resolution value, or is it a
    statement about the fibre stratification only (rank patterns), independent of any RLCT value?
(D) If you think it is NOT value-free, exhibit the precise dependence on the value (which step fails
    without it). If value-free, give the cleanest decomposition of D1>= into the green primitives above.
</sub_question>

<output_contract>
- A single verdict line: VALUE-FREE or VALUE-DEPENDENT (or VALUE-FREE-EXCEPT-<named gap>).
- A step-by-step of Aoyagi Thm 2's proof labelling each step PURE-ALGEBRA / SAME-POINT-MONOTONICITY /
  CHANGE-OF-VARIABLES / USES-VALUE.
- An explicit answer to (B): the mechanism that handles a non-deepest v (regular split + residual), and
  whether it needs the value.
- An explicit answer to (C): is the strata-coverage obligation value-free?
- Distinguish FACT (what the cited proof establishes) from INFERENCE (your assessment of value-freeness).
</output_contract>

<grounding_rules>
- Ground strictly in the facts above + standard RLCT/singular-learning theory (Watanabe, Aoyagi 2013, Lin).
- Reason on paper ONLY. Do NOT attempt to read files, run shell commands, or execute code.
- Preserve the FACT vs INFERENCE distinction. If a claim needs a hypothesis, name it.
- "Value" means specifically the equality rlctAtOn(core)=inf monomialThreshold=lambdaCore (R1's output).
  A SCALING inequality or a Jacobian-rank count is NOT "the value".
</grounding_rules>

<important>
You have NO file, shell, or code access in this task. Do not call any tool. Produce only the reasoned
adjudication as text. Any attempt to read the project or a PDF will fail; rely solely on the facts given.
</important>
