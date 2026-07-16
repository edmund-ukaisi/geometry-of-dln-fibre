# Reconcile: is a matrix RLCT bound valid over the FULL box, or only on a "shell"?

You are a decorrelated second opinion. I am withholding my conclusion. Argue whichever
direction the mathematics supports and give a crisp verdict. Exact algebra / RLCT
(learning-coefficient) reasoning; a Monte-Carlo sublevel-volume estimate is only a guide.

## Concrete objects (a worked anchor: dims all = 3)
Fix generic real matrices, well-conditioned:
- `Z` : 3x3 invertible (a "deep factor"), with σ_min(Z) ≥ some floor > 0.
- `Q_p` = `z0 · Z` where `z0` is 2x3 generic  ⇒ `Q_p` is 2x3 of rank 2.
Variables (all ranging over the cube `[-1,1]^(entries)`, i.e. bounded boxes, plus one is
required invertible):
- `T` : the full 3x3 front block  (think `T = [[P, B12],[C, D]]`, `P` the 2x2 top-left,
  required invertible; but for integrability near the singular locus treat `T` as ranging
  over a full 3x3 box).
- `A` : 1x3   ("corank rows selector").
Derived:
- `Q_b = A · Z`  (1x3),   `hsQ = [Q_p ; Q_b]`  (3x3, rows = 2 pivot + 1 corank).
- Loss  `L(T, A) = ‖ T · hsQ ‖_F^2`   (squared Frobenius; degree-2 homogeneous in T).

## The integral in question
`I(c) = ∫_{A ∈ box} ∫_{T ∈ box}  L(T,A)^{-c}  dT dA`   (c > 0).
Define `λ_full = sup{ c : I(c) < ∞ }` (the RLCT / integrability threshold over the FULL A-box).

There is a competing "shell-restricted" integral where `A` is confined so that
`σ_min(hsQ) ≥ ε` (equivalently, `[Q_p ; Q_b]` stays uniformly full rank 3):
`I_shell(c) = ∫_{A : σ_min(hsQ)≥ε} ∫_{T∈box} L(T,A)^{-c} dT dA`,  threshold `λ_shell`.

A separate "comparator" integral (the target upper bound) has integrability threshold
`λ_cmp = (m + a·b)/2` where here `a = b = 1`, `a·b = 1`, and `m := minAdm = 6`, so
`λ_cmp = (6+1)/2 = 3.5`. (You may take `λ_cmp = 3.5` as given.)

## The two claims to arbitrate
- Claim S (a "shell is load-bearing" cert): the pivot/loss bound `∫ L^{-c} ≤ C·comparator`
  holds only when `A` is confined to the shell `σ_min(hsQ) ≥ ε`; over the FULL `A`-box the
  threshold DEGRADES below `λ_cmp` because the locus `{A : Q_b ∈ rowspace(Q_p)}` (⇔ hsQ drops
  to rank 2), which is codimension 1 in `A`, is INCLUDED and is not excluded by the
  well-conditioning of `Z` alone. So `λ_full < λ_cmp = 3.5`, and `∫_{full} L^{-c} = ∞` for
  `c ∈ (λ_full, 3.5)` while the comparator is finite ⇒ the full-box bound is FALSE.
- Claim F (a "deep floor suffices" cert): the well-conditioning of `Z` (a Loewner floor
  `Z Zᵀ ⪰ ε'²·I`) is enough to make `∫_{full box} L^{-c} ≤ C·comparator` hold for all
  `c < 3.5`; i.e. `λ_full = 3.5`, no shell restriction on `A` needed.

## Precise questions
1. Compute (or tightly estimate) `λ_full`. In particular: near the rank-drop locus
   `{σ_min(hsQ) → 0}` (codim 1 in A), what is the asymptotics of the inner T-integral
   `J(A) := ∫_{T∈box} L(T,A)^{-c} dT` as `g := σ_min(hsQ)² → 0`? i.e. find β(c) with
   `J(A) ~ g^{-β(c)}`. Does `σ_min(hsQ)` vanish LINEARLY in the transverse A-coordinate
   (so `g ~ s²`)? Then the outer integral `∫ J(A) dA ~ ∫ s^{-2β} ds` (1-dim transverse)
   converges iff `2β < 1`. State the resulting `λ_full` and whether `λ_full < 3.5` or `= 3.5`.
2. KEY: at the rank-2 locus the T-integral is a 9-dim quadratic-form integral where hsQ hsQᵀ
   has one zero eigenvalue (a weak direction seen by all 3 rows of T). Is the excess exponent
   charged to that weak block enough to keep the OUTER A-integral finite up to `c = 3.5`, or
   does it diverge earlier? Be careful whether the corank rows of T (the C,D block) contribute
   to the same rank drop as the pivot rows (P,B12) — i.e. is the full 3x3 T-integral threshold
   the naive "pivot-only threshold + a·b/2", or larger because all rows jointly see the drop?
3. Verdict: is Claim S or Claim F correct for this anchor? If `λ_full < 3.5`, give the value
   and the c-window where the full-box bound is FALSE. If `λ_full = 3.5`, explain why the
   codim-1 rank-drop locus does NOT degrade the threshold.

Answer with: the value of `λ_full`, the T-integral scaling `β(c)`, and a one-line VERDICT
(Claim S / Claim F / other), plus the single most likely error in the losing claim.
