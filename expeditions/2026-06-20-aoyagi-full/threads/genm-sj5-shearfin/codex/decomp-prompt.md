# Cleanest sound decomposition of a matrix-RLCT finiteness (full-box, rank-drop present)

You are a decorrelated second opinion / red-team for a Lean-4 (Mathlib) formalisation. I want
(1) the threshold arithmetic double-checked, and (2) the CLEANEST decomposition into sub-lemmas so I
can prove the reachable ones and isolate the one genuine analytic wall behind a correct statement.
Exact RLCT / integrability reasoning. Answer crisply. Withhold nothing; correct me if I'm wrong.

## The integral (the target `pivotDomLHS_full < ⊤`)

Fix natural numbers `u ≥ 1`, `a := M0 − u ≥ 0`, `b := M1 − u ≥ 0`, `n` (deep column count, large),
`m` with `a + b ≤ m ≤ n`. Real `c' ≥ 0`. All boxes are `[−1,1]`-cubes ("matBox"/"genBox"/"blockbox").

Objects (per fixed deep parameter `z` and corank selector `A_cor`):
- `Z := Zf z : n_rows × n` real (the "deep factor"), with a Loewner floor (hypothesis `hfloor`):
  `Z Zᵀ ⪰ ε'² · (U Uᵀ)` where `U : n_rows × m`, `Uᵀ U = 1` (orthonormal m-frame), `ε' > 0`,
  and `m ≤ rank Z`. So `Z` has `m` singular values `≥ ε'`.  (n_rows = deep row count ≥ m.)
- `Q_p : u × n` pivot rows (from a separate parameter `z`, generically full row rank u; NOT A_cor-dependent).
- `Q_b := A_cor · Z : b × n` corank rows (`A_cor : b × n_rows`, ranges over the FULL box `[−1,1]^{b·n_rows}`).
- `hsQ := [Q_p ; Q_b] : (u+b) × n` (stacked).
- Front block `B = [[P, B12],[C, D]] : (u+a) × (u+b)`, `P : u×u` required invertible (`IsUnit`),
  `B12: u×b`, `C: a×u`, `D: a×b`; `B` ranges over the block cube `[−1,1]^{(u+a)(u+b)}` ∩ {P invertible}.
- Loss `L(B, z, A_cor) = frobSq(B · hsQ) = tr(B (hsQ hsQᵀ) Bᵀ)`  (squared Frobenius, degree-2 in B).

The integral (z over a fixed box, finite volume):
```
I(c') = ∫_z ∫_{A_cor ∈ box}  [ ∫_{B ∈ blockcube, P invertible}  L(B,z,A_cor)^{−c'}  dB ]  dA_cor  dz.
```
We must show `I(c') < ⊤` under `2c' < minAdm + a·b`, where `minAdm ≥ 1` is a fixed nat (the reduced-chain
minimal admissible codimension) with the KEY structural gate available as a hypothesis
`hpiv : minAdm ≤ u · tailMinWidth ≤ u · M1 = u·(u+b)`; and I can derive `minAdm + a·b ≤ (u+a)(u+b)`.

## The three DECORRELATED design confirmations (already banked)

Threshold `λ_full = (minAdm + a·b)/2` (the COMPARATOR threshold), STRICTLY below the full-block-dimension
threshold `(u+a)(u+b)/2`. Worked anchor (all dims 3, u=2, a=b=1): `minAdm = 6`, `a·b=1`, `λ_full=3.5`;
the full-block threshold is `4.5`. The rank-drop locus `{A_cor : Q_b ∈ rowspace(Q_p)}` (codim-1 in A_cor)
lowers `4.5→3.5`. Route named "unit-Jacobian column-shear normal form": choose invertible `R` on the n
columns with `Q_p R = [I|0]`, `Q_b R = (…, s)`; then `L ≍ |x|² + s²|y|²` (x strong, y weak, s transverse),
`σ_min(hsQ) ≍ |s|`; inner B-integral `≍ g^{−max(c'−m0/2,0)}` (`g=σ_min²≍s²`, `m0` = strong dim); outer
transverse `∫|s|^{−2(c'−m0/2)} ds` converges iff `c' < m0/2 + 1/2`. In the anchor `m0=6`, `+1/2 = a·b/2`.

## Banked Lean lemmas I can reuse (verbatim signatures)

- `blockFront_rowSplit`: `frobSq(fromBlocks P B12 C D · Q) = frobSq(P·Q_p + B12·Q_b) + frobSq(C·Q_p + D·Q_b)`
  where `Q_p = Q.submatrix inl id`, `Q_b = Q.submatrix inr id`. (pivot/corank row split.)
- `corankBlock_morsePeel_setLE` (per fixed `Qb` with `Qb Qbᵀ` PosDef, any pivot weight `w>0`,
  `ab/2 < c'`, any set s):
  `∫_{Γ∈s} (w + frobSq(Apiv) + frobSq(Ccross + Γ·Qb))^{−c'}`
    `≤ ofReal( det(Qb Qbᵀ)^{−a/2} · Cresid(ab,c') · (w + frobSq Apiv + frobSq(Ccross·(1 − Qbᵀ(Qb Qbᵀ)⁻¹Qb)))^{−(c'−ab/2)} )`.
  (Peels the D/Γ block, charges ab/2 as a det-Gram divisor + shifts exponent. Here Γ = the D block,
  Qb = A_cor·Z, Apiv=0, Ccross = C·Q_p.)
- `shell_corankOffSector_le_unif` (integrates A_cor over the FULL box, uses the deep floor `hfloor`,
  needs `ab/2 < c'`, `b≤m≤rank`, `a < m−b+1`): for any `w>0`, any `Ccross`,
  `∫_{A_cor∈box}∫_{Γ∈s} (w + frobSq(Ccross+Γ·(A_cor·Z)))^{−c'} ≤ Cunif · w^{−(c'−ab/2)}`,
  `Cunif` free of `Z, Ccross, w` (reads only ε', dims). [This ALREADY handles the corank block over the
  full A_cor box via the deep floor — det-Gram divisor integrated to a uniform constant.]
- `detGram_lintegral_box_lt_top`: `∫_{X∈matBox r n T} det(X Xᵀ)^{−a/2} < ⊤` for `a < n−r+1`.
- `matBox_frobSq_neg_lintegral_lt_top`: `∫_{matBox p q 1} frobSq(X)^{−c'} < ⊤` for `0<c'<pq/2`.
- The shell version `pivotPeel_domination` is ALREADY sorry-free: on the pivotShell
  `{σ_min(hsQ) ≥ ε}`, `∫_B L^{−c'} ≤ ε^{−2c'}·∫frobSq(B)^{−c'}`, finite for `c' < (u+a)(u+b)/2` — the CRUDE
  whole-block Loewner floor. This does NOT transfer to the full box (floor fails off-shell).
- Ratio-trick + comparator side already give: RHS-finiteness ⟺ `2c' < minAdm + ab` (so I get `hcrit`
  as a hypothesis), and I must produce `I(c') < ⊤`.

CRITICAL: `shell_corankOffSector_le_unif` requires the pivot weight `w` to be A_cor-FREE. In the row-split
the corank energy is `frobSq(C·Q_p + D·Q_b)` and the pivot energy `w = frobSq(P·Q_p + B12·Q_b)` DEPENDS on
A_cor (via Q_b = A_cor·Z). So I cannot directly apply it with `w = w(A_cor)`. There is a variant
`shell_corankPivot_coupled_le` that leaves `w(A_cor)` COUPLED inside the A_cor integral (RHS still has
`∫_{A_cor} det-Gram^{−a/2} · (w(A_cor)+resid)^{−(c'−ab/2)}`).

## My precise questions

Q1. **Threshold, general (u,a,b):** confirm `λ_full = (minAdm + a·b)/2` and identify the "strong dimension"
    `m0` in the normal form for general (u,a,b). Is `m0 = (u+a)(u+b−1)` (so the transverse block is the
    single last column, dimension `u+a`, giving a codim-`(u+a)` weak block but a 1-parameter `s`)? Or does
    the transverse charge `a·b/2` come from `b` independent small singular values (one per corank row),
    i.e. `b` transverse directions each charged `a/2`? Reconcile the "`+a·b/2`" with the anchor "`+1/2`"
    (where `ab=1`). Which is right, and does `minAdm = m0` in general or only in the anchor?

Q2. **The coupling (the crux):** after the corank peel, the residual is
    `∫_z ∫_{P,B12,C (P inv)} ∫_{A_cor} det(Q_b Q_bᵀ)^{−a/2}·(w(A_cor)+resid)^{−(c'−ab/2)}` (schematically).
    The pen-and-paper cert claims: `w = frobSq(P·Q_p + B12·A_cor·Z)` does NOT vanish as A_cor→rank-drop
    (there `w → frobSq(P·Q_p) > 0` for invertible P), so `{w=0}` is DISJOINT from `{det Q_bQ_bᵀ = 0}`; the
    det-Gram divisor is integrable over A_cor via the deep floor alone; and the pivot charge `minAdm/... `
    comes from the SEPARATE P-radial integral `∫_{P,B12} w^{−(c'−ab/2)}`. Is this decoupling SOUND for the
    UPPER bound (finiteness)? Concretely: is it valid to bound
    `(w(A_cor)+resid)^{−(c'−ab/2)} ≤ w(A_cor)^{−(c'−ab/2)}` (drop resid, valid since exponent ≤ 0 and
    resid ≥ 0), then Tonelli-separate `∫_{A_cor} det-Gram^{−a/2}` (finite, deep floor) from
    `∫_{P,B12,C} w^{−(c'−ab/2)}`? The obstruction: `w` depends on BOTH A_cor and (P,B12), so it does NOT
    factor out of the A_cor integral. How is the coupling actually dissolved for a rigorous UPPER bound?
    Is the honest move to bound `w(A_cor) ≥ (something A_cor-free and positive)` — and if so, what, given
    that `w` genuinely can be small for some (P,B12,A_cor)?

Q3. **Reachability / the wall:** given the banked lemmas, what is the SMALLEST irreducible new analytic
    lemma (the "wall")? Candidates: (i) the generalized quadratic-form monomial integral
    `∫_{cube} tr(B G Bᵀ)^{−c'} dB ≍ (∏ small eigenvalues of G)^{−(c'−m0/2)}` as a function of the spectrum
    of G (the "column-shear normal form" — a spectral CoV); (ii) the pivot P-radial charge
    `∫_{P,B12,C} frobSq(P·Q_p + B12·Q_b)^{−(c'−ab/2)} ≤ C·comparator` (the couplingfin `headSplit_pivotDom`,
    minAdm capacity via P-radial blow-up). Which is the genuine wall, and is either reducible to a banked
    piece? Give the cleanest chain `pivotDomLHS_full_lt_top ⟸ [reachable steps] + [ONE wall lemma L*]`,
    stating L* precisely.

Q4. **Shorter honest route?** Is there any decomposition that AVOIDS the spectral CoV — e.g. splitting the
    A_cor box into `{σ_min(hsQ) ≥ ε}` (shell, done by `pivotPeel_domination`) ⊔ `{σ_min < ε}` (off-shell),
    and bounding the off-shell part by the corank peel + a crude pivot bound — that reaches `λ_full` without
    a full spectral normal form? Or is the spectral/shear CoV genuinely irreducible? If irreducible, say so
    plainly (I will isolate it behind a correct statement, NOT launder it).

Answer with: Q1 value + m0 formula; Q2 soundness verdict (+ the correct decoupling move); Q3 the single
wall lemma L* stated precisely; Q4 shorter-route verdict.
