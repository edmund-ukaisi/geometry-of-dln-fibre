# Certificate — two-block / two-shared-factor diag(b): single chain SURVIVES (pen-and-paper, thread 28)

Pen-and-paper `pnp-twoblock` (2026-07-20), dispatched INDEPENDENT of thread-27 to stress-test its
"single dominant monomial / single divisibility chain" result at the flagged breaking-point: an
**L≥4 coupled binder with TWO INDEPENDENT shared deep factors**. All load-bearing results exact
(sympy Gröbner over ℚ; exact-rational divisor ratios). Decorrelated-confirmed by an independent
Codex `xhigh` consult (`./codex/twoblock-{prompt,answer}.md`) that reached the same verdict by its
own route. Batteries (alongside the thread-27 ones):
`theory/aoyagi-2023-reproduction/{g-coupled-444-twoblock,g-coupled-33322-separated,g-twoblock-census}.py`
(all EXIT 0), reusing `_rlct_lp.py` and the verified `g-coupled-224-heart.py` mechanism.

## VERDICT — the single divisibility chain SURVIVES (`⟨∏C⟩` stays principal per resolution chart)

Two independent shared deep factors do **not** produce two incomparable binding divisors. They
contribute their exceptional radials as **factors of the single dominant monomial `b₁`** (all
dividing `b₁`), never as incomparable generators of a non-principal ideal. So Object B's general-L
statement is **strengthened, not broken**: in each terminal resolution chart `⟨∏C⟩ = ⟨b₁⟩` is
principal, `b₁ | b₂ | … | b_M` a single chain, and the RLCT read-off is `rlct(b₁²)` — NOT a
genuine multi-generator Newton-polyhedron over incomparable monomials.

Verified EXACTLY at two new kill-instances attacking from both angles, plus a non-monotone check:

### (a) The instances + their exact `diag(b)`

**M=(4,4,4), t=(2,0) — the MINIMAL *uniquely*-binding TWO-corank-2-block instance** (35 such exist
in L=2..5, widths≤7; this is the smallest). `minAdm = min_{t₁}(4−t₁)²+4t₁ = {16,13,12,13,16}`,
unique minimiser t=(2,0), `minAdm=12`, rlct **6**. Blocks on t=(2,0): top `2×2` + deep-layer-2
`2×4` — two corank-2 blocks (vs (3,3,4)'s one corank-2 block + one corank-1 row).
- **Peel** (det-1 block-elim, `C¹=[[I₂,B],[C,D]]`): `Q₁C¹Q₂ = diag(I₂,Δ)`, `Δ=D−CB`; so
  `⟨C¹C²⟩ = ⟨R (2 bare pivot rows, 8 free coords), Δ·S (the (2,2,4)-heart)⟩`. The two census
  "corank-2 blocks" are the **same Δ cascading** (deep block = Δ propagated through C²), NOT two
  independent hearts.
- **Resolve + JOIN**: `R` radial `ρ` (`⟨R⟩=⟨ρ⟩`, Jac `ρ⁷`); `⟨ΔS⟩ = a·⟨σⱼ, e·s2ⱼ⟩` (Gröbner),
  Jac `a³`. Blow up the common corner `{ρ=a=0}`, `ρ=E, a=Eα`: `⟨∏C⟩ = ⟨E, Eα·…⟩ = ⟨E⟩` **principal**
  (Gröbner ideal-equality). Total Jac `E^{7+3+1}=E¹¹`, `loss=E²·unit`, rlct `(11+1)/2 = 6 = ½·12`.
- **`b = (E, Eρ, Eρβν, Eρβνδω)`** (Codex-confirmed 4-chain), `b₁=E` single divisor after the join.

**M=(3,3,3,2,2), t=(2,2,1,0) — the L=4 TWO-SEPARATED-shared-factor kill-instance** (the exact shape
thread-27 flagged). `minAdm=4`, rlct **2**. Two corank-1 scalar couplings: `δ₁` (layer 1, C¹ rank
3→2) and `δ₂` (layer 3, rank 2→1), **separated by a plateau at layer 2** (t₁=t₂=2). `δ₁` shares the
deep product `C³C⁴`; `δ₂` shares `C⁴` — the two independent shared deep factors.
- **Two nested det-1 peels** give `⟨∏C⟩ = ⟨X_row1, δ₂·X_row2, δ₁·X_row3⟩`, `X=C³C⁴` (3×2), row 1 =
  the KEPT (unweighted) rank-survivor.
- Radial the two shared factors `C³=w·C³bar`, `C⁴=y·C⁴bar` (unit pivots): `⟨∏C⟩ = wy·⟨Y_row1,
  δ₂Y_row2, δ₁Y_row3⟩`, `Y=C³bar·C⁴bar`. `Y_row1[0] = 1+pd` is a **local unit** (const term 1) ⟹
  `⟨∏C⟩_local = ⟨wy⟩` **principal**; and `loss = (wy)²·unit` (residual `R(origin)=‖Y_row1‖²=1`).
- **`b₁ = wy`** — a PRODUCT of two divisors `w (C³)`, `y (C⁴)` at different depths, **NOT joined**;
  both divide `b₁`, so still a single dominant monomial. rlct `= ½·min(w-ratio 3, y-ratio 2) = 2`
  (binding = the deepest block `C⁴`; `w` non-binding).

**Non-monotone L=4 sanity** (e.g. (2,3,2,3,2),(3,2,3,2,3),(2,4,2,4,2)): the mechanism is
monotonicity-independent — min-width ≥ 1 always, so a smallest `b₁` (the kept survivor) exists.

### (b) The exact ideal-principality check (done right — NOT sympy `%`)

- (4,4,4): `⟨E, Eασ_j, Eα e s2_j⟩ == ⟨E⟩` verified by **Gröbner ideal-equality** (mutual reduction
  to 0), a global principal ideal (`E` a literal common factor + bare generator from `R`'s unit pivot).
- (3,3,3,2,2): principality is a **local-ring** statement — verified by the residual carrying a
  generator with **nonzero constant term** (`Y_row1[0]=1+pd`, a local unit), equivalently
  `loss=(wy)²·unit` with `R(origin)=1`. (A global Gröbner "1∈ideal" test returns False here and is
  the *wrong* test — `1+pd` is a local, not global, unit.) Anti-check: with all rows δ-weighted
  (no kept survivor) the constant terms vanish and principality would fail — confirming the kept
  unweighted rank-survivor is exactly what supplies the bare `b₁`.

### (c) Not a break — so no multi-generator Newton polyhedron for the read-off

Because the chain survives, the RLCT read-off is `rlct(b₁²) = ½·min over the exceptional divisors
constituting b₁` (their `(Jac+1)/2` ratios) — this **is** Aoyagi's `rlct = ½·min{M_{s,k}: t̃=0}`
(min over the terminal divisors, which are the factors of `b₁`). It is a min over the *factors of a
single monomial*, NOT an LP over incomparable generators. Two honest nuances:
1. **`b₁` may be a product of several divisors at different depths** (`b₁=wy` for (3,3,3,2,2)), so
   the read-off min ranges over `b₁`'s factors — but the ideal is still principal `⟨b₁⟩`.
2. **Intermediate charts CAN be non-principal.** Before the corner-join, (4,4,4)'s ideal is
   `⟨ρ, aσ_j, a e s2_j⟩` (non-principal), and its lct needs the Newton polyhedron; Codex's LP gives
   6, with the minimising ray = the joined divisor `E`. The Newton polyhedron is needed *pre*-join;
   the *terminal* chart is principal. This does not change the deliverable (the terminal form is a chain).

### (d) What this means for Object B's GENERAL statement (for the architect)

- **Blueprint Object B as a SINGLE divisibility chain** `b₁|b₂|…|b_M`, `⟨∏C⟩ = ⟨b₁⟩` principal per
  resolution chart. This is Aoyagi's own inductive invariant (worked.tex:483–484:
  `b_i = (∏_{t̃=i-1} u_{s,k})·b_{i−1}`), and it is now VERIFIED faithful at the two-corank-2-block
  (4,4,4) and the two-separated-shared-factor (3,3,3,2,2) — the cases thread-27 flagged as most
  likely to break it. **Do NOT blueprint B as a multi-generator monomial ideal.**
- **The RLCT read-off is `rlct(b₁²) = ½·min{M_{s,k}}`** (single dominant monomial), NOT a
  Newton-polyhedron LP over incomparable generators. Object C (monomial-ideal RLCT) enters only to
  compute `rlct` of the single monomial `b₁²` (= min over its divisor-factors), a degenerate case.
- **The genuinely load-bearing subtlety is the EXPONENTS, not principality.** Getting the `M_{s,k}`
  (exponents of `b₁`'s divisors) right at corank≥2 requires tracking the symbolic divisor-SUPPORT
  (which shared factors' radials divide which `b_i`), exactly worked.tex:645's `support : Gen →
  Finset DivVar`. A "threshold-only" per-row-multiplicity shortcut gets these WRONG
  (`⟨δx,δy⟩` rlct ½ vs `⟨δ₁x,δ₂y⟩` rlct 1 — worked.tex:616). So: single chain confirmed; the
  exponent bookkeeping carries the shared-support datum.
- **Mechanism (why it never breaks — decorrelated agreement).** The peel recursion is a single
  linear chain (clear one pivot via a `c11=1` unit chart, recurse on ONE Schur complement). A new
  exceptional coordinate at threshold `k` multiplies the SUFFIX `b_{k+1},…` only (Codex's
  suffix-update; Aoyagi's invariant), preserving `b_i | b_{i+1}`. Independent radial scales appear
  transiently but their common-zero corner is blown up, creating a shared PREFIX rather than
  incomparable terminal factors. The kept unweighted rank-survivor always supplies the bare `b₁`.

## Verified vs open (honest scope)

**VERIFIED (exact + Gröbner + decorrelated Codex):** the combinatorial census (minimal
uniquely-binding two-corank-2-block = (4,4,4); the separated two-shared-factor branch structure);
the (4,4,4) join → principal `⟨E⟩`, rlct 6; the (3,3,3,2,2) two-separated-shared-factor →
`⟨wy⟩` principal, rlct 2; principality (local), loss = single-monomial²·unit; the
monotonicity-independence.
**SCOPE / OPEN:** (1) the "**no width vector breaks the chain**" universal is the suffix-update /
kept-survivor **inductive argument** (Codex + Aoyagi's invariant), corroborated by exact instances
{(4,4,4),(3,3,3,2,2),(3,3,4,3,3),(3,3,4),(3,3,2,2),(2,2,4)} — **not** an exhaustive computational
proof over all width vectors. (2) The **tie caveat is closed**: a *uniquely*-binding L=4 separated
two-coupling instance exists — **M=(3,3,4,3,3), t=(2,2,1,0)** (couplings at layers 1 & 3, plateau at
layer 2), unique minimiser, minAdm=6, rlct 3; its layer-1 peel is det-1 and the kept-survivor
mechanism (verified in full symbolic detail at (3,3,3,2,2)/(4,4,4)) applies. Depths of full
verification: (4,4,4) and (3,3,3,2,2) got the **full symbolic resolution + Gröbner/local-unit
principality**; (3,3,4,3,3) got the **peel-structure + uniqueness** check (full resolution follows
the same verified mechanism). (3) `loss ≠ Frobenius` (the peel is ideal- but not norm-preserving), so
the RLCT *equality* needs Lemma 1 / Object A — inherited from thread-27, unchanged. (4) The Lean
rendering of the exponent bookkeeping (support field) is the architect's build, not audited here.

## Most likely thing to break it / next step
The universal is inductive, not exhaustive. The residual risk is a chart where the kept unweighted
rank-survivor is exhausted *before* the deepest layer while two independent divisors remain
incomparable — the suffix-update argument rules this out (the survivor persists until rank hits 0,
since min-width ≥ 1 keeps a smallest diagonal `b₁`), but a Lean proof of the invariant
`b_i = ∏_{t̃<i} U_{t̃}` (divisibility preserved by every Case-1/Case-2 step) would settle it cold.
Recommended next: hand the architect the invariant + the `support` datum; the single-chain shape is
safe to blueprint.
