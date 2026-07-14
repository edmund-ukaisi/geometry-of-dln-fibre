# T-Obl3b re-formulation cert — the iterated-single-direction-spectral route does NOT close for `b>1`; the minimal irreducible primitive is the bordered-Gram/Schur-complement determinant recursion (NOT full Cauchy–Binet)

**Seat:** pen-and-paper WITNESS (re-formulation adjudication + adversarial stress-test),
genm-sj5-domination. **Date:** 2026-07-12. **NO Lean, NO build.** Exact algebra (Gram determinant
factorisation, PSD-det monotonicity, convergence-exponent arithmetic, singular-value counterexamples) +
numeric confirmation (guide only). Decorrelated `local-codex-consult` (xhigh, my conclusion WITHHELD):
`codex/tobl3b-reform-{prompt,answer}.md`. Reproducible: `scripts/tobl3b/reform_num.py` (Gram-det product
+ frobSq reduction + entanglement), `scripts/tobl3b/reform_conv.py` (convergence-exponent comparison).

**Consumed / read:** `tobl3b-pin-cert.md` (§1 minor CoV + §2 reduced convergence + §3 domination — the
charge/domination pins to preserve); `tobl3b-saturated-anb-pin-cert.md` (the saturated branch — untouched
by this cert); `final-assembly-design-cert.md` (§Obl-3b + §5 build-order); the BANKED
`RouteMSJFrontSpectral` (`frobSq_ge_twoBlock_of_sector`, `sigMin_sq_eq_iInf_eigenvalues`, `sjSector`) +
`RouteMSJFrontFirst` (`frontBox_twoBlock_le`, `frontFirst_g_le_of_sector` — the single-collapse two-block
spectral bound); the LANDED `RouteMSJShellUniform.uniformWenn_le` (PSD-monotonicity shell-0 bound) +
`RouteMSJShellCharge.flagCharge_ge`/`flagShift_lt_carrierThreshold` (the charge telescoping);
`RouteMSJDetMono.det_le_det_of_posSemidef_sub` (banked PSD-det monotonicity);
`RouteMSJOffSectorBPos.detGram_lintegral_box_lt_top` / `corankWeight_bpos_lt_top` / `corankOffSector_bpos_le`.

---

## ★ VERDICT — the native re-expression does NOT close for `b>1`. State it LOUDLY.

**The iterated-single-direction spectral route (peel the `j` weak `Z`-directions one at a time, reusing the
banked two-block spectral bound `frontBox_twoBlock_le`) does NOT close the shell-`j` uniform bound for a
corank block of width `b > 1`.** The banked spectral bound is a **Frobenius-trace, single-collapse** bound;
the T-Obl3b weight `det((A_cor Z)(A_cor Z)ᵀ)^{−a/2}` is a **determinant (product of all `b` Gram
eigenvalues)**. They coincide ONLY at `b = 1`. Three independent, exact obstructions (all confirmed by a
decorrelated Codex at 98%; my conclusion was withheld from its prompt):

```
OBSTRUCTION 1 (trace ≠ det, DISPOSITIVE).  Q_δ = diag(1,…,1,δ) (b×b):
   det(QQᵀ)^{−a/2} = δ^{−a} → ∞     but     frobSq(Q) = ∑λ → b−1  (BOUNDED).
   ⇒ NO inverse power of any frobSq loss can upper-bound the det-Gram weight near a rank-(b−1) matrix.
     The det singularity strictly dominates the trace singularity — a hard inequality DIRECTION, not a
     loose estimate. The banked bound's integrand (frobSq^{−c'}) is the wrong object for b>1.

OBSTRUCTION 2 (row-wise Gram–Schmidt scalarises, but ENTANGLES + does NOT shrink the corner).
   det(QQᵀ) = ∏_{i=1}^b ‖q_i^⊥‖²   (Gram–Schmidt; q_i^⊥ ⟂ span(q_1..q_{i-1}); numeric 2.6e-13, 1000 draws)
   and the INNERMOST row-integral IS a frobSq/SPEC shape:  ‖q_b^⊥‖² = frobSq(A_b·(ZΠ)),  Π = I−proj_{V_{b-1}}
   (numeric 1.4e-14).  BUT: (i) SPEC leaves sigMin(ZΠ)^{−α'}, and ZΠ depends on ALL outer rows A_1..A_{b-1}
   (numeric: sigMin(ZΠ) spans 1.61..2.23 across outer-row draws) ⇒ the b-fold iteration is NOT b independent
   SPEC applications — the residual sigMin factors entangle the outer corank-row integrals.  (ii) Removing
   one A-row leaves exponent STILL a/2 ⇒ residual corner a×(b−1), NOT the required (a−1)×(b−1); the charge
   (a−1)(b−1) is NOT reproduced.  (iii) The projected tail ZΠ (rank M₂−(i−1)) may retain SEVERAL weak
   directions ⇒ SPEC's single-collapse SECTOR hypothesis fails without a further flag decomposition.

OBSTRUCTION 3 (PSD-monotonicity strong-projection: banked, Cauchy–Binet-free, but WRONG convergence + a
   genuine divergence).  ZZᵀ ⪰ ε²·P_strong  ⇒  det(A ZZᵀ Aᵀ) ≥ ε^{2b}·det((A U_s)(A U_s)ᵀ),  U_s the M₂−j
   strong directions.  This is a CLEAN generalisation of the LANDED uniformWenn_le (j=0 all-strong case) —
   no Cauchy–Binet.  But the reduced weight ∫_A det((A U_s)(A U_s)ᵀ)^{−a/2} over the b×(M₂−j) block converges
   iff  a < (M₂−j) − b + 1 = M₂−j−b+1  — OFF BY 2j from the design's  a−j < M₂−b+1.  At the anchor (3,3,3)@t★=1
   (a=b=2, M₂=3, j=1): design 1<2 ✓, crude 2<1 ✗ (reform_conv.py).  And in the gap the divergence is REAL:
   as the j weak σ's → 0 monotonically with a ≥ M₂−b−j+1, monotone convergence gives Wenn(Z_δ) → ∞
   (Codex Q2).  ⇒ PSD-monotonicity keeps the FULL a×b corner; it CANNOT shrink the corner. The corner-shrink
   is not optional and is not derivable from PSD-monotonicity + SPEC.
```

**BUT — the sharpening that de-risks the controller's decision: the irreducible determinant primitive is
NOT full Cauchy–Binet.** The corner-shrink `(a,b) ↦ (a−1,b−1)` needs a Gram-volume pivot coupling one
`A_cor`-row direction with one `Γ`-direction — "determinant geometry" — and the **MINIMAL** such identity is
the strictly-smaller **one-step bordered-Gram / Schur-complement recursion**

```
det Gram(q_1,…,q_i) = det Gram(q_1,…,q_{i-1}) · dist(q_i, span(q_1,…,q_{i-1}))²      (on the independent locus)
```

iterated to `det(Q Qᵀ) = ∏_i ‖q_i^⊥‖²`. It needs **no sum over all `b×b` minors** (unlike full Cauchy–Binet)
and is a direct Schur-complement of the bordered Gram. **Mathlib v4.29 HAS `Matrix.det_fromBlocks₁₁`
(the Schur-complement determinant) + `GramMatrix.lean` + `GramSchmidtOrtho.lean`** — so this is a bounded,
Mathlib-adjacent build. It is **LABOUR, not a wall**: the design (charges, domination-`≤`, saturation) is
sound; only the CoV's determinant primitive is now correctly named and correctly sized.

---

## 1. THE CRUX (task #1) — the iterated peels do NOT compose to the pinned charge

**What "iterate the banked bound `j` times" would require, and why each attempt breaks.** The banked bound
`frontBox_twoBlock_le` CONSUMES `∫_{A₀∈box} frobSq(A₀·P)^{−c'}` and PRODUCES `C·sigMin(P)^{−α'}`. It is
single-collapse (one small singular direction of `P`, `sjSector` hypothesis) and frobenius-trace-shaped. To
"iterate `j` times" the output `sigMin(P)^{−α'}` must feed a NEXT front-box integral — but `sigMin^{−α'}` is
not a `frobSq` integrand, so the iteration has no native successor step. The only way to manufacture the
det-Gram from frobSq pieces is the row-wise Gram–Schmidt factorisation (OBSTRUCTION 2), which:

- **scalarises correctly** — `det(QQᵀ)^{−a/2} = ∏_i ‖q_i^⊥‖^{−a}`, each factor a `b=1` frobSq loss at
  `c' = a/2`, and by Tonelli the nonneg integrand integrates row-by-row (`reform_num.py` §1–§2, exact match);
- **but does NOT compose to `j` independent SPEC applications** — applying SPEC to the innermost row leaves
  `sigMin(ZΠ)^{−α'}` with `ZΠ` depending on the outer rows (`reform_num.py` §3, sigMin varies 1.61..2.23);
  the outer integral must carry `sigMin(ZΠ)^{−α'} ⊗ ∏_{i<b}‖q_i^⊥‖^{−a}` JOINTLY. This joint anisotropic
  `b×b` coupling is exactly what a single `b×b` det-Gram (or its Schur-complement recursion) handles cleanly
  and what an iteration of a single-collapse bound cannot.
- **and does NOT shrink the corner** — removing one `A_cor`-row keeps the exponent at `a/2`, so the residual
  is an `a×(b−1)` corner, never the pinned `(a−1)×(b−1)`. The freed-corner charge `½(a−j)(b−j)` is not
  produced.

**Do the exponents telescope?** The CHARGE telescoping is sound and BANKED regardless of the CoV mechanism
(`flagCharge_ge` = `minAdm_le_peelCharge_add_redChain`; convexity `minAdm_redChain_succ_ge`; the pin cert
swept `C_j ≥ minAdm(M)` 0/3161). But the ANALYTIC exponents do NOT telescope through iterated SPEC: SPEC's
per-peel `α' ∈ (max(0, a−(M₂−1)), 1)` (single row, `m=1`, `c'=a/2`) charges `< 1` per peel and passes a
`sigMin^{−α'}` tube; there is no arithmetic that assembles `j` such single-row tube-charges into the design's
`½(a−j)(b−j) + minAdm(redChain(t★+j))` — the tube-charge lives over the OTHER corank rows, not the deeper
`Z`-layers, so it does not map onto the `redChain` recursion. **The exponents do not telescope; the charge
does (banked), but only under the det-Gram / bordered-Gram CoV, not under iterated SPEC.**

## 2. THE BANKED REUSE (task #2) — exactly what `FrontSpectral`/`FrontFirst` provide, and its true reach

**`RouteMSJFrontSpectral` provides** the pure spectral algebra: `frobSq_mul_eq_sum_eigenvalues`
(`frobSq(A₀·P) = ∑_j λ_j·‖(A₀Q)_{·j}‖²`, `λ,Q` = spectrum of `P·Pᵀ`), `sigMin_sq_eq_iInf_eigenvalues`
(`sigMin P² = ⨅ λ`), `sjSector κ P hr` (the SECTOR predicate: every Gram-eigenvalue EXCEPT the single
smallest is `≥ κ²`), and `frobSq_ge_twoBlock_of_sector` (on the sector, `frobSq(A₀P) ≥ (⨅λ)·(collapsing
v-block) + κ²·(bounded-below u-block)`).

**`RouteMSJFrontFirst` provides** the measure bound (the object the tide wanted to reuse):
> `frontBox_twoBlock_le (P) (hr : 0<r) (hκ,hc',hσ:0<sigMin P, hσB:sigMin P ≤ B) (hα0:0<α')`
> `(hαlo: 2c'−m(r−1) < α') (hαhi: α'<m)` :
> `∃ C<⊤, ∫_{A₀∈matBox m r 1} frobSq(of A₀ · P)^{−c'} ≤ ofReal(sigMin P ^ (−α')) · C`,
and `frontFirst_g_le_of_sector` adds the a.e. transfer `frobSq^{−c'} ≤ twoBlockLoss^{−c'}` under
`sjSector κ P`. Here `σ = sigMin P` (ONE collapsing singular value of the TAIL `P`), `α'` the single
front-charge, box = `matBox m r 1`, `C` the σ-independent constant (from `twoBlock_radial_le`, `du=m(r−1)`,
`dv=m`).

**Does the single-direction bound apply to the deeper-`Z` singular directions?** — **Partly, and this is the
crux of the reach question:**
- **YES for `b=1`.** The corank weight at `b=1` IS a frobSq: `det(Q_bQ_bᵀ) = ‖A_cor·Z‖² = frobSq(A_cor·Z)`,
  and `frontBox_twoBlock_le` with `m=1, r=M₂, P=Z, c'=a/2` gives `Wenn(Z) ≤ C·sigMin(Z)^{−α'}` — the deeper
  product `Z`'s smallest singular value IS the collapse direction. This is the Obl-1 case; it composes.
- **NO for `b>1` and for `j≥2` weak directions.** (i) The weight is a det-Gram, not a frobSq (OBSTR. 1). (ii)
  For `j≥2` collapsing directions of `Z` the SECTOR hypothesis `sjSector κ Z` FAILS (more than one small
  eigenvalue), so the bound does not even apply to `Z` directly. (iii) The row-wise reduction's quotient tail
  `ZΠ` can retain several of the `j` weak directions, so its sector also fails without further flag work
  (Codex Q3(2)). The banked bound is genuinely a SINGLE-collapse, `b=1`-native tool.

## 3. BUILD-ORDER INVERSION (task #3) — the corrected order + the (unchanged) LHS shape

The off-sector-over-`Z` integrand (T-Obl3b's LHS) is produced INSIDE the T-peel spine (design tile #5), so
T-Obl3b cannot be stated standalone before T-peel. **Corrected build-order (co-formulated):**

1. **T-peel** does the FaithfulSJAt `Γ`-first freed-corner Gaussian peel → the atom `det(Q_bQ_bᵀ)^{−a/2} ·
   w^{−(c'−½ab)}` (`Q_b = A_cor·Z`), then stratifies the OUTER `Z` by the single-`ε` singular-value shells
   (pin cert §5: single `ε`, `S_j = {exactly j σ's < ε}`, exhaustive). This PRODUCES the shell-`j`
   off-sector-over-`Z` integrand.
2. **T-Obl3b** (the re-dispatched tile) bounds each shell-`j` integrand and hands it to the decorated IH.

Because the iterated-spectral route does NOT close (§1), **the LHS shape is UNCHANGED from the design's
det-Gram form** (the minor→bordered-Gram swap is INTERNAL to the CoV, not a change of statement). The exact
Lean statement shape of the off-sector-over-`Z` bound (per shell `j`, `1 ≤ j ≤ r−1`):

```
∫_{Z ∈ S_j} ∫_{A_cor ∈ matBox b M₂ 1} ∫_{Γ ∈ box} (w + frobSq (Ccross + of Γ · (of A_cor · Z)))^{−c'}
    ≤ const(ε) · (cornerComparator (redChain (t★+j) M) k jc  integrand  at  c' − ½·(a−j)(b−j))
```
closed by `lintegral_mono` + the arity-`(L+1)` decorated IH (`cornerComparator_adm`), with `const(ε)`
carrying `ε^{−a(M₂−j)}` and the reduced-Wenn on the strong sector. This is the design's shape; T-peel
produces the integrand first, T-Obl3b bounds it. (The saturated shell `S_r` and shell `S_0` are the LANDED
`tobl3b-saturated-anb`/`uniformWenn_le` branches — no det factorisation there: `S_0` uses PSD-monotonicity
outright, `S_r` has `p=0` freed corner and weight `≡1`.)

## 4. SHELL PREDICATE (task #4) — still required (the iterated route would have avoided it, but does not close)

Had the iterated single-direction route closed, it WOULD have peeled one `σ`-threshold at a time and needed
only single-`sigMin` sets `{σ_{M₂}(Z) < ε}` — no `{exactly j singulars < ε}` partition. Since it does NOT
close (§1), **the count-shell predicate IS still required.** The minimal measurable form (banked pieces):
`S_j = {σ_{M₂−j}(Z) ≥ ε > σ_{M₂−j+1}(Z)}` as a difference of `{minStretch of the appropriate compression ≥ ε}`
sets (`RouteMSJSigMin.minStretch` is the measurable smallest-singular-value function), or equivalently the
Loewner-projection encoding `{ZZᵀ ⪰ ε²·P_strong^{(M₂−j)}}` (the form `uniformWenn_le` already consumes for
`j=0`) — measurable via continuity of `det`/eigenvalues, summed by `ENNReal` subadditivity over the finite
`r+1`-piece single-`ε` cover. This is real, bounded LABOUR, not a wall.

## 5. PRESERVE THE PINS (task #5) — all preserved; only the CoV determinant-primitive is renamed/resized

The re-formulation adjudication changes NOTHING in the math — it identifies the correct, minimal determinant
primitive. All T-Obl3b pins are PRESERVED:
- **Uniform constant** — the only `ε`-dependent Jacobian factor is the strong-minor power `|Δ|^{−a} ≤
  ε^{−a(M₂−j)}` (weak-SV-free), whose LOWER bound `det ≥ ε^{2b}·det(strong Gram)` is PSD-monotonicity
  (banked), sharpened here to need no Cauchy–Binet.
- **Domination-`≤`** — the residual is a clean `≤` (drop nonneg `R`, `(w+R)^{−e} ≤ w^{−e}`), unchanged; the
  bordered-Gram recursion is an EQUALITY of determinants (chart Jacobian), not a new inequality.
- **Strict-convergence `j≥1`** — the reduced det-Gram convergence `a−j < M₂−b+1` (strict, 0/3161) is
  reproduced ONLY at the SHRUNK reduced dims `(a−j, b−j, M₂−j)`; the bordered-Gram recursion is precisely
  what produces those shrunk dims (§6). PSD-monotonicity alone gives the WRONG (too-strong) `a < M₂−j−b+1`
  (§ VERDICT OBSTR. 3).
- **Saturated `a≠b` inert** — the saturated shell `j=r` has `p = a−r = 0` freed corner ⇒ weight `≡1`
  (`Real.rpow_zero`), no det-Gram at all ⇒ needs NEITHER Cauchy–Binet NOR bordered-Gram. The
  `tobl3b-saturated-anb-pin-cert.md` branch stands untouched.

## 6. THE MINIMAL IDENTITY + THE LEAN BUILD PATH (for the re-dispatched T-Obl3b tile)

**The one genuinely-new determinant primitive — `borderedGram_det` (strictly < Cauchy–Binet).** On the
linearly-independent locus, via Mathlib's `Matrix.det_fromBlocks₁₁` applied to the bordered Gram
`Gram(q_1..q_i) = [[G_{i-1}, v], [vᵀ, ‖q_i‖²]]` (`v = G_{i-1}`-column of inner products), the Schur
complement is the squared distance to the span:
```
det Gram(q_1,…,q_i) = det Gram(q_1,…,q_{i-1}) · (‖q_i‖² − vᵀ (G_{i-1})⁻¹ v)
                     = det Gram(q_1,…,q_{i-1}) · dist(q_i, span(q_1,…,q_{i-1}))².
```
Induct to `det(Q Qᵀ) = ∏_i ‖q_i^⊥‖²`. **Mathlib-adjacent:** `Matrix.det_fromBlocks₁₁`
(`LinearAlgebra/Matrix/SchurComplement.lean`), `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`,
`GramSchmidtOrtho.lean` all exist at v4.29. This is a network-free, reusable, Mathlib-worthy build; smaller
than full Cauchy–Binet (no sum over `C(M₂,b)·C(n,b)` minors).

**The assembly that CLOSES T-Obl3b (`1 ≤ j ≤ r−1`), consuming BANKED + the one new primitive:**
- weak-SV-free LOWER bound `det(A_cor ZZᵀ A_corᵀ) ≥ ε^{2b}·det((A_cor U_s)(A_cor U_s)ᵀ)` —
  **PSD-monotonicity, BANKED** (`det_le_det_of_posSemidef_sub`; generalises `uniformWenn_le`), NO Cauchy–Binet.
- the corner-shrink CHART (eliminate the `j` weak directions, re-chart to the deeper comparator at reduced
  dims `(a−j, b−j, M₂−j)`) — the Jacobian is the strong-minor determinant; **`borderedGram_det` supplies it**
  (the ONE new primitive). This is where the design's "`(M₂−j)`-minor chart" lives, now correctly sized.
- reduced det-Gram integrability at the SHRUNK dims — **BANKED** (`detGram_lintegral_box_lt_top` at
  `r=b−j, n=M₂−j, a=a−j`; converges by `a−j < M₂−b+1`).
- charge telescoping `C_j ≥ minAdm(M)`, IH fires (`c' < ½C_j` strict) — **BANKED** (`flagCharge_ge`,
  `flagShift_lt_carrierThreshold`).
- the single-`ε` exhaustive count-shell cover — small NEW (`minStretch` + `RankLocusClosed`, §4).

**Controller decision (either way is LABOUR, not a wall):**
- **(A) minimal:** build `borderedGram_det` (Schur-complement recursion, ~1 module on `det_fromBlocks₁₁`),
  slot it as the chart Jacobian in the design's minor CoV. Strictly smaller than Cauchy–Binet.
- **(B) general:** build full Cauchy–Binet `det(BΣ²Bᵀ) = ∑_{|S|=b} minor(B_{:,S})²∏_{k∈S}σ_k²` (a larger,
  more broadly reusable Mathlib-worthy piece). Overkill for T-Obl3b, but a durable library asset.
The pin cert's route works with EITHER; **(A) is the minimal irreducible need.** Neither is a math wall.

## 7. DECORRELATED CODEX VERDICT (my conclusion withheld from the prompt)

`codex/tobl3b-reform-{prompt,answer}.md` (xhigh; the exact objects + the banked SPEC + PSD-monotonicity +
the design charges supplied; my "does-not-close / bordered-Gram-minimal" conclusion WITHHELD). **Codex
CONCURS on all four, decorrelated, at 98% confidence:**
- **Q1 NO** — SPEC controls the det weight only at `b=1`; the `diag(1,…,1,δ)` counterexample (det `δ^{−a}→∞`,
  frobSq bounded) is a hard direction; reducing `b>1` needs `det Gram = ∏‖q_i^⊥‖²` = "a determinant
  factorisation / iterated Schur-complement/Cholesky; QR merely moves it into the Jacobian" (independently
  re-derived — matches my OBSTR. 1–2).
- **Q2** — PSD projection gives exact `a < M₂−j−b+1`, differs from design `a−j < M₂−b+1` by `2j`; in the gap
  `Wenn(Z_δ)→∞` is genuinely UNBOUNDED (my OBSTR. 3, independently re-derived with the codim-`k=d−b+1` radial
  count); "the required simultaneous shrink `(a,b)↦(a−1,b−1)` needs a pivot/Schur-complement coupling one
  `A`-row with one `Γ`-direction — that mechanism is determinant geometry."
- **Q3** — Gram–Schmidt gives legitimate nested scalar integrals (Tonelli) but not a clean SPEC iteration:
  `P_i` has an `(i−1)`-dim kernel (`sigMin=0`), the quotient tail retains weak directions (sector fails),
  the projected tail depends on all previous rows (entanglement — my numeric §3), and removing one row keeps
  exponent `a/2` (corner not shrunk); "determinant geometry has merely migrated into `det H`, the residual
  norms, and the QR Jacobian."
- **Q4** — SPEC + PSD-only does NOT close; a determinant factorisation is IRREDUCIBLE; **the minimal identity
  is the one-step bordered-Gram/Schur-complement recursion `det Gram(q_1..q_i) = det Gram(q_1..q_{i-1})·
  dist²`, strictly smaller than full Cauchy–Binet.** The flip-condition ("a uniform one-weak-direction lemma
  from SPEC + PSD alone with no Schur/minor/QR/volume identity") is judged to "contain the missing
  determinant identity in disguise." No inference of mine was fed in; the concurrence is decorrelated.

---

## Close

- **Firmest result (decorrelated-confirmed, exact + numeric).** The iterated-single-direction-spectral route
  **does NOT close** the `b>1` shell-`j` uniform bound. The banked spectral bound is a single-collapse
  frobenius-trace object; the T-Obl3b weight is a `b×b` det-Gram (product). They coincide only at `b=1`. Three
  independent obstructions: (1) `frobSq^{−c'}` cannot dominate `det^{−a/2}` (`diag(1,…,1,δ)`, a hard
  direction); (2) row-wise Gram–Schmidt scalarises but entangles the outer rows and does not shrink the
  corner; (3) PSD-monotonicity strong-projection is Cauchy–Binet-free but gives the wrong convergence
  (`a < M₂−j−b+1`, off by `2j`) with a GENUINE `Wenn→∞` in the gap. **A `b×b` determinant identity is
  irreducible here.**
- **The sharpening (the high-value finding).** The irreducible primitive is NOT full Cauchy–Binet — it is the
  strictly-smaller **bordered-Gram / Schur-complement recursion** `det Gram(q_1..q_i) = det Gram(q_1..q_{i-1})·
  dist(q_i, span)²`, buildable directly on Mathlib's `Matrix.det_fromBlocks₁₁` + `GramMatrix` + `GramSchmidtOrtho`
  (all present at v4.29). The uniform LOWER bound is PSD-monotonicity (BANKED, no det identity); the
  bordered-Gram is needed ONLY for the corner-shrink chart Jacobian. The design (charges, domination,
  saturation) is SOUND; the pins are PRESERVED; the saturated `a≠b` branch needs no det identity at all.
- **Most likely to break it / the next step.** The one thing that would flip the verdict is a uniform
  one-weak-direction reduction proved from SPEC + PSD alone with NO Schur/minor/QR/volume identity — Codex
  and I both judge any such proof would smuggle in the determinant identity (the `diag(1,…,1,δ)` direction is
  dispositive). **Controller decision:** build the minimal `borderedGram_det` (option A, a bounded
  Mathlib-adjacent module) OR full Cauchy–Binet (option B, a durable but larger library asset); the design's
  minor CoV closes with EITHER. Recommend (A). Either is LABOUR, not a wall. If a further pen-and-paper is
  wanted before the build: pin the exact corner-shrink chart at the anchor `(3,3,3)@t★=1, j=1` with the
  `borderedGram_det` Jacobian in place of the pin cert's Cauchy–Binet minor, to confirm the reduced residual
  `= cornerComparator(redChain 2 (3,3,3))`-integrand identification survives the primitive swap (it should —
  the Jacobian value is the same 2×2 strong minor).
