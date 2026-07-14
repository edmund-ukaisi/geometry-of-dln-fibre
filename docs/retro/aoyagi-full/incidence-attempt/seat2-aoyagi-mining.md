# Seat 2 — Mining Aoyagi (2023) for the corank-peel / alignment degeneracy

**Seat:** `pen-and-paper` (retro, incidence-attempt). **Date:** 2026-07-14.
**Question put to me:** the aoyagi-full Lean build is walled on ONE analytic estimate — the
"partial-shell transverse-Schur incidence estimate" `(∗_T1)`. Working hypothesis: Aoyagi handles this
exact degeneracy at her corank-peel/recursion step (algebraically, at germ level, in chart
coordinates), and the missing estimate is her step translated into an integral-domination statement.
**Task:** mine her actual proof, extract the mechanism, translate germ→region, verdict on `(∗_T1)`
with the `(2,2,3)` corner in exact arithmetic. FACT vs INFERENCE throughout.

**Sources.** Paper text = `theory/aoyagi-2023-reproduction/aoyagi-2023-extracted-text.txt` (page-tagged),
cross-checked against the repo's corrected reproduction (`verify-*.md`); page images are the reproduction's
authority where the pdf→text garbles (esp. Definition 3). Exact scripts:
`/tmp/aoyagi_mining/{corner_223.py, corner_reduction.py}`. Decorrelated consult:
`/tmp/aoyagi_mining/codex-{prompt,answer}.md` (gpt-5.x, xhigh; independently verified F1–F3 below).

**One-line verdict (up front).** Aoyagi's proof does **not** contain `(∗_T1)` and her mechanism does
**not** translate to it. What she has is a **germ-level** move (Lemma 2 block-elimination → Schur node,
then a global monomial resolution), plus **Theorem 4** which lets her *replace the parameter region by
the deepest-point germ entirely* — so she never needs a box-integral domination. `(∗_T1)` is a
**region-level, base-preserving, uniform-over-the-moving-family** integral inequality; the gap
germ→region (uniform constants; the singular-`P` and rank-minor strata; the moving-subspace incidence)
is genuinely new analysis relative to her paper. The `(2,2,3)` corner is *consistent* with `(∗_T1)`
being true (LHS finite below `T1`, threshold attained exactly at `T1`), but that consistency is not a
proof of the uniform step. **The constructive read: her germ mechanism is exactly the input to the
repo's germ-level *squeeze* route (Route B), where the incidence "wall" does not arise — not to the
box-integral cover route (Route A) that `(∗_T1)` belongs to.**

---

## (i) The located steps in Aoyagi's proof

All the degeneracy handling is at **germ level** (a point), via **ideal equalities under unit
transforms**, followed by a **global** monomial resolution. Locations are page/line in the
page-tagged extraction.

1. **Lemma 1 — the RLCT is an ideal invariant (p5, L184–199).**
   > If `J = ⟨F₁,…,Fₙ⟩` and `G₁,…,Gₘ ∈ J`, then `λ_w(ΣG²) ≥ λ_w(ΣF²)`; if moreover `J = ⟨G₁,…,Gₘ⟩`
   > then `λ_w(ΣF²) = λ_w(ΣG²)`.

   This is the ONLY tool she uses to move between forms. It is a statement about the **germ RLCT at a
   point `w`** — a single number — not about integrals over a region. Every "= " in her recursion is a
   Lemma-1 ideal equality. FACT (quoted).

2. **Lemma 2 — block elimination via the invertible pivot (p10–11, L426–508).**
   For `A = [[A₁,A₂],[A₃,A₄]]` with `A₁` a **regular `r×r`** block, the units
   `Q₁ = [[E,O],[−A₃A₁⁻¹, E]]`, `Q₂ = [[E,−A₁⁻¹A₂],[O,E]]` give `Q₁AQ₂ = diag(A₁, C₄)`,
   `C₄ = A₄ − A₃A₁⁻¹A₂` (the **Schur complement**), `rank C₄ = rank A − r`. FACT (quoted, with proof).

   This is the object the hypothesis calls the "corank peel". `A₁` is the pivot `P`; `C₄` is the
   residual. The transforms are **local analytic units**: `A₁⁻¹` is bounded only *because Aoyagi sits
   in a neighbourhood of the base point where `A₁ ≈ E_r`* (see step 5).

3. **Theorem 3 — whole-product block-diagonalisation (p11–13, L519–782).**
   By induction on layers, units `P₁,P₂` give
   `P₁(∏A^{(s)})P₂ = diag(C₁, ∏C^{(s)})`, `C₁` regular `r×r`, `C^{(s)}` the **reduced** `M^{(s)}×M^{(s+1)}`
   blocks (`M^{(s)} = H^{(s)} − r`). The regular part peels off exactly:
   `λ_w⟨∏A^{(s)} − ∏Ā^{(s)}⟩ = [r² + r(H^{(1)}+H^{(L+1)} − 2r)]/2 + λ_w⟨∏C^{(s)}⟩` (p13, L818–833).
   FACT (quoted). This is the "regular block contributes `r(H¹+H^{L+1})/2 − r²/2`, then recurse on the
   reduced product" split.

4. **The recursive blow-up + `diag(b)` bookkeeping (p14–22, L866–1537).**
   Inductive statement (p14–15, L891–904):
   > `⟨∏C^{(s)}⟩ = ⟨ diag(b₁,…,b_{M(S)}) · [[E_J, O],[O, D_J]] · ∏_{s=S+1}^{L} C^{(s)} ⟩`,

   `M(S) = min{M^{(s)} : 1≤s≤S}` (running-min width), `b_i` = **products of blow-up scalars `u_{s,k}`**,
   `D_J` the residual block. Each step blows up the submanifold `{d_{ij}=0 (residual block), u_{S,k}=0}`,
   factors a common scalar `u_{S,J+1}` out of the residual into the weights (`b'_i = u_{S,J+1} b_i`), and
   clears one residual pivot via a **unit matrix `P` whose entries are `b`-ratios** `−(b'_{J+i}/b'_{J+1}) d''`
   (p18 L1165–1194, p20 L1422–1451). The blow-up **Jacobian** per step is `u^{M_{s,k}−1} du` with
   `M_{s,k}` the **codimension of the blown-up centre** (Case 2: `(M(S)−J)(M^{(S+1)}−J)`; Case 1 the
   split form). She reads off (p22, L1543–1557):
   > candidate lct `= ½ min{ M_{s,k} : t̃_{s,k}=0 }`,
   > `M_{s,k} = (M^{(1)}−t^{(1)})(M^{(2)}−t^{(1)}) + Σ_{j≥2}(t^{(j−1)}−t^{(j)})(M^{(j+1)}−t^{(j)})`.

   FACT (quoted). This `M_{s,k}` is the reproduction's `Mval` (codim); `λ = ½·min Mval`. **This is a
   GLOBAL resolution** — she blows up in the space of *all* the `C^{(s)}` entries jointly and takes the
   min over *all* charts. There is no "reduce layer-`s` integral to the shorter-chain integral" step.

5. **Theorem 4 — the deepest-point reduction (p14, L839–857; cited from her [22]).**
   For `Fᵢ` homogeneous in `w₁,…,w_j` and `φ` suitably homogeneous,
   > `λ_{(0,…,0,w*_{j+1},…,w*_d)}(⟨F⟩,φ) ≤ λ_{(w*_1,…,w*_j,w*_{j+1},…,w*_d)}(⟨F⟩,φ)`.

   i.e. **the RLCT is minimised at the deepest (most degenerate) point**. She uses it (L857, "we can set
   `r(s)=r`") to reduce the whole parameter region to the germ at the origin. FACT (quoted).
   **This is the load-bearing structural fact for my verdict:** Aoyagi's proof deliberately *avoids* any
   region/box integral — Theorem 4 collapses the region to the deepest germ, and everything after is a
   germ computation. A box-integral domination like `(∗_T1)` is a strictly heavier object than anything
   in her proof.

**What plays the role of the "transverse part"?** The residual/Schur complement `C₄ = A₄ − A₃A₁⁻¹A₂`
(Lemma 2) and, one level down, the residual block `D_J` of the recursion. **How does she charge it?**
By the **blow-up Jacobian `u^{M_{s,k}−1}`** of the centre `{D_J = 0} ∩ {u=0}`, whose exponent `M_{s,k}`
is the codimension of that centre — *not* by any per-`z` fibre integral. The charge is the codimension
of the vanishing locus, read globally.

---

## (ii) The translated mechanism, with Jacobians — and where it fails to reach the region

`(∗_T1)` peels the outer layer `A⁽⁰⁾` (`M₀×M₁`) at pivot rank `u` (`a=M₀−u`, `b=M₁−u`), integrates the
current-layer parameters `(P,B₁₂,C,Γ)` and the corank family `A_cor`, and asks for a bound by the
**shorter-chain** integral. Aoyagi's germ move translates as follows.

**Step T-1 (Lemma 2 block-elimination = the freedSchur structure).** Left-multiplying `A⁽⁰⁾` by the
unit `Q₁ = [[E,O],[−CP⁻¹,E]]` and applying to `hsQ = [Q_p ; Q_b]`:
`‖A⁽⁰⁾hsQ‖² ≡_ideal ‖P Q_p + B₁₂ Q_b‖² + ‖C₄ Q_b‖²`, `C₄ = Γ − CP⁻¹B₁₂` (Schur complement of `A⁽⁰⁾`).
The residual acts on the **corank rows only**. This IS the freedSchurLoss structure. **FACT** (Lemma 2).
*Region caveat:* `Q₁` involves `P⁻¹`; `‖Q₁X‖² ≠ ‖X‖²`, so this is an **ideal/germ equality (Lemma 1)**,
not a two-sided norm bound with uniform constants. The setup dodges `P⁻¹` by keeping `C` un-eliminated
(retaining `C Q_p`), at the cost of a residual `‖C Q_p + Γ' Q_b‖²` that recouples `Q_p, Q_b` — so the
clean Schur exposure of the incidence has to be re-derived, not inherited.

**Step T-2 (the shear translations, Jacobian 1 — the honest change of variable).** With
`D = XY^⊤(YY^⊤)⁻¹`, `X = Q_p`, `Y = Q_b`, the translations `B₁₂ ↦ B₁₂ + PD`, `Γ ↦ Γ + CD` have
**Jacobian 1** and put the loss in the transverse form
`‖P·Q_p(I−Π_b)‖² + ‖B₁₂' Q_b‖² + ‖C·Q_p(I−Π_b)‖²` (Π_b = proj onto rowspan `Q_b`). **FACT** (exact;
this is the region-level analogue of Aoyagi's `−A₁⁻¹A₂`, `−A₃A₁⁻¹` shears, and the one place her germ
move genuinely survives to the box because the Jacobian is a *constant* 1).

**Step T-3 (charge the pivot columns — Aoyagi's `M_{s,k}` Jacobian, as a fibre integral).** The
current-layer charge `ab/2` is Aoyagi's centre-codimension `(M₀−u)(M₁−u)/2` read as the Jacobian of
integrating out `B₁₂'` (the `u×b` block) against the pivot direction. Where Aoyagi writes a monomial
blow-up Jacobian `u^{ab−1}`, the region version needs `∫_{box} (…‖B₁₂'Y‖²…)^{−c'} = C·(…)^{−(c'−ab/2)}`
— the banked lemma **K3** (`det(Q_bQ_b^⊤)^{−a/2}` charge + exponent shift `−ab/2`). **FACT that the
exponent bookkeeping matches** (corner check below); **INFERENCE that K3 supplies it uniformly** in the
moving family.

**Where the translation breaks (germ → region). Enumerated, with the Jacobian for each fix.**

| # | Aoyagi germ move | Region-level obstruction | Fix / status |
|---|---|---|---|
| G1 | Lemma 1 gives **RLCT equality at a point** | `(∗_T1)` is a **per-`c'` integral inequality over boxes** with a finite constant; a germ RLCT equality does not imply it | not a fix — a **different statement** (Codex Q1). The literal already-`z`-integrated `(∗_T1)` is even vacuous (`K_j = L/R` if both sides finite); the load-bearing content is the **pointwise-in-`z`** bound |
| G2 | `A₁⁻¹ = P⁻¹` bounded because `A₁ ≈ E` near base | over the **IsUnit-`P` box** `P⁻¹` is unbounded; norm-comparison constants blow up like `σ_min(P)^{−k}` | **repairable by labour**: a floor `σ_min(P) ≥ δ`, else dyadic singular-value strata / determinantal blow-up, Jacobian `\|u\|^{k−1}`. New *global-absorption* content, not a corollary of "P invertible" (Codex Q2a) |
| G3 | fixed base point `Q_p = pivot ≈ E` | `Q_p = Q_p(z)` **moves** (direction + magnitude); need `∫_{layer} ≤ K·(‖Q_p(z)‖²)^{−q}` uniformly | on a chart where a `u×u` minor `X_I` of `Q_p` is floored, normalise `P'=PX_I, C'=CX_I`, **Jacobian `\|det X_I\|^{u+a}`** — uniform only while `\|det X_I\| ≥ δ`; covering rank-loss needs **minor shells** + proving the determinant powers are absorbed by the RHS divisor. **Additional content** (Codex Q2b) |
| G4 | residual charged by centre codim `M_{s,k}` (global) | the **moving-subspace incidence** rowspan `Q_b → Q_b` aligning with rowspan `Q_p` is a *fibre* degeneration; bare Gram `det(Q_bQ_b^⊤)` is **blind** to it | needs the **transverse Schur** `det(Q_b(I−Π_p)Q_b^⊤)` and a **`z`-uniform fibre pushforward**. Aoyagi's blow-ups **jointly mix base (`z`) and fibre (layer) variables**, so no base-preserving fibrewise version is extractable by bookkeeping. **Genuinely NEW** (Codex Q2d, Q3) |
| G5 | `diag(b_i)` — full per-row **coupled** divisor support | RHS uses a single **scalar** `commonDivisor(z)²` with exponent shift `−ab/2` | factoring a scalar common divisor has Jacobian 1 but **discards the support-sharing**; the reproduction proved the coupled `b_i` are **necessary at corank ≥ 2** (thresholds-only gives the wrong value). Collapsing to a scalar with the exact shift needs a **new weighted-comparison theorem**. **Genuinely NEW** (Codex Q2c; reproduction `verify-r1-light-recursion.md`) |

So the honest translation reaches T-1/T-2 (germ structure + a Jacobian-1 shear that survives to the
box) and stalls at G1/G3/G4/G5: the RLCT-equality → integral-inequality promotion, the moving family,
the moving-subspace incidence, and the coupled-divisor collapse are **not** in Aoyagi.

---

## (iii) Verdict on `(∗_T1)`, with the `(2,2,3)` binding corner in exact arithmetic

**Verdict: Aoyagi's mechanism does NOT yield `(∗_T1)`.** She proves the RLCT *value* by a global
germ-level resolution and, via Theorem 4, never needs a region/box domination at all. `(∗_T1)` is a
strictly different (region-level, base-preserving, uniform-over-the-moving-family) object. The corner
below shows `(∗_T1)` is *consistent* (LHS finite for `c'<T1`, threshold exactly `T1`) — but the corner
tests the **threshold at fixed `z`**, not the **uniform-in-`z`** step, which is the actual wall.

**Corner setup (exact).** `M=(M₀,M₁,M₂)=(2,2,3)`, peel outer `A⁽⁰⁾` (`2×2`) at `u=1`; `a=b=1`,
`ab/2=1/2`. Deepest tail: `A⁽¹⁾` is `2×3`, `Z=I₃` (last width `n=M₂=3`), so `Q_b = A_cor·I₃ = A_cor`
(`1×3`). Fix `z` so `Q_p = e₁ = (1,0,0)`; the incidence family is `Q_b = (q₁,t₂,t₃)`, alignment at
`t₂=t₃=0`. Scalars `p=P` (unit ≈1), `β=B₁₂`, `c₀=C`, `γ=Γ'`. Loss
`F = (p+β)² + β²(t₂²+t₃²) + (c₀+γ)² + γ²(t₂²+t₃²)`.

**Certified facts** (`/tmp/aoyagi_mining/corner_223.py`, `corner_reduction.py`; sympy + Newton-polytope
LP, exact rationals; independently re-derived by Codex):

- **F1 — arithmetic is tight and additive.** `Mval_min(2,2,3)=4 ⇒ T1=2` (at `t=(1,0)`; `t=(0,·)` also
  attains 4). Reduced chain `redChain 1 (2,2,3) = (1,3)`: `Mval_min=3 ⇒` reduced RLCT `=3/2 = q`-threshold.
  **Additivity exact:** `ab + codim(reduced) = 1 + 3 = 4 = codim(full)`; equivalently
  `T1 = ab/2 + (reduced RLCT) = ½ + 3/2 = 2`. Codex confirmed `min(4,4,6)=4` for `(2,2,3)`. **FACT.**
- **F2 — the incidence degeneracy at this corner is a NONDEGENERATE quadratic; RLCT `= T1` exactly.**
  The in-domain zero locus of `F` is `{p+β=0, c₀+γ=0, t₂=0, t₃=0}` (codim 4), along which `β≈−1`,
  `γ≈−c₀` are **spectators** (`F` does not vanish in those directions there). With `x=p+β, y=c₀+γ`:
  `F = x² + y² + (β²+γ²)(t₂²+t₃²)`, and `β²+γ² > 0` is a **unit** on the locus. The transverse Hessian
  in `(x,y,t₂,t₃)` has eigenvalues `{2, 2, 2(β²+γ²), 2(β²+γ²)}` — positive definite. A `d=4`
  positive-definite quadratic has RLCT `d/2 = 2 = T1`; radialising gives exactly `∫₀^δ r^{3−2c'} dr`,
  which **converges iff `c' < 2` and DIVERGES at `c'=2=T1`** (verified `c'∈{19/10 → 5, 2 → ∞, 21/10 → ∞}`).
  So the LHS is finite below `T1` with the threshold **attained exactly at `T1` (zero slack)**. **FACT.**
- **F3 — bare-Gram control is blind to the incidence; the transverse Schur is not.** Exact at the
  corner (`corner_reduction.py`, K2 identity checked `≡ 0`): `det(Q_bQ_b^⊤) = q₁²+t₂²+t₃² ≈ 1` at
  incidence (`q₁≈1`), while `det(Q_b(I−Π_p)Q_b^⊤) = t₂²+t₃² → 0`. Codex re-derived the dual form
  `det(YY^⊤)=1+|t|²`, `det X(I−Π_Y)X^⊤ = |t|²/(1+|t|²)`, `det Y(I−Π_X)Y^⊤ = |t|²`, and the symmetry
  `det(YY^⊤)det(X(I−Π_Y)X^⊤) = det(XX^⊤)det(Y(I−Π_X)Y^⊤)`. So any estimate keyed on `det(Q_bQ_b^⊤)^{−a/2}`
  alone cannot see the degeneration. **FACT.**
- **F4 — the P-radial blow-up (K5) does NOT decouple the pivot weight.** After `(p,β)=R(ω_p,ω_β)`,
  `‖[P|B₁₂]hsQ‖² = R²·[(ω_p+ω_β)² + ω_β²(t₂²+t₃²)]` — **still `A_cor`-dependent** through
  `ω_β²(t₂²+t₃²)`, which is precisely the transverse/incidence term. So K5 cannot hand an `A_cor`-free
  weight to K4; any "decoupling" strong enough to feed K4 *is* the missing incidence estimate. **FACT.**

**Consequence.** `(∗_T1)`'s LHS is finite for `c' < T1` at the corner and the exponent bookkeeping
(`ab/2` current-layer charge + reduced-chain `q`-threshold) is **exact and tight**. This corroborates
that `(∗_T1)` is *true*. But every one of F1–F4 is a **fixed-`z` germ fact** — it establishes the
threshold and the additive split, not the **uniform bound over the moving family `Q_p(z)`**, which is
where the wall sits (G3/G4). The corner being a benign nondegenerate quadratic is exactly why the germ
squeeze (below) handles it trivially, and exactly why it is *not* evidence that a box-integral proof is
within reach.

**A note on `(3,3,4)` (corank ≥ 2).** `Mval_min(3,3,4)=8 ⇒ RLCT 4` (Codex-confirmed `min(9,8,9,12)=8`).
The reproduction (`verify-r1-light-recursion.md`) established that a **thresholds-only** recursion (no
symbolic `diag(b)` support) returns `3` there — the coupled divisor support is **necessary** once a
binding peel has corank ≥ 2 in both layer-1 dimensions. This is G5: the scalar-`commonDivisor` collapse
is *false* in general, so `(∗_T1)`'s RHS shape cannot be a mere scalar weight without a new
weighted-comparison theorem. (Codex could not re-verify the "`=3`" number since the light recurrence
was not in its prompt; the value stands on the reproduction's exact Newton-LP computation.)

---

## (iv) The minimal genuinely-new statements a proof of `(∗_T1)` still requires

Neither is in Aoyagi, and neither is derivable by bounded bookkeeping from her constructs (because her
resolution jointly mixes base `z` and fibre layer variables — it is not base-preserving).

- **(N1) The uniform parameterised transverse-Schur incidence / pushforward estimate** — the load-bearing
  one (G3+G4). Precise sufficient form (Codex Q3, tidied): with `X=Q_p(z)`, `Y=A_cor Z(z)`,
  `D=XY^⊤(YY^⊤)⁻¹`, `S=X(I−Π_Y)`, `q=c'−ab/2`, after the Jacobian-1 translations `B'=B+PD`, `Γ'=Γ+CD`
  and integrating `Γ'`,
  > `∫_z ∫_{A_cor∈S_j(z)} det(YY^⊤)^{−a/2} ∫_{P,C,B'} ( ‖PS‖² + ‖B'Y‖² + ‖CS‖² )^{−q}`
  > `  ≤ K_{j,c'} · ∫_z ( g(z)² ‖X‖² )^{−q}`,

  **`z`-uniform**, respecting the translated-box constraint `B'−PD ∈ box`, and **including the
  singular-`P` and rank-minor strata of `X`** (G2/G3): the constant must survive `σ_min(P)→0` and
  `det X_I → 0` via minor shells whose determinant powers are absorbed by `g(z)²`. Stated pointwise-in-`z`
  (the already-`z`-integrated form is vacuous — Codex Q1). This is the estimate the genm thread named
  "(∗_T1)"; it is genuinely new relative to Aoyagi.

- **(N2) The coupled-`b` → scalar-`commonDivisor` weighted-comparison theorem** (G5). A theorem that
  Aoyagi's row-wise **coupled** `diag(b_i)` weights (with their shared exceptional factors) imply the
  proposed **scalar** `commonDivisor(z)²` bound with the **exact `−ab/2` exponent shift** — knowing that
  the corank-≥2 reproduction forbids replacing the coupled support by independent per-row scalars
  (`verify-r1-light-recursion.md`). Without this the RHS comparator shape is unjustified beyond corank 1.

Everything else in the translation is bounded labour: T-1 (Lemma 2 structure), T-2 (the Jacobian-1
shear), K3's `ab/2` charge, and the reduced-comparator integration.

---

## The constructive read — steer to the germ-level squeeze (Route B), not the box cover (Route A)

The mining answers a question the brief did not ask but that the wall demands: **`(∗_T1)` is the wrong
target for Aoyagi's mechanism.** Her mechanism is germ-level (Lemma 2 + Theorem 4 + monomial resolution);
`(∗_T1)` belongs to the repo's **Route A** (measure-theoretic *cover* / box-integral domination). The
repo's own route adjudication (`theory/aoyagi-2023-reproduction/verify-r1-route-adjudication.md`,
2026-06-24) already records two facts that make the steer sharp:

1. A naive **measure-preserving chart recursion is UNSOUND** (dimension-conserving → telescopes to
   `ambient/2 = 4` for `(2,2,2)`, contradicting the true `3/2`) — RETRACTED. `(∗_T1)` is *not* this
   (it carries the `ab/2` blow-up charge, so it is a genuine domination, not measure-preserving) — but
   the retraction is why Route A must fight for descent (hence the shell-`j` partial floor) and why the
   incidence wall appears.
2. **Route B — the same-point squeeze** `c₁Φ ≤ F ≤ c₂Φ ⇒ rlctAtOn F = rlctAtOn Φ` (Lean lemma
   `rlctAtOn_squeeze`, proven) computes `rlctAtOn` **additively at germ level, with no chart and no
   measure Jacobian**. Its residual atom `hnode` is exactly "after the measure-preserving det-1
   GL-straightening (Aoyagi's Lemma 2) the node loss is in Schur form near the deepest point" — a
   **germ-level, local, explicit** statement, and precisely Aoyagi's block-elimination.

My corner check is a direct instance of Route B working: at `(2,2,3)` the straightening is **exact**
(`F − Φ = 0` with `Φ = x²+y²+(β²+γ²)(t₂²+t₃²)`; `/tmp/aoyagi_mining/corner_reduction.py`), `rlctAtOn Φ =
2 = T1`, and it splits additively as pivot (`x²`, the `ab/2` charge) + Schur residual (the reduced
`1×3` chain, `3/2`). The incidence "degeneracy" is just the Schur residual, handled **at the same
point** — no box integral, no uniform-in-`z` estimate, so **N1/N2 do not arise**. Theorem 4 is what
licenses staying at the germ: the region RLCT equals the deepest-point RLCT.

**Recommendation.** Do not commission N1/N2 (the incidence estimate + weighted-comparison) to rescue
Route A. Route B's residual (`hnode` = Aoyagi's Lemma-2 germ Schur straightening for general `M`, +
additive assembly) is (a) strictly more tractable, (b) exactly what Aoyagi's paper actually supplies,
and (c) free of the moving-family / singular-`P` / coupled-divisor region hazards. If whole-chain
finiteness (not the peeling step) is all that is wanted, Codex's Q4 route — formalise Aoyagi's full
global resolution (`diag(b)`, Cases 1(1)/1(2)/2, chart Eqs (1)–(5), all Jacobians) — also avoids
`(∗_T1)`, but is far heavier than the squeeze.

---

## Close (firmest result / most likely to break it / next step)

- **Firmest result (obstruction, exact scope).** Aoyagi's proof contains **no** layer-peeling
  integral-domination; her degeneracy handling is a **germ-level** ideal equality (Lemma 2 Schur
  elimination) plus a **global** monomial resolution, with **Theorem 4** collapsing the region to the
  deepest germ so no box integral is ever needed. `(∗_T1)` is therefore a genuinely different,
  region-level statement; the germ→region gap (N1 uniform incidence/pushforward incl. singular-`P` and
  rank-minor strata; N2 coupled-`b`→scalar `commonDivisor`) is new mathematics. The `(2,2,3)` corner is
  exact-certified *consistent* with `(∗_T1)` (finite below `T1`, tight at `T1=2`, additive `½+3/2`),
  and is a direct instance of the germ **squeeze** (Route B) computing the same value with no incidence
  estimate.
- **Most likely thing to break this.** If someone exhibits a **base-preserving fibrewise** reading of
  Aoyagi's blow-up — i.e. shows her `u_{s,k}` charts can be reorganised so the base `z` variables are
  never blown up jointly with the fibre — then N1 would reduce to bounded labour and the verdict softens
  to "Aoyagi gives `(∗_T1)` up to bookkeeping." I saw no such reorganisation (her `t^{(s)}_{S,k}`
  profile couples all layers), and Codex independently judged the mixing irreducible; but I did not
  *prove* non-existence, so this is the crack to watch.
- **Next step that settles the open part.** Formalise **Route B's `hnode`** for general `M`: state
  Aoyagi's Lemma-2 straightening as the germ squeeze `c₁Φ ≤ F ≤ c₂Φ` with `Φ =` pivot quadratic + Schur
  residual, uniform `c₁,c₂>0` on a deepest-point neighbourhood, and check the additive close against
  `½·minAdm` via the keystone. If that germ squeeze goes through (the `(2,2,3)` and a corank-2 `(3,3,4)`
  node are the two exact test cases — the first is `F=Φ` exactly, the second exercises the coupled
  residual), the incidence wall is retired without N1/N2. Failing that, N1 is the irreducible new
  analysis and should be scoped as a standalone lemma before any further Route-A Lean build.

## Scope / separation of levels
- Levels kept distinct: the **germ RLCT equality** (Lemma 1, a number at a point) vs the **region
  integral domination with a uniform constant** (`(∗_T1)`) are different throughout — the entire verdict
  rests on that distinction. The **codimension** additivity (`Mval`) and the **RLCT** `½·codim` are the
  reproduction's/paper's established inputs, not re-litigated here; the `rlct = ½·codim` reading still
  rides on the cited Aoyagi/Watanabe analytic equality.
- Definition 3 is defective (reproduction `verify-def3-underspec.md`); I used `Mval_min` (= codim) as
  the primitive everywhere, consistent with the corrected reproduction.
- Exact algebra only; no floats used for any threshold. Scripts + Codex prompt/answer archived under
  `/tmp/aoyagi_mining/` (copy into the expedition thread if this is folded in).
