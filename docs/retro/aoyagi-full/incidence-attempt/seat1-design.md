# Seat-1 (witness) design cert — the partial-shell transverse-Schur incidence estimate (∗_T1)

**Seat:** pen-and-paper (witness), aoyagi-full retro, `incidence-attempt`. **Date:** 2026-07-14.
**Scope:** adjudicate (∗_T1) — the terminal analytic brick of aoyagi-full — in full detail, with exact
verification at the binding anchors. **No Lean, no expedition-file writes.** Scripts sit beside this file
(`verify_*.py`); all load-bearing algebra is exact (sympy/rational) or a sublevel-volume RLCT computation.
Monte-Carlo of the *singular integrand* is used only as a discarded guide (it undersamples deep strata —
noted at each use).

---

## 0. VERDICT (honest)

- **(∗_T1) is TRUE as an inequality** (LHS finite for `c'<T1`, a finite `C_j` exists). **Not refuted.**
- **On a non-circular PROOF: one wall dissolved, a second, distinct wall found and localized.**
  - **Advance [FACT].** A coordinatization makes `freedSchurLoss` the exact sum `‖U R + W X‖² + ‖W Y‖²`. It
    **dissolves the wall the prior expedition hit** — the *decoupled* head-split route (isolate the pivot
    block, peel `C` separately) provably tops out at `ab/2 + u·ρ/2 < T1` for `M₂>M₁` chains, and the binding
    corner `(2,2,3)` is `M₂>M₁`. Keeping `[P;C]` coupled recovers the missing `au/2`. Corner RLCTs `= T1`.
  - **New wall [FACT], for the mixed-degeneration cuts `b<j`** (required for any chain with `r≥3`). There the
    inner integral `Ψ(z) → ∞` as a single `σ_min(Q_p)→0` (with `‖Q_p‖_F` floored), while the comparator is
    `O(1)` there. I confirmed this is **not** a route artefact: I read the Lean defs and the comparator
    integrand is `commonDivisor(z)²·frobSq(prod M' z)` with `commonDivisor = ∏_ℓ|z_ℓ|^{kℓ}` (a monomial,
    vanishing only on coordinate hyperplanes) and `frobSq(prod M' z) = ‖Q_p‖_F²` (vanishing only on *full*
    degeneration). **Neither factor tracks `σ_min(Q_p)`.** So the stated comparator is provably too weak to
    dominate the LHS on the `z`-region where shell-`j` (`b<j`) actually lives (partial `Q_p`-degeneration).
    The RLCT of the mixed stratum is `T1` for `σ_min>0` but drops to `3<T1` in the limit — verified with `X`
    (the in-plane part) integrated, so not an `X=0` artefact.
- **Net judgement.** The coordinatization is a genuine unlock and removes the decoupled wall. But **(∗_T1) as
  stated — domination by `∫_z(commonDivisor²‖Q_p‖_F²)^{−q}` — is NOT provable non-circularly at the `b<j`
  cuts**: the RHS does not see the `σ_min(Q_p)→0` singularity that drives the LHS. Closing it needs a
  **strengthened comparator** that tracks `σ_min(Q_p)` (a `det`-type / reduced-RLCT factor), OR an auxiliary
  lemma bounding `∫_z Ψ` via the small-singular-value density of the reduced product `prod M' z`. Both are
  genuine additional mathematics; the stated brick, unchanged, does not close for `r≥3`.

This corrects an earlier optimistic read of my own ("LABOUR, pointwise with room"); §4b/§5 is where I caught
and then pinned it.

---

## 1. The coordinatization (FACT — verified exactly)

Fix `z`. `Qhat` (`u×n`) orthonormal basis of `row Q_p`, `Vhat` completion, `O=[Qhat;Vhat]` orthogonal.
`Q_p=R Qhat` (`R u×u` invertible, sing. vals = `Q_p`'s, `‖Q_p‖_F=‖R‖_F`); `Q_b=X Qhat+Y Vhat`,
`X=Q_b Qhat^T`, `Y=Q_b Vhat^T`. With `U=[P;C]` (`M₀×u`), `W=[B12;Γ']` (`M₀×b`):

    freedSchurLoss = ‖U R + W X‖² + ‖W Y‖²                                          (COORD)
    Q_b(I−Π_p)Q_b^T = Y Y^T   (transverse Schur = YY^T, exactly)

- **[FACT]** (COORD) and the Schur identity hold symbolically (`verify_proj.py`, `verify_more.py`:
  `u=a=b=1,n=3` and `u=2,a=1,b=2,n=4` over an exact rational orthonormal frame). Completing the square in the
  full `W` gives constant term `‖U Q_p(I−Π_b)‖²`.
- The substitution `V := U R + W X` (bijective in `U`, Jacobian `|det R|^{−M₀}`) gives
  `freedSchurLoss = ‖V‖² + ‖W Y‖²` with `V` and `(W,Y)` **disjoint coordinate groups**. This absorbs the
  `WX` cross-term (the coupling that blocked K4) into `V`, and turns the incidence into the fixed-locus
  statement "`Y` drops rank".

---

## 2. Corner certificates (RLCT = `T1`) — FACT

`minAdm(M)=min_r[(M₀−r)(M₁−r)+rM₂]` for `L=0`; `T1=½minAdm`. `(verify_thresholds.py`,
`verify_corner_223.py`, `verify_rlct_exact.py`.)

- **(i) Binding corner `M=(2,2,3), u=j=1, t*=0` (argmin tie, zero slack).** In coordinates
  `loss=ξ²+η²+(B²+Γ'²)(t₂²+t₃²)`. By disjoint-variable additivity of the sublevel exponent
  `λ` (`Vol{f<ε}~ε^λ`): `λ(ξ²+η²)=1` and `λ((B²+Γ'²)(t₂²+t₃²))=1` (the latter with `Vol~ε·log(1/ε)`, checked:
  `Vol/(ε log 1/ε)` flat). So **`λ = 2 = T1`**, `∫loss^{−c'}<∞ ⇔ c'<2`, log-divergent at `2`. Cross-check:
  branch A (`t=0`) rank-4 nondeg Hessian (det 64) → `c'<2`; branch B (`B=Γ'=0`) → `∫ρ^{3−2c'}dρ` twice →
  `c'<2`. ✔
- **(ii) Non-argmin `M=(4,4,4), u=3, t*=2` (`M₂=M₁`).** Regime-I threshold `13/2 > T1=6`: shell-1 excludes
  the binding rank-2 stratum, so on-shell finiteness holds past `T1`; the estimate at `c'<6` never needs the
  false `T2=6.5`. ✔
- **(iii) Corank-2 `M=(4,4,8), u=2, j=2, t*=0` (`M₂>M₁`).** After peeling the `D₁=M₀(M₁−j)=8`
  O(1)-quadratic directions, the reduced integral `∫∫ τ₁⁴τ₂⁴|τ₁²−τ₂²|(τ₁²‖W₁‖²+τ₂²‖W₂‖²)^{−s}` has an exact
  change of variables `W_i=w_i/τ_i` (valid: `(n−u)−b−M₀=0>−1`) giving finiteness `⇔ c'<M₀M₁/2=8=T1`. **The
  Vandermonde does not break it**; corank-1 and corank-2 both hit `T1` exactly. ✔

These confirm the *coupled* object has RLCT `= T1` (at these anchors), i.e. finiteness of (∗_T1)'s LHS to
`c'<T1`. (INFERENCE: `= T1` at binding chains, `> T1` at non-argmin cuts, everywhere `≥ T1`; consistent with
the banked off-shell stratification.)

---

## 3. The middle lemma (minimized) — what a formaliser would prove IF the descent closes

Under `V := U R + W X`, the disjoint split gives `λ(coupled) = M₀u/2 + λ_incid`, so the single new fact is

    **(INC)   λ( ‖W Y‖²  restricted to  Y ∈ shell-j )  ≥  ½·minAdm(M) − M₀u/2 ,**

equivalently, for the fixed positive weight `w=‖V‖²` produced by integrating the `V`-block,

    ∫_{A_cor∈S_j} ∫_{W box} ( w + ‖W Y‖² )^{−q} dW dA_cor  ≤  K_{j,q}·w^{−(q−λ_incid)},  Y=A_cor Z Vhat^T.

Because the weight is now `A_cor`-free, **this is a K4-shaped object** (deep floor `ZZ^T⪰ε²U_sU_s^T`, applied
to `Z Vhat^T`, plus the shell restriction). Verified at the corners (§2). *This lemma governs finiteness; the
descent needs more — see §4b/§5.*

---

## 4. The two obstructions, both verified exactly

### 4a. The DECOUPLED-route dead-end — FACT, decorrelated (this is *why* the expedition walled)

If one peels `C` into a separate corank weight and integrates the **isolated** pivot block
`∫_{P,B12}‖[P|B12] hsQ‖^{−2c''}`, that block is `u` copies of `x↦x·hsQ`, rank `u·ρ`,
`ρ=rank(hsQ)=min(M₁,M₂,…,M_last)`; its RLCT is `u·ρ/2` (verified `(3,3,4)@u=1`: `λ=1.505≈3/2`). The route thus
reaches only `c' < ab/2 + u·ρ/2`. Shortfall `T1 − (ab/2+uρ/2)` (`route_gap.py`):

| chain / cut | `M₂>M₁`? | `T1` | decoupled reach | shortfall |
|---|---|---|---|---|
| `(2,2,3)@u=1` (binding) | yes | 2 | 3/2 | **+1/2** |
| `(3,3,3)@u=2` | no | 7/2 | 7/2 | 0 |
| `(4,4,4)@u=3` | no | 6 | 13/2 | −1/2 (margin) |
| `(4,4,8)@u=2` | yes | 8 | 6 | +2 |
| `(3,3,4)@u=1` | yes | 4 | 7/2 | +1/2 |

The shortfall is `>0` exactly on `M₂>M₁` chains, and equals the `au/2` the coupled `V`-block keeps but the
decoupled route discards (it splits `C` off the pivot). **The binding corner `(2,2,3)` is `M₂>M₁` with
shortfall `1/2`, so the decoupled route provably cannot prove (∗_T1) there.** A fresh `xhigh` Codex consult
independently located the same ceiling `u·ρ/2` and the `M₂≤M₁` decoupled-safe scope, and noted "no
contradiction — the true RLCT is delivered by the other branch." **Correction to Codex's fix:** gating the
lemma by `M₂≤M₁` would *delete the binding corner* — the right fix is the coupled route, which carries no
`M₂≤M₁` restriction. This obstruction is **dissolved** by §1.

### 4b. The MIXED-STRATUM pointwise failure — FACT (the obstruction I could NOT dissolve)

Cuts with `b<j` (i.e. `j>(M₁−t*)/2`, the upper half of the legal `j`-range) force a small singular value
into `R`, not `Y`. Model this exactly on `M=(3,3,7), u=2, j=2, b=1, t*=0` (`T1=9/2`), at `X=0`:

    Ψ-integrand = ‖U₁‖² + μ²‖U₂‖² + τ²‖W‖²,   μ=σ_min(R)→0,  ‖R‖_F=√(1+μ²)→1 (FLOORED),  τ=‖Y‖ (shell).

`verify_R1_wall.py` (sublevel RLCT) + exact analysis:
- **`μ>0`:** all three blocks nondegenerate ⇒ RLCT `= 9/2 = T1`. (MC `3.73` at `μ=0.3`, undersampled-low.)
- **`μ→0`:** the box caps the freed `U₂` block (`∫_0^3 b^{1/2}(A+μ²b)^{−c'}db → A^{−c'}·const`, verified
  `verify_R1_crux.py`), collapsing it to a constant; the RLCT **drops to `3`** (the `∫_W` factor now binds at
  `c'<3`). (MC `≈2.7`, undersampled-low but the drop is unambiguous.)

Hence `Ψ(z) → ∞` as `σ_min(R)→0` for `c'∈(3, T1)`, while the comparator `(cd²‖Q_p‖²)^{−q}` — with
`‖Q_p‖²=‖R‖_F²→1` — stays `O(1)`. **So the pointwise-in-`z` bound `Ψ(z) ≤ C·(cd²‖Q_p‖²)^{−q}` is FALSE.** The
descent is inherently integrated: only the `z`-measure of `{σ_min(R)≈μ}` (which shrinks as `μ→0`) tames the
blow-up. (For `b≥j` cuts — e.g. the binding `(2,2,3)` — there is no mixed stratum and the pointwise route did
work: `Ψ~r^{2−2c'}log(1/r)` dominated by `r^{1−2c'}`, `verify_scaling.py`. The failure is specific to `b<j`.)

---

## 5. The deciding sub-statement — RESOLVED (against the clean route)

My draft rested the verdict on one question; I then read the Lean defs
(`RouteMSJLedger.lean:94`, `RouteMSJCornerComparator.lean:116`) and **settled it**:

> The comparator integrand is `decLoss = commonDivisor(e)(z)² · frobSq(prod M' z)`, with
> `commonDivisor(e)(z) = ∏_ℓ |z_ℓ|^{sharedDivisorExp e ℓ}` (a **monomial** in the deep coordinates) and
> `frobSq(prod M' z) = ‖Q_p(z)‖_F²`.

So the comparator vanishes only on the coordinate hyperplanes `{z_ℓ=0}` (via `commonDivisor`) and on the
*full* degeneration `{prod M' z = 0}` (via `frobSq`). **It does not track `σ_min(Q_p)`.** At a generic `z`
where `σ_min(Q_p)→0` but all `|z_ℓ|` and `‖Q_p‖_F` stay floored, the comparator is `O(1)` — and that is
exactly the `z`-locus on which shell-`j` (`b<j`) is supported (partial `Q_p`-degeneration: on shell-`j` with
`b<j`, `Q_p` must carry `j−b` small singular values, but `j−b<u`, so never all of `Q_p` — hence `‖Q_p‖_F`
floored). There `Ψ(z)→∞` (§4b) against an `O(1)` comparator.

**Conclusion: the stated (∗_T1) domination is NOT provable non-circularly for `b<j` cuts.** This is a genuine
wall, distinct from and additional to the (dissolved) decoupled-route wall.

**The fix, named precisely (this is the actual missing brick):** replace the RHS weight `‖Q_p‖_F²` by one
that tracks the *smallest* singular value — the natural candidate is a `det`-normalized / reduced-RLCT weight,
e.g. `commonDivisor² · (∏ σ_i(Q_p)²)`-type or the honest reduced-chain RLCT object whose singular locus is
`{rank Q_p < u}`, not just `{Q_p = 0}`. With such a comparator the `σ_min(Q_p)→0` singularity of `Ψ` is
matched and the integrated descent can close. Equivalently, supply the auxiliary lemma *"`∫_z Ψ(z)` over
`{σ_min(Q_p)<δ, ‖Q_p‖_F floored}` is finite for `c'<T1`"* directly, via the small-singular-value density of
`prod M' z` — DLN-specific input the current comparator does not carry.

**Escape hatch to check first (controller):** whether the shell **cover** actually requires `b<j` cuts, or
whether the head-split can always be taken at a `j≤b` cut (for which the clean coupled route of §1–§3 *does*
close — no mixed stratum, `Ψ(z)` bounded, verified for `(2,2,3)`). If `b<j` cuts can be avoided
architecturally, the wall is moot and the coordinatization suffices. If not, the comparator must be
strengthened as above.

---

## 6. Close

- **Firmest result.** The coordinatization `freedSchurLoss=‖V‖²+‖WY‖²` (exact) dissolves the decoupled
  head-split wall (the `M₂>M₁` / `u·ρ/2` ceiling — the reason the expedition stalled at the `M₂>M₁` binding
  corner `(2,2,3)`). Corner RLCTs `= T1` confirmed exactly at `(2,2,3)`, corank-2 `(4,4,8)`, non-argmin
  `(4,4,4)@u=3`. For `j≤b` cuts the coupled descent closes (`Ψ` bounded, `(2,2,3)` verified). (∗_T1) is TRUE
  as an inequality throughout.
- **The wall, precisely located and confirmed.** For `b<j` cuts (needed when `r≥3`), `Ψ(z)→∞` as
  `σ_min(Q_p)→0` with `‖Q_p‖_F` floored, while the **stated** comparator `commonDivisor²·‖Q_p‖_F²` is `O(1)`
  there (both factors verified from the Lean defs — a monomial and a Frobenius norm, neither tracking
  `σ_min`). So the stated domination cannot be proven non-circularly at `b<j`.
- **Next steps that settle it.** (a) **Controller:** decide whether the shell cover forces `b<j` cuts (if the
  head-split can always sit at `j≤b`, the wall is moot and §1–§3 finish the job). (b) If `b<j` is
  unavoidable: **strengthen the comparator** to a `σ_min(Q_p)`-tracking (`det`/reduced-RLCT) weight, or add
  the auxiliary small-singular-value-density lemma for `prod M' z` (§5). (c) Formalise the coupled route of
  §1–§3 for the `j≤b` cuts regardless — that part is clean, coordinatization-verified labour, and strictly
  better than the decoupled architecture.

**Strategic note for the controller.** Two difficulties were tangled under "the wall": (1) the decoupled-route
ceiling `u·ρ/2 < T1` on `M₂>M₁` — **dissolved** by coupling the full `U=[P;C]` block via `V=UR+WX`; (2) the
`b<j` mixed-stratum failure — **a real wall for the stated comparator**, because that comparator tracks only
`‖Q_p‖_F` (full degeneration), not `σ_min(Q_p)` (partial), and shell-`j`(`b<j`) lives exactly on the
partial-degeneration `z`-locus. Do **not** adopt Codex's `M₂≤M₁` scope (it deletes the binding corner). The
substantive open brick is now (2): a `σ_min`-aware comparator, or a proof that `b<j` cuts are avoidable.
