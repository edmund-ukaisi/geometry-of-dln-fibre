# Cert #104 — the general per-node blow-up presentation for the binding `hstep`

> **RESOLVED by `cert-104b-two-strata-cover.md` (route (ii)).** The obstruction below is real and
> precisely located, but it was an artifact of reading ONLY the core stratum (with `nReg := n`) and
> dropping the outer `D₀` exceptional divisor. The sound uniform `hstep` is the **two-strata cover**
> `rlctAtOn(dlnLoss M 0) = min{mk/2, rlctAtOn(core)}`, `rlctAtOn(core) = n/2 + child` — see
> `cert-104b`. This document stands as the derivation of the blow-up algebra + the obstruction
> diagnosis that motivated the cover.

**Seat.** pen-and-paper (witness), DLNFibre aoyagi-full, task #104 (the R1 geometric heart).
**Method.** exact symbolic algebra (sympy 1.14) + exact-integer combinatorics + a decorrelated
xhigh Codex consult. No Lean. **Verification script:**
`sympy/node_blowup_cert_104.py` (all checks pass). **Codex artifacts:**
`codex/node-blowup-104-{prompt,answer}.md`.

> **Headline (honest).** The general per-node blow-up presentation is derived and exact-verified.
> The single-pivot blow-up `A = y₀·Â`, the `y₀²·core` factorization, the `|Jac| = y₀^{mk−1}`
> Jacobian, and the general `m×k` Schur normal form all generalize from the `(2,2,2)` anchor and
> are sympy-verified for many shapes. **But the soundness condition the briefing flagged FAILS in
> general:** the `y₀^{mk−1}` exceptional-divisor power's contribution is `mk/2`, which equals the
> required node increment `nReg/2` **only in a restricted regime** (`R = 0 ∧ mk ≤ n`). For a large,
> descent-reachable class of nodes (smallest `(2,2,4)`), the increment `nReg/2` is a **value-side
> difference of two branches, NOT the ratio of any single divisor of `F`**. This is a genuine
> obstruction to the uniform "single-pivot `flatCore` + `smoothBlockSplitForm` squeeze with
> `nReg := n`" route — and it is precisely the regime that the existing `(2,2,2)`/`Case222NodeDescent`
> anchor never exercises. The sound route is the **`min`-of-two-branches Jacobian-weighted threshold**,
> which I make explicit below; the per-node descent step still holds **numerically**, but its
> Lean realization needs `nReg = min{mk−R, n}` and the `min` structure, not a clean `nReg`-Morse block.

---

## 0. Node model (matching the `(2,2,2)` anchor cert)

At a deepest-layer pivot node, `dlnLoss M 0 = ‖A · B‖²_F` at the all-zero deepest point, where:

- `A` = the deepest pivot layer (layer 0), size `m × k`, `m = M¹`, `k = M²`.
- `B` = the product of the remaining chain layers, size `k × n`, `n = M^{L+1}`. Near the deepest
  point `B` is treated as a **generic** `k × n` matrix (the deeper layers are the recursion's child,
  handled separately by the `ReducedTransport` det-1 reindex).

The `schurState` reduction is `red(M) = (M¹−1, M²−1, M³, …)`: the two pivot widths each drop by 1,
the tail `n` is **fixed**. Write `R := minAdm(red(M))` (the child's `2·rlct`).

The per-node descent step the binding R1 spine consumes (`RouteMNodeDescent.descentStep`) is

$$
\operatorname{rlctAtOn}(\texttt{flatCore})(0,0) \;=\; \tfrac{nReg}{2} \;+\; \operatorname{rlctAtOn}\!\big(\texttt{dlnLoss}(red M)\,0\big)(0),
\qquad nReg := \operatorname{minAdm}(M) - \operatorname{minAdm}(red M).
$$

`nReg = minAdm M − minAdm(red M)` is the **value-side** count (`RouteMNReg.nRegOf`); the arithmetic
identity `minAdm(red M) + nReg = minAdm M` is already PROVEN in Lean
(`minAdm_schurStateRed_add_nRegOf`). Telescoping the step down the `schurState` chain to a leaf gives
`rlct = ½·Σ nReg_k = ½·minAdm M`.

---

## 1. The blow-up and the `y₀²·core` factorization (VERIFIED, V1)

Single-pivot chart `φ₁` (pivot = the `(0,0)` entry of `A`, call it `y₀`):

    a₀₀ = y₀,    a₀ⱼ = y₀·uⱼ  (j≥1),    aᵢ₀ = y₀·vᵢ  (i≥1),    aᵢⱼ = y₀·wᵢⱼ  (i,j≥1)
    ⇒  A = y₀·Â,   Â = [[1, uᵀ],[v, W]]   (m×k, top-left entry exactly 1)

`B` passes through unchanged. Then, sympy-verified exactly (V1) for
`(m,k,n) ∈ {(2,2,2),(3,2,3),(3,3,2),(2,3,3),(2,2,5),(2,2,4),(1,1,2),(1,1,4),(4,3,2),(2,4,3),(3,3,3)}`:

$$
F\circ\varphi_1 \;=\; \|A\cdot B\|^2 \;=\; y_0^{\,2}\cdot \texttt{core}, \qquad \texttt{core} = \|\hat A\cdot B\|^2.
$$

**The Jacobian.** `φ₁ : (y₀, u, v, W) ↦ A`. The `(0,0)` entry contributes `∂a₀₀/∂y₀ = 1`; each of
the **other `mk−1` entries** is `y₀·(coord)`, contributing a factor `y₀`. Hence

$$
\boxed{\;|\!\det J_{\varphi_1}| = y_0^{\,mk-1}\;}
$$

(exact, V1; matches the `(2,2,2)` cert's `y₀³` since `mk−1 = 3`). This is the genuine exceptional-divisor
power of the blow-up of the codim-`mk` center `{A = 0}`.

---

## 2. The general `m×k` Schur normal form (VERIFIED, V2)

Partition `Â = [[1, c],[b, D]]` with `c = uᵀ` (`1×(k−1)`), `b = v` (`(m−1)×1`), `D = W`. Schur-eliminate
the unit pivot block. With `Bred := B[1:,:]` (the lower `(k−1)×n` block of `B`):

    Erow := B[0,:] + u·Bred                  (1×n;  row 0 of Â·B — the pivot-row product)
    S    := W − v·u                          ((m−1)×(k−1);  the Schur complement D − b·c)
    SBred := S·Bred                          ((m−1)×n;  the reduced-core rows)

Then, sympy-verified exactly (V2) for all the shapes above:

$$
\texttt{core} \;=\; \sum_{j=1}^{n} \texttt{Erow}_j^{\,2} \;+\; \sum_{i=1}^{m-1}\sum_{j=1}^{n}\big(v_i\,\texttt{Erow}_j + (S\,B_{\mathrm{red}})_{ij}\big)^2.
$$

This is exactly the `(2,2,2)` cert's Schur form generalized: `Erow` the `nReg_struct = 1·n = n`
pivot-row squares, `b = v` the `(m−1)` lower rows, `S` the `(m−1)×(k−1)` Schur complement. Near the
deepest point `v → 0`, so `core ≈ ∑_j Erow_j² + ‖S·Bred‖²`.

**The reduced core (VERIFIED shape, V3).** `‖S·Bred‖² = ∑_{i,j}(S·Bred)_{ij}²` is the squared-Frobenius
product loss of the `(m−1)×(k−1)` matrix `S` against the `(k−1)×n` matrix `Bred` — i.e. exactly
`dlnLoss(red M) 0` with `A' = S`, `B' = Bred`. (At `(2,2,2)`: `S = y₃−y₂y₁` is `1×1`, `Bred = [x₆,x₇]`,
`‖S·Bred‖² = (y₃−y₂y₁)²(x₆²+x₇²) = dlnLoss(1,1,2) 0` — the anchor's `G²`.)

**The change of variables, explicit.** `Erow_j = B[0,j] + (u·Bred)_j` is, at fixed `(u, Bred)`, a
det-1 affine shear of the free top-row coordinate `B[0,j]`. So `{Erow_j}_{j=1}^n` are `n` independent
smooth coordinates (a unipotent, measure-preserving reparametrization of `B[0,:]`), and they do **not**
appear in `‖S·Bred‖²` (which uses only `u, v, W, Bred`). This det-1 `Erow`-shear is the
**`ReducedTransport` measure-preserving part** — it is Jacobian-1 and must be kept SEPARATE from the
blow-up's `y₀^{mk−1}` Jacobian (the briefing's instruction; they are different objects).

---

## 3. The RLCT bookkeeping — the `min`-of-two-branches threshold (VERIFIED, V4/V5)

`rlctAtOn F 0 = weightedThreshold F 1 {0}` (`Rlct.lean`). Transporting through the **non-MP** blow-up
`φ₁` puts the Jacobian into the integrand as a weight (the SOUND weighted-cover route; this is exactly
the route `RouteMO1Bridge` says is required and the MP-chart `dlnLoss_chart_squeeze_descent`/#148 lacks):

$$
\operatorname{rlctAtOn} F\,0 \;=\; \sup\Big\{ c' : \int_{\text{nbhd } 0} |y_0^2\,\texttt{core}|^{-c'}\, y_0^{\,mk-1}\, d\mathrm{vol} < \infty \Big\}.
$$

The integrand is `y₀^{mk−1 − 2c'}·core^{−c'}`. With `core ≈ ∑_{j=1}^n Erow_j² + ‖S·Bred‖²` a
normal-crossing form in the disjoint coordinate groups `{y₀} ⊔ {Erow_j} ⊔ {child coords}`, the
threshold factorizes into a **min over the binding group**:

- **`y₀`-axis (the exceptional divisor `D₀`):** `∫₀ y₀^{mk−1−2c'} dy₀ < ∞ ⇔ mk−1−2c' > −1 ⇔ c' < mk/2`.
  The divisor `D₀` has monomial data `(k_mon, h) = (1, mk−1)`, ratio `(h+1)/(2k_mon) = mk/2`.
- **`Erow`-Morse + child block:** `n` independent smooth squares (each `½`) plus the child threshold
  `R/2`, so `c' < n/2 + R/2 = (n+R)/2`.

Both must converge, so

$$
\boxed{\;\operatorname{rlctAtOn} F\,0 \;=\; \tfrac12\,\min\{\,mk,\; n+R\,\}\;}
$$

and this **equals `½·minAdm(M)`** — sympy-verified over `(m,k,n) ∈ 1..7 × 1..7 × 1..11` (V4, V5),
since the `L=2` `minAdm` recursion is exactly `minAdm(m,k,n) = min{mk, n + minAdm(m−1,k−1,n)}`. Hence

$$
nReg \;=\; \operatorname{minAdm}(M) - R \;=\; \min\{\,mk - R,\; n\,\} \quad(\text{V4, verified}).
$$

---

## 4. The soundness verdict — where `y₀^{mk−1}` IS / IS NOT `nReg/2` (VERIFIED, V6)

The briefing's load-bearing condition: *the pinned `y₀^?` power must be the exceptional-divisor power
whose contribution IS `nReg/2`; the squeeze lower bound must come FROM that divisor power.* Testing
`mk/2 = nReg/2` exactly over the range (V6):

$$
\underbrace{mk/2 = nReg/2}_{\text{divisor realizes the increment}} \iff \big(R = 0 \;\wedge\; mk \le n\big).
$$

So the `y₀^{mk−1}` divisor contributes `nReg/2` **only** when the child is degenerate (`R = 0`, a
leaf-adjacent node) and the tail is wide enough that `D₀` binds. Two regimes for the descent:

| regime | condition | binding branch | `nReg` | single-pivot squeeze with `nReg := n` |
|---|---|---|---|---|
| **(a) REGULAR** | `n ≤ nReg` (i.e. `n + R ≤ mk`) | core branch `(n+R)/2` | `nReg = n` | **SOUND** — the `n` `Erow` squares ARE the fresh Morse block; `D₀` (ratio `mk/2`) is NON-binding. This is the `(2,2,2)` anchor regime. |
| **(b) WIDE-TAIL** | `n > nReg` (i.e. `n + R > mk`) | divisor `D₀` `mk/2` | `nReg = mk − R < n` | **UNSOUND** — `∑_{j=1}^n Erow²` over-counts; `rlctAtOn(∑^n Erow² + G²) = n/2 + R/2 > mk/2 = rlct`. |

Range census (V6, `1..7²×1..11`): **339 REGULAR nodes, 200 WIDE-TAIL nodes.**

**The obstruction, precisely.** In the WIDE-TAIL regime with **positive child** (`R > 0`), the increment

$$
\tfrac{nReg}{2} = \tfrac{mk - R}{2} = \underbrace{\tfrac{mk}{2}}_{D_0\text{ ratio}} - \underbrace{\tfrac{R}{2}}_{\text{child rlct}}
$$

is a **difference of the divisor ratio and the child RLCT** — it is **not the ratio of any single
divisor of `F`** (if it were, the RLCT would be `≤ nReg/2 < mk/2`, contradicting `rlct = mk/2`). The
smallest such node reachable on a descent is **`(2,2,4)`** (`nReg = 3`, `R = 1`, `mk = 4`: `mk/2 = 2 ≠
nReg/2 = 3/2`; verified). These nodes are **unavoidable**: the `schurState` descent fixes `n` and
shrinks `m,k`, so every chain ends at a wide-tail node (even `(2,2,2)`'s child `(1,1,2)` is wide-tail —
but there `R = 0`, so `D₀` binds soundly at `nReg/2 = 1/2`).

**Why this is the #148-vacuity lesson, sharpened.** #148 (`dlnLoss_O1_descent`) tried a
measure-preserving chart `χ` with the squeeze `c₁·Φ ≤ dlnLoss∘χ ≤ c₂·Φ`, `Φ = ∑^{nReg}Eᵢ² + G²` — and
that is unsatisfiable for the raw loss (rank-0 Jacobian). The present analysis shows the SOUND
post-blow-up `core` IS squeezable by `Φ`, but **only with `nReg := n`**, and `rlctAtOn(Φ) = n/2 + R/2`
— which is the TRUE RLCT only in the REGULAR regime. Feeding `IsSchurStraightenSqueeze` with `nReg := n`
in the wide-tail regime gives a green-but-WRONG descent step (over-counts). The squeeze does NOT see the
`y₀^{mk−1}` Jacobian cap; that cap lives in the weighted-cover transport, which the `smoothBlockSplitForm`
squeeze (no Jacobian, `GeneralR1Recursion.lean`) deliberately omits.

---

## 5. What a Lean formaliser can transcribe — and what it must NOT

**SOUND to transcribe (the REGULAR regime, `n ≤ nReg`, where the existing machinery is correct):**
- The blow-up `A = y₀·Â`, `F∘φ₁ = y₀²·core`, `|Jac| = y₀^{mk−1}` (V1) — exact, dimension-uniform.
- The general `m×k` Schur normal form `core = ∑_j Erow_j² + ∑_{i,j}(v_i Erow_j + (S·Bred)_{ij})²` (V2)
  — the general `IsSchurStraightenSqueeze.squeeze`-producer obligation `flatCore − Φ ∈ ideal(Erow)`.
- `‖S·Bred‖² = dlnLoss(red M) 0` (V3) — the general `redCore_eq` / `ReducedTransport.hredCore`.
- The `Erow`-shear `Erow_j = B[0,j] + (u·Bred)_j` as the det-1 MP `ReducedTransport` reindex (Jacobian 1).
- With `nReg := n` in the REGULAR regime, `RouteMNodeDescent.descentStep` is SOUND and gives
  `n/2 + rlct(child)` = the true RLCT.

**MUST NOT do (the obstruction):**
- Do **not** feed `IsSchurStraightenSqueeze` with `nReg := n` (the `Erow` count) at a WIDE-TAIL node —
  it over-counts. The contract's `nReg` must be `minAdm M − minAdm(red M) = min{mk−R, n}` (the
  value-side `nRegOf`), which equals `n` only in the REGULAR regime.
- Do **not** claim the `y₀^{mk−1}` divisor "delivers `nReg/2`" as a uniform soundness story — it
  delivers `mk/2`, which is `nReg/2` only when `R = 0 ∧ mk ≤ n`.

**The honest path for the general wide-tail node (the genuine remaining gap):** the per-node step
`rlctAtOn F 0 = nReg/2 + rlct(child)` holds, but its sound proof in the wide-tail regime is the
**`min`-of-two-branches Jacobian-weighted threshold** `rlctAtOn F 0 = ½·min{mk, n+R}` (V5), NOT a
`smoothBlockSplitForm`-with-`nReg=n` squeeze. A faithful general Lean `flatCore`/squeeze would need
either (i) a `nReg`-dependent presentation that exposes only `nReg = min{mk−R, n}` smooth directions
plus the `D₀` divisor cap, or (ii) to carry the `min` explicitly via the weighted-cover transport
(`weightedThreshold F 1 = weightedThreshold (F∘φ₁) y₀^{mk−1}`) with the normal-crossing additivity of
the threshold across `{y₀} ⊔ {Erow} ⊔ {child}`. This is strictly more than the `(2,2,2)` anchor's
machinery, which only ever runs in the REGULAR regime.

---

## 6. Cross-check against the divisor-soundness witness

The banked `divisor-binding-{prompt,answer}.md` witness asked whether the FIRST single-layer blow-up
divisor can bind below the downstream minimum. Its (re-run, `T₀ = (0,…,0)`) finding: the trivial
center `T₀` has `Mval = mk`, binds (is the strict unique minimizer) **iff every tail width `≥ M¹+M²`**.
That is exactly the WIDE-TAIL condition here (`D₀ = T₀`-stratum divisor, ratio `mk/2`, binds when the
tail is large). **Consistent:** my V6 obstruction (`D₀` binds, increment `≠` divisor ratio) is the same
phenomenon the divisor-binding witness flagged — the first/deepest divisor genuinely binds in the
wide-tail regime, and the naive per-node descent reading is unsound there. The present cert pins the
exact boundary (`R = 0 ∧ mk ≤ n` for divisor-realizes-increment) and the exact sound value
(`½·min{mk, n+R}`).

---

## 7. Status summary

- **Proved/Verified (exact):** the single-pivot blow-up, `y₀²·core`, `|Jac| = y₀^{mk−1}`, the general
  `m×k` Schur normal form, `‖S·Bred‖² = dlnLoss(red M) 0`, the `min` threshold `½·min{mk,n+R} = ½·minAdm`,
  the recursion `nReg = min{mk−R, n}`, and the soundness boundary `mk/2 = nReg/2 ⇔ (R=0 ∧ mk≤n)` — all
  in `sympy/node_blowup_cert_104.py`, all passing; decorrelated-confirmed by xhigh Codex.
- **Obstruction (precise, reported):** the uniform "single-pivot `flatCore` + `smoothBlockSplitForm`
  squeeze with `nReg := n`" route is UNSOUND at wide-tail-with-positive-child nodes (smallest `(2,2,4)`),
  which are unavoidable on descents. The `y₀^{mk−1}` divisor contributes `mk/2`, not `nReg/2`; the
  increment is a two-branch value difference. The sound general route is the `min`-of-two-branches
  Jacobian-weighted threshold.
- **What this de-risks:** the REGULAR-regime general node (`n ≤ nReg`) — the `(2,2,2)`-class — is fully
  derived and transcribable with `nReg = n`. The WIDE-TAIL regime needs the `min`/weighted-cover
  presentation; flagged here so a formaliser does not transcribe the over-counting `nReg=n` squeeze.
