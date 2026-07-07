# `sjJointResolution` — design certificate (pen-and-paper, aoyagi-full)

**Seat:** pen-and-paper (adjudicate one truth-value; exact algebra; decorrelated Codex). **Target:**
`sjJointResolution` (`RouteMSJResolution.lean:797`, branch `origin/genm-sjbpeel`), the last analytic
sorry of the general-`L` R1-UPPER `(S,J)`-peel. Statement: under the strong IH (box-finiteness for
every one-shorter chain), for `1 ≤ t ≤ min(M₀,M₁)` and `c' < minAdm M / 2`, the RAW per-`(t,ρ,κ)`-chart
peeled integral `gammaPeelIntegral M t ρ κ c' < ⊤`, where (re-scoped def, confirmed exact against
branch)

    gammaPeelIntegral M t ρ κ c' = ∫_{A'∈paramsBoxM (tailChain M) 1} ∫_{A0∈matBox(M₀)(M₁)1 ∩ pivotChart ρ κ}
                                     ofReal( frobSq(A0 · prod(tailChain M) A')^{−c'} ).

---

## VERDICT

**The finiteness is TRUE, but the route does NOT map cleanly onto the currently-banked pieces.**

- **Steps 1–2 (raw→cross-coupled bridge + Γ-atom) MAP** — banked identity + measure plumbing + one
  NEW-but-bounded atom lemma, all exact-verified here — **subject to two structural refinements the
  brief's step-framing glosses** (enlarge-before-shear; a genuine second branch `c' ≤ a/2`).
- **Step 3 (finiteness of the outer integral / the `(S,J)` recursion) is a GENUINE GAP.** The strong
  IH is **insufficient as a black box**: at the binding cut the residual exponent *exactly saturates*
  the reduced-chain IH threshold, leaving **zero budget** for the Gram-determinant coupling factor;
  no Hölder / nesting / single-shorter-chain call can absorb it. This gap is **BOUNDED**
  (Aoyagi-style — the coupling is subordinate, value = `½·minAdm`), **not a wall**, but it is the
  **unbuilt `(S,J)` monomial/normal-form double induction**, not a consumption of banked lemmas.

**Consequence for the formaliser:** `sjJointResolution` is **not** a bounded-plumbing sorry like
`sjBoundaryPeel`. It is the mountain. Handing it over as if closable from the banked inventory would
repeat the "clean headline racing ahead of the hole" trap the peel has already avoided four times.
Three decorrelated lines agree on this (my exact algebra; Codex xhigh, independent; the prior
`genm-r1upper-design` cert's overturn test).

---

## Per-step adjudication

### Step 1 — the raw → cross-coupled BRIDGE

| sub-step | status | note |
|---|---|---|
| block identity `frobSq(A0·Q) = ‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²`, `Γ = D−CA⁻¹B` | **BANKED** | `frobSq_schur_block_split` / `frobSq_schur_toBlocks_split` (`RouteMSJChartAlgebra`). Exact, sorry-free. Sympy-re-confirmed to 1e-10 (scalar & matrix Γ). |
| arbitrary `(ρ,κ)` → `fromBlocks` (reindex `A0` rows/cols, co-reindex `Q` rows) | **NEW-but-bounded** | measure-preserving reindex plumbing; `submatrix_mul_equiv` + Frobenius permutation-invariance. |
| shear `D ↦ Γ` measure-preserving | **BANKED** | `measurePreserving_shearSub` (`RouteMSJPivotChart`). |

**REFINEMENT (load-bearing correction to the brief's step-1 framing).** The brief asks whether the
shear rewrites the box integral into the cross-coupled form *"over the shear-image domain — EXACTLY,
with the shear MP on the pivot-chart domain."* It does **not** compose that way, and it need not:

- The block identity rewrites the **integrand pointwise** (exact). `Γ = D − CA⁻¹B` is still a
  *function of D* at this point — the D-block is not yet a free variable.
- The shear MP is **clean only on the full space** `ℝ^{pq}`, not on `matBox ∩ pivotChart` (the box
  maps to an awkward `(A,B,C)`-dependent *sheared box* `{Γ | Γ + CA⁻¹B ∈ box}`).
- The honest, clean composition is: (i) rewrite integrand (banked identity); (ii) Fubini to isolate
  the inner `D`-integral (pivotChart constrains only the minor `A`, so it factors out; `matBox` is a
  product box, so `matBox = box_{ABC} × box_D`); (iii) **enlarge** `box_D ⊆ ℝ^{pq}` (`≤`, integrand
  `≥ 0`); (iv) **full-space** translation `D ↦ Γ` (banked MP). This yields an **upper bound**, not an
  identity — which is all `< ⊤` needs. So `sjJointResolution` proves finiteness by domination, and
  step 1 is *integrand-rewrite + enlarge-inequality + full-space-shear*, **not** an exact
  chart-domain rewrite.

### Step 2 — finiteness of the cross-coupled form (the Γ-atom)

| ingredient | status | note |
|---|---|---|
| anisotropic-shifted corank atom (ADDENDUM-4 lemma 6): `∫_{Γ∈ℝ^{p×q}}(w+‖ΓR+S‖²)^{−c'} = Cinf(pq,c')·det(RRᵀ)^{−p/2}·(w+‖S(I−P_R)‖²)^{−(c'−a/2)}` | **NEW-but-bounded** | generalizes the banked isotropic `matBox_corank_residual_le` (its `R=I,S=0,box` special case). Clean derivation = translation-inv + Gram c.o.v. `Γ=Γ'G^{−1/2}` (Jac `det(RRᵀ)^{−p/2}`) + one radial integral. Verified EXACT (symbolic `p=q=1`, MC matrix `p=q=2`). |
| exponent bookkeeping `a=(M₀−t)(M₁−t)`, shift `c'↦c'−a/2`, Gram exp `−p/2 = −(M₀−t)/2` | **CONFIRMED exact** | see DATA. |

**REFINEMENT / NEW STRUCTURAL BRANCH (the brief's steps 2–3 describe only the atom branch).** The
atom **requires `c' > a/2`**. But `c' < ½·minAdm M` does **not** imply `c' > a/2`: whenever
`a ≥ minAdm M` we have `c' < ½·minAdm M ≤ a/2` *always*, so the atom is **never applicable** on that
chart. This is **real and prevalent** — **94/480** `t ≥ 1` charts over width-`1..4` four-chains (e.g.
`(2,4,1) t=1`: `a=3 > minAdm=2`; `(2,3,1,2) t=1`: `a=2 = minAdm`). Those charts need a **separate,
easier** bounded-integrand argument (`core ≥ w > 0` ⟹ integrand `≤ w^{−c'}`, finite box). Not fatal,
but a branch the route must carry and the sketch omits.

**Two a.e. certificates (from ADDENDUM 4, still required, per-chart):** core positivity `w=‖A·Q̃_p‖²>0`
needs `Q̃_p ≠ 0` a.e. (nonzero-poly witness); the atom needs `rank Q_b = M₁−t` a.e. On the **750/5440
bottleneck charts** (`M₁−t > min(M₂,…,M_L)`) `det(Q_b Q_bᵀ) ≡ 0` and the chart must **recurse** (its
rank drop is a deeper boundary — the `(S,J)` coupling), NOT use the atom.

### Step 3 — the recursion + the additive `½·minAdm` (THE GAP)

| ingredient | status |
|---|---|
| additive `½·minAdm` on the paradigm chain `(3,3,3,3)` | **CONFIRMED** (see DATA: charges `[1,2,3]` sum `6 = minAdm`) |
| well-founded recursion (arity strictly decreases; `t ≥ 1` forces strict reduction) | **sound** (matches the Lean strong-induction spine) |
| **outer-integral finiteness** `∫_{(A,B,C,A')} det(Q_b Q_bᵀ)^{−(M₀−t)/2}·(w+‖C·Q̃_p(I−P)‖²)^{−(c'−a/2)}` from the IH | **GENUINE GAP — the unbuilt `(S,J)` monomial resolution** |

**Why the IH cannot close it (my exact argument; Codex-corroborated).** At the binding cut `t*`,
`minAdm M = a + minAdm(redChain t* M)` (definitional; **0/4000** exhaustive). Hence as
`c' → ½·minAdm M`, the residual exponent `(c'−a/2) → ½·minAdm(redChain t*)` **exactly** — the residual
*saturates the reduced-chain IH threshold*, so the **leftover budget for the coupling factor
`det(Q_b Q_bᵀ)^{−p/2}` is exactly 0** (0/4000). A Hölder split `P_tail^{−(c'−a/2)}·(coupling)` needs a
conjugate `r>1` with `(c'−a/2)r < ½·minAdm(redChain)` — forcing `r → 1` at the endpoint,
**impossible**. Codex sharpened this independently: the Gram factor `‖Q_b‖^{−1}` is IH-controlled only
to power `< 2·½·minAdm(1,3,3) = 3`, and near the endpoint the required conjugate blows up — Hölder
fails for `ε ≤ 5/6`; the "generous" full-tail bound still fails for `ε < 5/14`.

**The mechanism a black-box IH cannot see (mine + Codex, matching ADDENDUM 2).** At `L=2` the tail is a
single free matrix — `Q_p, Q_b` are disjoint row-blocks (independent), the Gram divisor decouples, and
this IS the built `SchurCore`. At `L ≥ 3`, `Q_b = A₁_b·Z`, `Q_p = A₁_p·Z` **share** the deeper product
`Z = A₂···A_{L−1}`; the Gram divisor `{det(Q_b Q_bᵀ)=0}` and the reduced-core divisor live over the
*same* `Z`, and their orders **add** on the shared exceptional divisors — invisible to any single
shorter-chain call. Resolving this is Aoyagi's `diag(b)·[E_J|D_J]·∏_{s>S}C^{(s)}` `(S,J)` double
induction. It is **BOUNDED** (coupling subordinate `a ≤ minAdm(tailChain)`, verified; value exactly
`½·minAdm`), not a research wall — but it is unbuilt and is not the banked inventory.

**Coupled-degeneration observation (third independent angle).** The residual has THREE coupled
degeneration loci the resolution must handle *simultaneously*: `{det A → 0}` (chart boundary — `A`
invertible but arbitrarily near-singular), `{det(Q_b Q_bᵀ)=0}` (tail bottom-rows rank drop), and
`{Q̃_p = 0}` (core zero). Dropping the free `C`-block term to decouple fails precisely near
`det A → 0` (there the surviving `‖C·Q̃_p(I−P)‖²` is what keeps the core positive). This is a fresh
concrete witness that the terms cannot be separated — consistent with the gap, and it confirms the
finiteness does not *diverge* (each locus's order stays under threshold by subordination) — it is
true-but-coupled, not false.

---

## Banked-piece + branch-merge INVENTORY (for the formaliser)

Consumable now (steps 1–2):
- `frobSq_schur_block_split`, `frobSq_schur_toBlocks_split`, `frobSq_row_split`, `fromBlocks_mul_topRows/botRows`, `topRows_eq_mul_QtildeP`, `botRows_eq_cross` — `RouteMSJChartAlgebra.lean` (`origin/genm-sjbpeel`).
- `measurePreserving_shearSub`, `pivotChart`, `pivotLocus_eq_iUnion`, `schur_cov`, `schurCompl` — `RouteMSJPivotChart.lean` (`origin/genm-sjbpeel`).
- `pivotChartCover_matBox_le_sum`, `pivotChartCover_lintegral_le_sum` (CLOSED cover subadditivity), the `rmatMul`/`matBox`/`paramsBoxM`/`redChain`/`tailChain`/`peelExp` defs — in `RouteMSJResolution.lean` / `MatMulFibre.lean` / `RouteMLayerSplit.lean` / `RouteMBoxReduction.lean`.
- Isotropic corank atom `matBox_corank_residual_le` — `RouteMSJCorankResidual.lean` on **`origin/genm-sjpeel-blow`** (NOT in the peel-stack lineage; **must be merged**). Exact statement confirmed: `∫_{matBox p q T} ofReal((frobSq D + w)^{−c'}) ≤ ofReal(Cresid(pq)c'·w^{−(c'−pq/2)})` for `0<p,q`, `pq/2 < c'`, `0<T,w`.

Must be BUILT for step 2:
- `fullSpace_anisotropic_shifted_gamma_atom` (the atom above; generalizes `matBox_corank_residual_le`).
- `gammaBox_le_fullSpace` (enlarge-before-shear, integrand `≥ 0`).
- the `c' ≤ a/2` bounded-integrand branch (separate, easier).
- per-chart `Q̃_p ≢ 0` and `det(Q_b Q_bᵀ) ≢ 0` witnesses (non-bottleneck) + bottleneck routing.

Must be BUILT for step 3 (the mountain — NOT banked):
- the `(S,J)` monomial/normal-form double induction (Aoyagi §5): the `[E_J|D_J]` carrier, the
  charge-update `(S,J)→(S,J+1)` / `S→S+1`, the common-resolution monomial assembly. The charge-budget
  *value* half is banked (`minAdmRec_eq_minAdm`, `sjChargeUpdate_accum`, `sjSubordination`); the
  *integral-level* resolution is not.

---

## Sympy / exact DATA (mine — separated from Codex interpretation)

Scripts under `expeditions/2026-06-20-aoyagi-full/threads/genm-sjjoint-design/`:

- `sjj_atom.py` — (1) anisotropic-shifted atom, MC LHS vs closed RHS: ratios `0.914 / 0.983 / 0.972 / 1.014` for `(p,q,n)=(2,2,3),(2,2,2),(1,3,3),(3,1,2)` (heavy-tail MC noise; symbolic `p=q=1` matches EXACTLY, residual `= 0`). (3a) minAdm anchors all OK. (3b) **`(3,3,3,3)` additive charge: binding cuts `t=2 (a=1)→(2,3,3)`, `t=1 (a=2)→(1,3)`, base `(1,3)=3`; total `1+2+3 = 6 = minAdm`, `½·minAdm = 3` — PASS.** (3c) subordination `a ≤ minAdm(tail)` holds at all cuts.
- `sjj_ihgap.py` — binding-cut identity `minAdm M = a + minAdm(redChain t*)`: leftover budget `0` in **0/4000** random chains. Hölder max conjugate `r → 1` (limit `1.0`) at every binding cut with `a>0` ⟹ **HÖLDER FAILS**.
- `sjj_branch.py` — the `c' ≤ a/2` (atom-inapplicable) branch: **94/480** `t≥1` charts over width-`1..4` 4-chains have `a ≥ minAdm M`.

## Codex INTERPRETATION (decorrelated, xhigh — `codex/sjjoint-{prompt,answer}.md`)

Independently returned **VERDICT: joint-resolution-required** (hypothesis withheld from the prompt).
Its own Hölder-conjugate arithmetic at `(3,3,3,3) t*=2` reaches the same obstruction; it named the
shared deeper product `Z = A₂···A_{L−1}` as the coupling object and judged it **bounded Aoyagi-style,
not a true wall**. Its "most likely wrong": only a *determinant-weighted / rank-stratified
shorter-product theorem* would package it as black-box — "but that theorem would already contain the
simultaneous joint resolution in substance." (Inference, not fact — but it matches my exact
saturation argument and the prior overturn test.)

---

## Closing

- **Firmest result.** `sjJointResolution` is TRUE and BOUNDED, but its proof is the `(S,J)` monomial
  resolution, NOT a banked-piece composition. Steps 1–2 are banked / one bounded new atom
  (exact-verified), modulo enlarge-before-shear and the `c' ≤ a/2` branch. Step 3's outer integral is
  the gap: the IH saturates at the binding cut (0/4000), Hölder is infeasible, the Gram divisor and
  reduced-core divisor share `Z` at `L ≥ 3`.
- **Most likely to break this verdict.** A determinant-weighted / rank-stratified shorter-product
  estimate with explicit dependence on the singular values of the shared `Z` (Codex's escape, my
  ADDENDUM-2 "most likely to overturn"). Both judge it unlikely and, if it existed, tantamount to the
  joint resolution. The cheapest probe: try to bound `∫ det(Q_b Q_bᵀ)^{−p/2}·P_tail^{−(c'−a/2)}` on
  the smallest coupled case `(2,2,2,2) t=1` (tail `(1,2,2)`, a `1×2·2×2` product) purely from the IH
  for `(1,2,2)` + `(2,2,2)` — my prediction (and the prior cert's): it loses a power on `{det Z=0}`.
- **Next construction to settle the open part.** Two staged wins are available WITHOUT the mountain:
  (i) land steps 1–2 as their own lemma — `gammaPeelIntegral ≤ ∑ (Γ-atom residual + c'≤a/2 term)`,
  sorry-free, reducing `sjJointResolution` to *outer-residual finiteness*; (ii) discharge the **`L=0`
  (depth-2) instance** of `sjJointResolution` — there `tailChain M` is a single free matrix, `Q_b`/`Q_p`
  decouple, and it is the banked `SchurCore`/`rrp` case (the `L ≥ 1` instances are the mountain). That
  isolates the true gap to `L ≥ 1` and banks the reachable part. *(Speculation, registered as such — I
  do not prescribe the Lean route; the controller synthesizes it.)*
