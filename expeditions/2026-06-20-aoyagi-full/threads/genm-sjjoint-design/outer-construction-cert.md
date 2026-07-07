# The OUTER `(S,J)` joint-resolution CONSTRUCTION — design certificate (pen-and-paper, aoyagi-full)

**Seat:** pen-and-paper (design a construction + adjudicate where it closes / where it could still be a
wall; exact algebra; decorrelated Codex, hypothesis-withheld). **Target:** the actual RESOLUTION that
CLOSES the outer-residual finiteness left open by my prior cert (`cert.md`) — i.e. finiteness at
`c' < ½·minAdm` of the outer integral of the peel's post-atom residual
`R = det(Q_b Q_bᵀ)^{−(M₀−t)/2}·(‖A·Q̃_p‖² + ‖C·Q̃_p·(I−P_{Q_b})‖²)^{−(c'−a/2)}`, `a=(M₀−t)(M₁−t)`,
where `Q_b` is the non-pivot rows of the tail PRODUCT `Q = A₁···A_{L−1}` (so the Gram determinant couples
to the shared deeper factors `Z = A₂···A_{L−1}`).

---

## VERDICT

**The construction CLOSES the value — but ONLY as a DECORATED joint-resolution induction, not as the
current plain-IH spine; and it has ONE genuinely-new brick that is the true remaining wall for a
formalisation.**

- **It closes.** The finiteness at `c' < ½·minAdm` holds by an induction over **partial rank profiles**
  carrying (i) the accumulated Gram-weight and (ii) a **symbolic exceptional-divisor support table**
  (which variables are SHARED). The exponent accounting is exact and closes for **every** chart at
  **every** cut (verified `0/171`), not just the binding branch. This is the analytic realisation of
  Aoyagi's coupled `diag(b)` `(S,J)` resolution (worked-tex `§ssec:blowup`/`§ssec:candidates`).
- **The current `sjJointResolution` contract cannot be the vehicle.** Its IH is *plain* box-finiteness
  for shorter chains (`hIH : ∀ M', RouteMBoxThresholdFinite M'`). My prior cert proved this is
  insufficient; the construction shows *why constructively*: the recursion must carry the Gram-weight +
  support, so the inductive statement must be **strengthened to a decorated object** `I_π(s)`. The
  spine (`SJStepHyp`, `routeMBoxThresholdFinite_of_step`) is a correct *outer* scaffold, but the joint
  resolution is a **separate weighted induction** that slots under it — `sjJointResolution`'s plain IH
  is the top-level consumer, not the recursion engine.
- **The one remaining wall (probe it hardest).** The genuinely-new, non-standard, un-banked brick is the
  **joint normal-form / principalisation of `det(Q_b Q_bᵀ) = ‖∧^{q}Q_b‖²` of a matrix PRODUCT
  `Q_b = A_{k,b}·Z`, simultaneously with the projected residual core, tracking the shared divisor
  support at corank ≥ 2.** If this lemma is admitted, the induction closes by the banked monomial
  endpoint. Without it, it does **not** close cleanly. It is **BOUNDED** (the value is certified
  general-`L`, all branch types — Aoyagi + 3 methods + RRR anchor), i.e. **not a mathematical wall**,
  but I cannot label it bounded-standard: it is genuine-new and is where a formalisation stalls.
  Decorrelated Codex (xhigh, my construction withheld) **independently produced the same decorated
  object, the same accounting, and named the same hardest brick.**

---

## Q1 — the joint blow-up, mapped to Aoyagi's construction

Aoyagi resolves `‖∏_{s=1}^L C^{(s)}‖²` at the deepest point by a simultaneous rank-flag blow-up
(worked-tex `theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex §ssec:blowup`, p.15–22 of the
original). The **resolution variety** is built by the `(S,J)`-indexed step (`0≤S≤L`, `0≤J≤M(S+1)`,
`M(S)=min{M^{(s)}:s≤S}`), maintaining the invariant

    ⟨∏_{s=1}^L C^{(s)}⟩ = ⟨ diag(b₁,…,b_{M(S)}) · [[E_J,O],[O,D_J]] · ∏_{s=S+1}^L C^{(s)} ⟩,

`D_J` the `(M(S)−J)×(M^{(S+1)}−J)` residual block, `b_i` accumulated exceptional monomials
(`b_0=1`, `b_i = (∏_{t̃_{s,k}=i−1} u_{s,k})·b_{i−1}`). The blow-up **charts** are:

- **Case 2** (full remaining equal block): blow up `{d_{ij}=0 : J<i≤M(S), J<j≤M^{(S+1)}}`; the chart
  introduces `u_{S,J+1}` with divisor exponent `M'_{S,J+1}=(M(S)−J)(M^{(S+1)}−J)` (the residual-block
  codim), reduces `D_J → [[1,O],[O,D_{J+1}]]`, advances `J` (or `S`).
- **Case 1** (partial equal block, length `J₁`): blow up the `J₁×(M^{(S+1)}−J)` sub-block; splits into
  1(1) (an *inner* recursion **adding** `J₁(M^{(S+1)}−J)` to a divisor's exponent) and 1(2)
  (introduces `u_{S,J+1}`, advances `J`).

At `S=L+1` the product is diagonal `diag(b₁,…,b_{M(L+1)})` and `‖∏‖² = ∑ b_i²` — **normal crossing**.

**Correspondence to the repo's peel-atom.** The peel's boundary-0 pivot-chart + Schur + Γ-atom IS one
Case-2 step, *pre-integrated*: the atom does in one measure-theoretic move (`matBox_corank_residual`
→ residual with charge `a/2 = ½(M₀−t)(M₁−t)`) what the Case-2 blow-up does (introduce `u`, Jacobian
power `M'−1`, charge `M'/2`). So the outer recursion = iterating the peel-atom, layer by layer,
accumulating the `diag(b)` weight. The Gram determinant `det(Q_b Q_bᵀ)^{−p/2}` is the analytic shadow
of `∏_i b_i^{−p}` (Q3).

## Q2 — the induction structure (the DECORATED object)

The plain object `Box(N,c')` cannot recurse (the weight has nowhere to live). Strengthen to a
**decorated residual integral** indexed by a **partial rank profile** `π=(t₁,…,t_k)` (`t₀=M₀`, weakly
decreasing, `t_j ≤ admBound(j)`):

    I_π(s) := ∫ W_π · F_π^{−s},

- `F_π` = the current Schur/projection residual core (`≈ P_tail` of the depth-`(L−k)` remaining chain);
- `W_π` = the product of Gram-determinant weights created by the `k` peels so far;
- **the datum carries a common exceptional-divisor support table**: for each divisor, the order of every
  core generator, every Gram minor, and the Jacobian — i.e. **which variables are shared** (this is the
  load-bearing decoration; a threshold-only invariant cannot distinguish `⟨δx,δy⟩` from `⟨δ₁x,δ₂y⟩`,
  Q3/DATA-A).

Accumulated charge `A(π) = ∑_{j=1}^k (t_{j−1}−t_j)(M_j−t_j)`. **Remaining threshold**

    Θ(M,π) := ½( min_{T ⪰ π} Mval_M(T) − A(π) ),        Mval_M(T) = Aoyagi terminal exponent.

**IH:** `I_π(s) < ∞ for every s < Θ(M,π)`. Original box is `π = ∅`, `A=0`, `Θ = ½·minAdm(M)`.

**Peel step (well-founded).** A peel at next cut `u=t_{k+1}` adds `a=(t_k−u)(M_{k+1}−u)`, creates the
Gram factor, and shifts `s ↦ s−a/2`, giving child `π'=(π,u)`. The step is sound because

    s < Θ(M,π)  ⟹  s − a/2 < Θ(M,π')     for EVERY legal u,

which reduces to the **threshold-monotonicity** `min_{T⪰(π,u)} Mval ≥ min_{T⪰π} Mval` (completions of
`(π,u)` ⊆ completions of `π`) — verified `0/171` (DATA-C). **Well-founded** by finite profile length
`≤ L` (equivalently the finite `(S,J)` progression). **Base** `k=L` (or `L=1`): the terminal
one-matrix / free-vector Morse endpoint (banked `sjBase1_freeMatrix` / `sumSqND_box_lt_top`), plus the
monomial rule for the accumulated `∏ b_i` weight (banked machinery — Q4).

**Induction variable = chain arity / profile length**, matching the existing Lean spine
`routeMBoxThresholdFinite_of_step` (`Nat.strong_induction_on`) — but over the DECORATED statement, NOT
the plain `RouteMBoxThresholdFinite`.

## Q3 — the exponent accounting (the crux) + how it beats Hölder

The resolution makes the loss normal-crossing; each terminal divisor `u_{s,k}` has Jacobian power
`M_{s,k}−1` and loss-order 2, so `∫ u^{−2s}·u^{M_{s,k}−1} du < ∞ ⟺ s < M_{s,k}/2`. And **every**
admissible-branch terminal exponent `M_{s,k}=Mval(branch) ≥ minAdm`, min attained at the binding branch
(DATA-B, exhaustive). Hence `s = c' < ½·minAdm ≤ M_{s,k}/2` on **every** divisor ⟹ converges.

**Paradigm `M=(3,3,3,3)` (binding `T=(2,1,0)`, charges `[1,2,3]`, `Mval=6`, `½minAdm=3`), `c'=3−ε`:**

| peel | cut | charge `a` | shifted `s` | child threshold `Θ` |
|---|---|---|---|---|
| 1 | `t₁=2` | `1` | `s₁ = 5/2 − ε` | `½(6−1) = 5/2` ✓ |
| 2 | `t₂=1` | `2` | `s₂ = 3/2 − ε` | `½(6−1−2) = 3/2` ✓ |
| base | `t₃=0` | `3` | — | `2s₂ = 3 − 2ε < 3` ✓ |

Along the full branch, `2c' = 6 − 2ε < 1+2+3 = 6`. **This is the recovered budget.** The black-box
Hölder route (my prior cert) computed `½·minAdm(redChain)` for `P_tail` and, at the binding cut, had
`c'−a/2 → ½·minAdm(redChain)` — zero slack for the coupling. The DECORATED route pays the Gram pole's
order **on the SAME resolved divisors as the residual core** (they share `Z`, so share divisor labels),
so its order is added into the child's divisor ledger, not demanded as an independent integral. That is
precisely the correlation data the black-box shorter-chain call cannot see.

## Q3 (hardest brick) — the simultaneous monomialisation, and whether corank ≥ 2 CLOSES

The single genuinely-new step: **jointly principalise `det(Q_b Q_bᵀ)` and the projected core**, where
`Q_b = A_{k,b}·Z` is the non-pivot rows of a matrix PRODUCT. Concretely — a finite chart decomposition

    Q_b = D_b · U_b,   U_b U_bᵀ uniformly nonsingular   ⟹   det(Q_b Q_bᵀ) ≍ ∏_i b_i²,

so `det(Q_b Q_bᵀ)^{−p/2} ≍ ∏_i |b_i|^{−p}` (total order `pq = a`, matching the charge), and the
projection `P_{Q_b}=U_bᵀ(U_b U_bᵀ)^{−1}U_b` introduces **no hidden `b_i^{−1}` poles** (the diagonal
cancels), so `I−P_{Q_b}` is clean. **Corank ≥ 2 CLOSES** because the same `b_i` divisor labels remain
visible in `Q_p`, `Q_b`, and the later generators — *shared, not duplicated*. Clean identity:
`det(Q_b Q_bᵀ) = ‖∧^{q}Q_b‖²`, so principalise the vector of maximal minors (Plücker coords) of the
product; sum-of-squares prevents cancellation once one transformed Plücker coordinate is a unit.

**Why this is the wall.** A free-matrix Schur chart is standard (banked at `L=2`). The **product** case
`Q_b = A_{k,b}·A_{k+1}···A_{L−1}` must resolve the Gram minors of a product while **preserving the shared
deeper factors** — that is the corank-≥2 symbolic-support tracking the worked-tex certifies as NECESSARY
(the `⟨δx,δy⟩` vs `⟨δ₁x,δ₂y⟩` obstruction, DATA-A; the binding DLN witness `(3,3,4) t=(1,0)`, corank
`2×2`, coupled `rlct=4` vs threshold-only `3`, `verify-r1-diagb-334.md`). It is not measure-theoretic
plumbing; it is a resolution-of-singularities / principalisation lemma. **This is exactly where a clean
measure-theoretic route (change-of-variables + Fubini + monomial endpoint) does NOT suffice on its own.**

---

## Q4 — banked / new brick map

**Consumable (banked or bounded-and-verified):**
- the boundary-0 peel-atom step (steps 1–2 of `cert.md`): block identity `frobSq_schur_block_split`,
  shear `measurePreserving_shearSub`, the anisotropic-shifted atom (generalising `matBox_corank_residual_le`,
  `origin/genm-sjpeel-blow`), the pivot-chart cover `pivotChartCover_matBox_le_sum`.
- the charge-budget VALUE half: `minAdmRec_eq_minAdm`, `LayerSplit_value_eq_minAdm`, `Mval_decompose`,
  `sjChargeUpdate_accum`, `sjSubordination`, `minAdm_leadWidth_mono`, `sjRunMin_antitone` — all sorry-free.
- the monomial / Morse endpoint: `sumSqND_box_lt_top`, `Case222Cover.monomialIntegrand_integrable_of_lt`,
  `monomialThreshold_ge_of_mult`, `integrableOn_monomial_mul_unit_iff`, `monomialIntegrand_eq_prod_rpow`;
  and the **specific-case blow-up bricks** `Case111`/`Case222` (Aoyagi Case 1 / Case 2 for the `(2,2,2)`
  worked instance) — the general-`L` templates.
- the recursion spine `routeMBoxThresholdFinite_of_step` + base `sjBase1_freeMatrix` (correct *outer*
  scaffold; must wrap the decorated statement — see below).

**NEW bricks the construction needs:**
| brick | class |
|---|---|
| the DECORATED statement `I_π(s)` (partial-profile-indexed object carrying `W_π` + divisor-support table) + its arity induction | **genuine-new** (re-scopes the contract) |
| threshold monotonicity `min_{T⪰(π,u)}Mval ≥ min_{T⪰π}Mval` (peel-step soundness) | bounded-standard (DATA-C; combinatorial, on the banked `minAdm`) |
| the per-layer charge-accumulation `Σ charges = Mval(branch)` + all-branch `≥ minAdm` | bounded-standard (DATA-B/C; = `minAdmRec` + cone enumeration) |
| **joint principalisation of `det(Q_b Q_bᵀ)=‖∧^q Q_b‖²` (matrix PRODUCT) + projected core, tracking shared support (corank ≥ 2)** | **genuine-new — THE WALL** |
| the weighted base/endpoint (`∏ b_i` monomial weight × Morse) | bounded (banked monomial machinery, needs the weighted wrapper) |

---

## DATA (mine — exact; separated from Codex INTERPRETATION)

Scripts under `.../threads/genm-sjjoint-design/`:
- **DATA-A** (`sjj_resolution.py`) — the sharing obstruction, EXACT via the toric RLCT formula
  `rlct(∑x^α)=min_{w>0}(Σw)/(min_α⟨w,α⟩)` (sanity `x²=½`, `x²+y²=1`): `⟨δx,δy⟩ = ½` (shared `δ`) vs
  `⟨δ₁x,δ₂y⟩ = 1` (separate) — identical threshold/multiplicity data, different value ⟹ the support
  table is NECESSARY.
- **DATA-B** (`sjj_resolution2.py`) — every admissible-branch terminal exponent `Mval ≥ minAdm`, min =
  `minAdm`, for `(3,3,3,3),(3,3,4),(2,2,2,2),(3,3,3,3,3),(4,4,4,4)`. `(3,3,4)` binding `t=(1,0)`, corank
  `2×2`, coupled `rlct=4`.
- **DATA-C** (`sjj_resolution2.py`,`sjj_thresh_mono.py`) — per-layer charges sum to `Mval=minAdm`
  (`(3,3,3,3):[1,2,3]`, `(3,3,3,3,3):[1,2,3,0]`, `(4,4,4,4):[4,3,4]`, `(3,3,4):[4,4]`); threshold
  monotonicity holds `0/171` partial-profile/next-cut pairs ⟹ the induction closes for EVERY chart.

## Codex INTERPRETATION (decorrelated, xhigh — `codex/construction-{prompt,answer}.md`; my construction withheld)

Independently produced: the same **decorated residual integral** `I_π(s)=∫ W_π F_π^{−s}` with the same
partial-profile index, the same charge `A(π)`, the **same threshold** `Θ(M,π)=½(min_{T⪰π}Mval−A(π))`,
the same peel-step soundness `s<Θ(π) ⟹ s−a/2<Θ(π')`, the same `(3,3,3,3)` accounting, and named the
**same hardest brick**: "simultaneous monomialisation of `det(Q_bQ_bᵀ)` and the projected residual core",
via `Q_b=D_bU_b` ⟹ `det ≍ ∏b_i²`, `det^{−p/2}≍∏|b_i|^{−p}` (order `pq=a`), `det(Q_bQ_bᵀ)=‖∧^qQ_b‖²`,
"divisor labels shared, not duplicated." Its "most likely formalisation stall": proving the joint normal
form for a **matrix product** `Q_b=A_{k,b}·A_{k+1}···A_{L−1}` (not a free matrix) — "if this
normal-form/principalisation lemma is admitted, the induction closes by monomial endpoint inequalities;
without it, the construction does not close cleanly." (Inference, but matches my exact accounting + the
worked-tex certification of the value.)

---

## Closing

- **Firmest.** The outer finiteness closes at `c'<½·minAdm` as a DECORATED arity induction over partial
  rank profiles carrying the Gram-weight + a symbolic divisor-support table; the exponent accounting is
  exact and closes for every chart (`0/171`), recovering the budget the black-box Hölder route lost by
  paying the coupling's order on the shared divisors. This is Aoyagi's coupled `diag(b)` `(S,J)`
  resolution; the value is certified general-`L`. Decorrelated Codex reproduced the object, the
  accounting, and the hardest brick.
- **The one place it could still be a wall (probed hardest).** The joint principalisation of
  `det(Q_b Q_bᵀ)=‖∧^q Q_b‖²` for the matrix PRODUCT `Q_b=A_{k,b}·Z`, jointly with the projected core,
  tracking shared support at corank ≥ 2. It is BOUNDED (value certified), so not a mathematical wall,
  but it is genuine-new resolution-of-singularities content, NOT measure-theoretic plumbing, and is
  where a formalisation stalls. I do not certify it bounded-standard.
- **Actionable structural consequence.** `sjJointResolution`'s plain-IH contract cannot be the recursion
  vehicle; the construction requires a NEW decorated statement `I_π(s)` with its own arity induction. The
  controller should re-scope the analytic contract to the decorated object (the spine stays as the outer
  scaffold; `sjJointResolution` becomes its top-level `π=∅` corollary).
- **Next construction to settle the open part.** Attempt the joint normal-form lemma on the smallest
  genuinely-coupled product case — `Q_b = A_{1,b}·A_2` at `(2,2,2,2) t=1` (a `1×2 · 2×2` product,
  corank 1) then `(3,3,3,3) t=2` (corank `1×1` but two active deeper layers) and the corank-2 product
  `(3,3,4)`-embedded-in-`(3,3,4,·)` — checking that `det(Q_bQ_bᵀ)=‖∧^qQ_b‖²` principalises to `∏b_i²`
  on a finite chart cover of the product while the projected core stays pole-free. My prediction (and
  the QR/`D_b U_b` split suggests): it principalises, and the corank-≥2 sharing is carried by the
  Plücker-coordinate support — but this is the lemma to build, and its faithfulness for a genuine
  `≥2×2` block on a PRODUCT (not a free matrix) is the crux. *(Speculation, registered — the Lean route
  is the controller's.)*
