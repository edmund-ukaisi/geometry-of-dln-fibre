# brickD-pin — the exact per-arm statement + proof decomposition of `headSplit_domination` (Brick D)

**Seat:** pen-and-paper (design, decorrelated), `genm-satred`, backbone follow-on (controller commission
"pin Brick D's exact per-arm statement"). **Date:** 2026-07-16. **NO Lean edits.** This pins the CONTRACT
(already in Lean) + the per-arm PROOF decomposition + the banked-lemma citations per arm + the honest scope
forks, so a dedicated formaliser builds Brick F then Brick D. Verified: exact-ℕ scope scan
(`scripts/brickD_scope.py`, 22932 cuts, 0 fails), the read of the full assembly
(`RouteMSJDeeperFlagCore.lean`), my satred/D-cert content, decorrelated Codex (`codex/brickD-{prompt,answer}.md`).

---

## ★ WHAT BRICK D IS (and is not)

`headSplit_domination` (`RouteMSJDeeperFlagCore:513`) is the **single unbuilt analytic seam** of the
reduce-to-shorter-chain. It is the **front-block change-of-variables**: it integrates out the FRONT outer
blocks (`P`:u×u, `B₁₂`:u×b, `C`:a×u) of `freedSchurLoss` and does the row/head split, producing the freed
core `deeperFlagCoreIntegrand` — leaving the corank-weight integral (`∫_{A_cor}∫_Γ`) and the reduced-param
integral for **L1** (`deeperFlag_shell_core_le`, ALREADY sorry-free) and the decorated IH. It does **NOT**
do the corank weight (that is L1) and does **NOT** touch the codim/`rlct` levels (pure finiteness/(□)).

**The scaffolding is the DECORATED JOINT DESCENT** — the valid backbone from `backbone-cert.md`, NOT the
naive "absorb pivot → routeMLayerBoxIntegral(redChain) directly" (Codex-unsound). The target is the
DECORATED `cornerComparator (redChain u M) ![1] ![minAdm−1]` (`decLoss = commonDivisor(v)²·frobSq(prod
(redChain u M) z)` — the P-radial exceptional monomial × the reduced product), reached via L1 then the
decorated IH (`cornerComparator_adm` + `adm`). Confirmed sound: the exponent gate is safe (cut-soundness
`minAdm M ≤ peelCharge(u)+minAdm(redChain u M)`, **0/22932**), and the in-scope regime is strictly
convergent (below).

## 1. The verbatim contract (do not restate — this is the Lean statement to prove)

`headSplit_domination M t j κ hε c' ht hj ht1 hnd hpiv hcvg hrange hε' Zf U_sf hZfMeas hUsMeas hUs hrank
hfloor hagree` (`:513`), with `u := t+j`, `a := M 0 − u`, `b := M 1 − u`, delivers

    ∃ Ccrossf sΓf (C_hle : ℝ≥0∞), C_hle < ⊤ ∧
      shellSpineIntegrand M u κ ε (min (M 0 − t) (M 1 − t)) ⟨j,_⟩ c'
        ≤ C_hle · deeperFlagCoreIntegrand M u ![1] ![minAdm (redChain u M) − 1] Zf Ccrossf sΓf c'.

The SCOPE hypotheses (load-bearing, verified in §4): `hpiv : minAdm (redChain u M) ≤ u · tailMinWidth M`
(pivot-admissibility, gates `C_hle < ⊤`); `hcvg : a + b ≤ min (M 1) (M_last) − j =: m` (corank
convergence); `hrange : m ≤ M 2` (range/non-vacuity); `hε' : 0 < ε'` (floor `ε' = ε/√(M₁M₂)`); the frame
data (`Zf, U_sf` + `hUs/hrank/hfloor/hagree`) from Brick F.

## 2. The proof decomposition (six steps; the docstring's content, made per-arm)

**(S-a) Row-split** `A' ↔ (z, A_cor)` via `blockSplitEquiv κ` (pivot rows `z` = the κ-image; corank rows
`A_cor` = the b complement rows of the leading tail layer `A₀ := A' 0`). Banked reindex; measure-preserving.

**(S-b) Head-split** `prod (tailChain M) A'` → expose `Q_p = z·Z_deep` (u pivot rows) and `Q_b = A_cor·Zf z`
(b corank rows), via `prod_headSplit` / `paramsHeadSplit` and `deeperFlagZdeep`. `Z_deep = Zf z` on the good
set `G` (Brick F `hagree`; Ky-Fan → shell ⊆ G, step S-e).

**(S-c) P-radial blow-up** `P = commonDivisor(v)·P̂` (det-1 clear): the pivot energy `frobSq(P·Q̃ₚ)` becomes
`commonDivisor(v)²·frobSq(prod (redChain u M) z) = (cornerComparator … ![1] ![minAdm−1]).decLoss v z` PLUS
the Jacobian monomial `∏|v_ℓ|^{jc_ℓ}` (here `d=1`, `jc = minAdm(redChain u M)−1`). This is what makes the
target the DECORATED comparator (the density that satred's coupled route worried about is carried by the
blow-up monomial, NOT folded pointwise — so no `A>2Δ` undershoot; see §4). `Qt := Q̃ₚ = Q_p + P⁻¹B₁₂Q_b`.

**(S-d) B₁₂ → Γ' shear** `Γ' = Γ + C·P⁻¹B₁₂` (banked `RouteMSJChartShear`, measure-preserving): `B₁₂` is
absorbed exactly into the Γ-shift, so `frobSq(C·Qt + Γ·Q_b)` is unchanged in form and the `B₁₂`-integral is
a bounded box-volume factor into `C_hle`.

**(S-e) C-integral → `C_hle < ⊤`** (THE per-arm core — §3). Integrate `C` (a×u) out; the result is
`Ccrossf z` (the shifted cross-data) plus a FINITE, z-uniform constant absorbed into `C_hle`. `C_hle < ⊤`
is via the codim-`u·ρ` linear-image argument (gated by `hpiv`) + the banked C-integral atoms. Ky-Fan
(`RouteMSJKyFan`) shows the shell image sits in `G` so `Zf = Z_deep` there.

**(S-f) Assemble** `shellSpine ≤ C_hle · deeperFlagCore` (the leftover `∫_{A_cor}∫_Γ` + reduced-param
integrals are exactly `deeperFlagCoreIntegrand`, untouched — handed to L1).

## 3. The per-arm `C_hle < ⊤` (S-e) — the arms the controller named, with banked citations

`C_hle < ⊤` is the finiteness of the integrated-out front. It splits by `a` vs `u` (this IS my D-cert
§3bis / satred, now placed as Brick D's internal case analysis):

**Arm A<U (`a < u`) — the CLEAN R2 leaf.** Drop the C-transverse (`‖C·Qt·Π_⊥ω‖² ≥ 0`); the C-integral
is the banked R2 form (`edge_C_shift_bound` / `RouteMSJGammaAtom`, β-invariant): `≤ |v'_{j₀}|^{−a}·R_a(W,c')`
with `R_a = scaledRadialEuclid` a CLEAN power `W^{a/2−c'}` (c' > ab/2 strict, no log). The `|v'_{j₀}|^{−a}`
weight is disposed by the sphere integral `∫_{ω} ‖Qt·ω‖^{−a} dω`, **finite IFF a < u** (`ker Qt` codim u;
`corner_block_lintegral_lt_top`). This is edgefub's b=1 leaf, generalised: for a<u it is the finite,
network-free route, and `C_hle` is this sphere constant × `R_a`'s `Cresid`. [Correction banked in D-cert:
`a<u` is right — `Qt` (u<N) has a kernel, `v→0` on it, the threshold is genuine.]

**Arm A≥U (`a ≥ u`) — the FULLER lemma (the two banked atoms).** The dropped-transverse is lossy
(`∫‖v‖^{−a}dω` diverges for a≥u), so keep the full C-integral. Via `Y = C·Qt` (Jacobian `det(Qt Qtᵀ)^{−a/2}`)
+ shift-invariance it is EXACTLY the banked `RouteMSJGammaAtom.gammaAtom_aniso_shifted_eq`
(`R=Qt, q=u, S=γ⊗Q_b, p=a`: `det(RRᵀ)^{−a/2}·Cresid(a u)·(w+‖S(I−P_R)‖²)^{−(c'−au/2)}`; needs `Qt Qtᵀ`
PosDef = full-row-rank, generic at hpiv). The reduced pivot-Gram `∫ det(Qt Qtᵀ)^{−a/2}` is the banked
`RouteMSJQBoxCore.qbox_lintegral_lt_top` (`< ⊤` iff `b ≤ q` and `a < q − b + 1`), applied at the PIVOT
Gram (full-rank, safe) — **NOT the corank `Q_b` Gram** (`a = q−b+1` trap; NEVER cite qbox for `Q_b` at the
edge). Dim-matching (`Qt`'s row/col ↔ qbox `b,q`) FOLDS into the reduced-chain recursive IH at the merge
(D-cert §3bis: single-level qbox is strict for 209/283, the marginal cells recurse one level — the arity
recursion; NOT a one-shot). `C_hle` = the `Cresid`/box constants; the `det(Qt Qtᵀ)^{−a/2}` is disposed by
the IH (it is the reduced chain's OWN leading-Gram singularity).

**The P-block absorption (satred, both arms).** `[P|B₁₂]` (u×(u+b)) stays full row rank u as `det P → 0`
(`B₁₂` supplements — the cross-block IS the det-P compensation), so the det-P→0 region contributes a finite,
vanishing-with-cutoff amount (NOT the non-integrable `|det P|^{−M₂}` artifact of the wrong per-P CoV). The
codim-`u·ρ` linear-image argument (gated by `hpiv`, witness `(3,3,4,4)`: hpiv is strictly stronger than mere
convergence on `M₂>M₁` wide chains) is what makes the absorbed integral finite → `C_hle < ⊤`.

**Gram/monomial → `decLoss` (the decoration carried).** The P-radial (S-c) delivers `decLoss v z =
commonDivisor(v)²·frobSq(prod (redChain u M) z)` + the monomial `∏|v_ℓ|^{jc_ℓ}` — the Gram weight is carried
INTO the decorated comparator, not discarded (Codex backbone-verdict + satred: the blow-up monomial carries
the density; the monomialThreshold at `k=![1], jc=![minAdm−1]` equals `½minAdm(redChain u M)`, verified in
`spineToCore`'s `hbeta`).

**⚠ CONDITIONALITY of `C_hle < ⊤` (decorrelated Codex, folded honestly).** `C_hle` is NOT unconditionally
finite/uniform. Integrating the front to a constant needs (a) a threshold `c' < D/2`,
`D = u² + a·dim(Row Q̃ₚ + Row Q_b)` — in the decisive cell `(u,a,b)=(1,1,1)`, `N=m=2` (chain `(2,2,2)@u=1`)
`D/2 = 3/2 = ½minAdm(M)` EXACTLY, so the true constraint `c' < ½minAdm M` SATURATES the threshold (verify it
does so per-cell, not just here); and (b) **UNIFORM CONDITIONING** — a uniform lower singular-value bound on
`Q̃ₚ`/the combined row-space, NOT merely generic full rank (Codex + the backbone-cert O1: full rank is
insufficient — the maps can APPROACH rank-drop within the box). This is precisely why Brick D must NOT
integrate the front to a bare constant but must (i) BLOW UP P (→ `decLoss`, carrying the pivot energy as the
decoration, not a constant) and (ii) CARRY `Q_b`/`det(Q̃ₚQ̃ₚᵀ)^{−a/2}` to the reduced chain (the IH), which is
exactly the scaffolding's route. The uniform conditioning of the m-frame `Q_b = A_cor·Zf` IS Brick F's role
(the Loewner floor `hfloor : Zf·Zfᵀ ⪰ ε'²·U_sf·U_sfᵀ`); the PIVOT `Q̃ₚ`'s non-uniformity (`z→0` in the box)
is carried to the reduced chain via `det(Q̃ₚQ̃ₚᵀ)^{−a/2}` → `qbox`/IH, NOT absorbed into `C_hle`. **Two sharp
sub-caveats (Codex Q4):** (1) the projected Gram `Q_b(I−P_R)Q_bᵀ` (gammaAtom's `‖S(I−P_R)‖²`) can DEGENERATE
when `Row Q_b → Row Q̃ₚ` even with `Q_b` full row rank — the reduced chain must carry this; (2) if `Z_deep`'s
nonzero singular values approach 0, `det(·)^{−a/2}` scales as `t^{−ab}` — the Gram weight must remain in the
induction (never a uniform constant). **Net: the blow-up+carry route + Brick F's floor are the mechanisms
that make `C_hle < ⊤` hold; do not state `C_hle` as an unconditional constant divorced from them.**

## 4. The scope — verified exact (`scripts/brickD_scope.py`, 22932 cuts)

**(P1) In-scope is the STRICTLY-CONVERGENT interior — NO log.** For every in-scope cell (`hcvg: a+b ≤ m`),
the strong-block convergence `a < m − b + 1` HOLDS strictly (**0/20874 fail**). So the corank weight
`∫det(gram)^{−a/2}` is finite (L1's `strongBlock_unif_const_lt_top`), and L1 extracts the FULL `ab/2` charge
uniformly. **Brick D's in-scope arms therefore carry NO δ-slack / NO log** — the edge δ-slack is OUT of this
statement's scope (P3).

**(P2) In-scope single-chain reduction REACHES `½minAdm M`.** L1 lands `cornerComparator(redChain u M).
integral(c'−ab/2)`; cut-soundness (`minAdm M ≤ ab + minAdm(redChain u M)`, **0/22932 fail**) gives
`ab/2 + ½minAdm(redChain u M) ≥ ½minAdm M`, so the shifted exponent `c'−ab/2 < ½minAdm(redChain u M)`
strictly for `c' < ½minAdm M`. The `k = a+b−ρ > 1` "multi-chain" cells that ARE in-scope (2274, all with
`a=0`, saturated) are still fine — L1 uses the strong-block uniform bound, NOT the sector charge, so the
`k>1` undershoot (D-cert) does not bite in the convergent regime.

**(P3) Two SCOPE FORKS to surface to the controller (design decisions, not walls):**
- **The log-tie + deep corank are OUT of scope.** The corank-one tie (`a+b = m+1`, **7476 cells**, e.g.
  `(1,3,·)@u=1`) violates `hcvg`; there the strong block log-diverges and the reduction needs the δ-slack /
  rank-sector (D-cert §3). These are handled by the EDGE brick (edgefub, b=1 a<u) and the cut-selection /
  deeper shells — NOT `headSplit_domination` as stated. IF the controller wants Brick D to absorb the tie,
  its `hcvg` must weaken to `a+b ≤ m+1` and the proof gains the δ-slack arm (`one_add_log_inv_le_rpow` +
  the arity-IH on the open range `c'−ab/2+δ < ½minAdm(redChain)`) — the genuinely-harder analytic content.
  **Recommendation: keep `headSplit_domination` at the clean interior (`hcvg` as-is); delegate the tie to
  the edge brick.** The shells at a binding cut have `k_j = k_0 − 2j`, so most shells are interior; the tie
  shell is edgefub's; the deep/saturated is `deeperFlag_waist`.
- **`a=0` (saturated, top shell `j=M₀−t`) is nominally in-scope but its content is satred's.** At `a=0` the
  C-block and the second `freedSchurLoss` term vanish (satred S1); Brick D degenerates to the P-radial only,
  reducing to the comparator at `c'` (peelCharge=0). This is PROVABLE within `headSplit_domination` (the
  degenerate arm) via the P-radial blow-up (which supersedes satred's `A>2Δ` pointwise-fold worry — the
  blow-up monomial carries the density, reaching `½minAdm M` via cut-soundness). **BUT** the docstring
  routes `a=0`/waist to the SEPARATE `deeperFlag_waist` (SVD-qPeel, task #156, satred's coupled route).
  **Recommendation: add `1 ≤ M 0 − (t+j)` (i.e. `a ≥ 1`) to `headSplit_domination`'s hypotheses to cleanly
  exclude `a=0`** (delegating saturation to `deeperFlag_waist`), OR keep it and prove the degenerate `a=0`
  arm inline citing satred. Either is sound; the `a≥1` guard is cleaner (matches the corank-route content).

## 5. Banked vs new (the formaliser's kit)

**BANKED (consume):** L1 `deeperFlag_shell_core_le` (the whole corank-weight → comparator step, sorry-free);
the S3 uniform bricks (`strongBlock_lintegral_le_unif`, `shellCorankWeight_le_unif`,
`shell_corankOffSector_le_unif`); `RouteMSJChartShear` (freedSchurLoss/weld/blockSplitEquiv, the B₁₂→Γ'
shear); `RouteMSJGammaAtom.gammaAtom_aniso_shifted_eq` (a≥u C-integral); `RouteMSJQBoxCore.qbox_lintegral_lt_top`
(reduced pivot-Gram); `edge_C_shift_bound` / `corner_block_lintegral_lt_top` (a<u leaf + sphere disposal);
`RouteMSJKyFan` (shell ⊆ G); `cornerComparator_decLoss` / `_adm`; `deeperFlagCore_decLoss_pos_ae` (hpos,
sorry-free); the P-radial det-1 clear + `prod_headSplit` / `paramsHeadSplit`. **Diamond guard:** raw-`Pi`
instances for all matrix CoV/products (`Matrix.module` diamond).

**NEW (build inside Brick D):** the ASSEMBLY of S-a..S-f — the row/head-split CoV threading, the P-radial
blow-up producing `decLoss` + monomial, the C-integral arm-dispatch (a<u vs a≥u) folding into `C_hle`, the
codim-`u·ρ` linear-image finiteness (satred, gated by hpiv), Ky-Fan → G. This is chart-maps + Jacobians +
the two banked C-integral atoms glued — patient detail-at-scale, NOT a monument (Mathlib-gap-wise). Brick F
(`exists_headSplitFrame`) is the measurable frame selector (Borel functional calculus, moderate — build it
FIRST; `deeperFlag_spineToCore` consumes F then D).

## 6. Decorrelated Codex — DONE (`codex/brickD-{prompt,answer}.md`, xhigh, conclusion withheld)

Independently confirms the design AND sharpens it (folded into §3's conditionality caveat):
- **Q1:** `C_hle < ⊤` is NOT unconditional — needs `c' < D/2` (`D = u²+a·dim(Row Q̃ₚ+Row Q_b)`) + uniform
  conditioning, not generic full rank. (In `(2,2,2)@u=1`, `D/2 = ½minAdm M` exactly — the true constraint
  saturates it.) ⟹ the front must be BLOWN UP + CARRIED, not integrated to a bare constant. Matches the
  scaffolding's route + the backbone-cert O1.
- **Q2:** the `a<u` vs `a≥u` split IS needed for the comparison proof (`a<u`: drop-transverse majorant
  `∫_S‖Q̃ₚω‖^{−a}` finite iff `a<u`; `a≥u`: keep full C-integral, fact-(ii) gammaAtom needs `c'>au/2` +
  produces `det(Q̃ₚQ̃ₚᵀ)^{−a/2}`, disposed by fact (iii)/qbox at the PIVOT Gram, `a<q−u+1` — NOT the `Q_b`
  bound). Confirms my split + the qbox-on-pivot-not-corank care.
- **Q3:** det-P→0 is BENIGN (`[P|B₁₂]` right-inverse ⟹ `‖PR‖≥K⁻¹‖P‖`, no `|det P|^{−M₂}`) — conditional on
  the overall integral being locally finite (the `c'<D/2` radial-rank obstruction is separate, not a det
  obstruction). Confirms satred's structural resolution.
- **Q4:** the corank rank-defect locus `{rank Q_b<b}` IS covered by fact (iii)/strong-block (`a<m−b+1`);
  the two uncovered risks (folded to §3): the PROJECTED Gram `Q_b(I−P_R)Q_bᵀ` degenerating as `Row Q_b→Row
  Q̃ₚ`, and `Z_deep` singular values → 0 (`t^{−ab}` scaling) — both must be carried by the reduced-chain IH,
  and the uniform-conditioning is Brick F's floor.

No wall; the finding is a SHARPENING of `C_hle`'s conditionality (blow-up+carry + Brick F floor are the
mechanisms), not a break.

## Close

- **Firmest result.** Brick D = the front-block CoV `shellSpine ≤ C_hle · deeperFlagCore` (verbatim contract
  §1), whose per-arm core is `C_hle < ⊤` via arm-A<U (clean R2 leaf + sphere disposal, a<u), arm-A≥U (banked
  `gammaAtom_aniso_shifted_eq` + `qbox_lintegral_lt_top`), the P-block absorption (satred, det-P benign,
  codim-uρ via hpiv), and the Gram→`decLoss` decoration. The scaffolding is the decorated joint descent
  (sound), L1 is banked, the exponent gate is safe (0/22932), and the in-scope regime is strictly convergent
  (0/20874) — single-chain reaches `½minAdm M` via cut-soundness. NO `(□)` wall.
- **Most likely to break the BUILD.** (i) The **two SCOPE FORKS (§4-P3)**: the log-tie (`a+b=m+1`) and `a=0`
  saturation are (a) out-of-scope / (b) satred-content — a build that tries to force them through the clean
  interior arm will hit the strong-block log-divergence (tie) or mis-apply the corank route (a=0). Resolve by
  the two recommended guards (`hcvg` as-is + delegate tie; add `a≥1` + delegate saturation). (ii) Citing
  `qbox` for the CORANK `Q_b` Gram (the `a=q−b+1` trap) instead of the PIVOT `Qt` Gram. (iii) The a<u/a≥u
  split MUST be taken (one route does not cover both — `∫‖v‖^{−a}` diverges for a≥u). (iv) Dropping the
  P-radial blow-up decoration (reducing to bare `routeMLayerBoxIntegral(redChain)` — Codex-unsound).
- **Next construction.** Build Brick F (measurable frame, moderate), then Brick D by S-a..S-f, dispatching
  the C-integral on `a<u` vs `a≥u`; the two scope guards are the controller's call to bake into the
  statement before the tide. I pin the exact per-arm sub-lemma statements (a<u sphere-disposal; a≥u
  gammaAtom+qbox instantiation) on request once F is up.

Files (absolute):
- `…/threads/genm-satred/brickD-pin.md` (this pin); `D-cert.md`, `satred-cert.md`, `backbone-cert.md`
- `…/threads/genm-satred/scripts/brickD_scope.py` (the exact scope scan, 22932 cuts, 0 fails)
- `…/threads/genm-satred/codex/brickD-{prompt,answer}.md` (decorrelated, conclusion withheld)
- Lean: `RouteMSJDeeperFlagCore.lean` (:513 Brick D, :492 Brick F, :368 L1 BUILT, :655/:750 assembly)
