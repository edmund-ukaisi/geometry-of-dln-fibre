# (D) design cert — the JOINT determinantal rank-sector resolution (deep-corank + saturated A>2Δ)

**Seat:** pen-and-paper (design, decorrelated), `genm-satred`, follow-on. **Date:** 2026-07-16.
**NO Lean.** Math design only. Verified THREE ways: my exact-`ℕ` + sublevel-volume numerics
(`scripts/{joint_corank,corner_rlct,strata_recursion,AvsDelta}.py`), corneradj's **independent**
per-stratum derivation (`genm-corneradj`, `scripts/strata.py`), decorrelated Codex (repo-grounded,
`codex/D-{prompt}.md` + `D-run.log` — the answer file did not finalize cleanly, Codex's read-only
sandbox rejected its own script runs; the substantive Close was captured in the run log). Consumes
corneradj's `edge-design-cert.md` (the k=1 edge + frontier map) and couplerad's `corankaxis.py`.

---

## ★ VERDICT

**(D) CONVERGES. The joint determinantal rank-sector resolution REACHES the threshold `½·minAdm M` for
BOTH the deep-corank cells (`a≥1, b≥1, a+b≥ρ+2`) AND the saturated `A>2Δ` cells (`a=0`). NO `(□)` wall.
The controller's KILL-condition is NOT triggered — no cell undershoots via the joint resolution.**

The single-chain / factored / pointwise routes DO undershoot (that is corneradj's + my earlier finding),
but the **joint** resolution — resolving the corank rank-sector and the deep factor **together**, reducing
each stratum to a *different* arity−1 chain — reaches `½·minAdm M` because its exponent count **is the
`minAdm` recursion realized geometrically**. This is one mechanism, two matrix-shape instances.

---

## 1. Part 1 — convergence (the `(□)`-critical check): REACHES `½·minAdm M`

**The truth (rigorous, not numerical).** Every corner shell integrand `∫_{A'∈shell} ∫_{x∈outerDom} ∫_Γ
freedSchurLoss(x,Γ,Q)^{−c'}` is `≤ RouteMLayerBoxIntegral(M)|_{P-block invertible}` — the Schur weld
(`chartInner_schurWeld_eq`, `RouteMSJChartShear`, measure-preserving) rewrites `freedSchurLoss` as the
front-factor chart loss, and the shell (⊆ full `A'` box) + `outerDom` (⊆ block box) + the `Γ` shear-image
are a SUB-region (integrand `≥0`). Hence the corner RLCT `≥ ½·minAdm M` (Aoyagi / the geometric codim).
**So the corner cannot undershoot in the truth.** (Numerics consistent: sublevel-volume slopes
`(2,1,2,2)@t=0 → 1.0`, `(2,2,3,3)@t=0 → 2.0`, `(2,2,2,2) SAT → 1.5`, all `= ½·minAdm M`, slow by
multiplicity/MC-noise, `corner_rlct.py`.)

**Why the single-chain / factored / pointwise routes UNDERSHOOT** (verified, exact). Locking the reduction
to the single chain `redChain u M` (equivalently corneradj's `{Γ=0}` clean route, or my saturated pointwise
density fold) gives the per-stratum reduction (corneradj, independent; matches my `joint_corank.py` to the
digit)

    red_r = a·r/2  [Γ-image dim a·r]  +  (b−r)(ρ−r)/2  [A_cor codim to rank ≤ r],   r = rank(A_cor·Zf),

with `min_r red_r = ab/2 − (k−1)/2` at `k = a+b−ρ ≥ 2` (top stratum `r=b` gives `ab/2`; a DEEPER stratum
`r<b` strictly binds). Numeric check (`joint_corank.py`, `S` fixed generic rank `ρ`): `a=2,b=1,ρ=1` →
`0.494` (`=1/2`, not `ab/2=1`); `a=3,b=1,ρ=2` → `1.00` (not `3/2`); `a=1,b=1,ρ=1` edge → `0.5` (the `r=b`,
`r=b−1` TIE = the log/multiplicity bump). **The saturated `A>2Δ` cells are the DUAL** (front factor
`[P|B₁₂]·Y`, `a=0`): single-chain shortfall `A/2 − Δ`, and at the tight cells it equals `(k−1)/2` exactly
[`(2,3,4,4)`, `(2,2,2,2)`, `(2,2,3,3)`: all `= 1/2`]. So corank shortfall `(k−1)/2` and saturated shortfall
`A/2−Δ` are one phenomenon, two blocks.

**Why the JOINT rank-sector REACHES `½·minAdm M`** (verified, exact — `strata_recursion.py`). The corank
rank-drop `(b−r)` dropped rows **re-peel to a deeper effective cut** `u' = u + (b−r)`, so stratum `r`
reduces to `redChain u' M` (an arity−1 IH instance — a *different* chain per stratum, NOT locked to
`redChain u M`). The exponent bookkeeping is then the `minAdm` recursion's min-over-cuts:

    min_r [ peelCharge(u') + minAdm(redChain u' M) ]  =  minAdm(M),   u' = u + (b−r).

Checked: `(2,1,2,2)@0`: `min(r=0→u'=1: 0+2, r=1→u'=0: 2+0) = 2 = minAdm` ✓; `(2,2,3,3)@0`:
`min(5,4,4)=4` ✓; `(4,2,3,4)@1`: `min(6,6)=6` ✓; `(2,3,4,4)@0`: `min(…)=6` ✓. So the joint reaches
`½·minAdm M` via `∀`-arity−1 IH. **This is `minAdm`'s own recursion, realized geometrically as the corank
rank-sector.** The single-chain undershoot is exactly the failure to leave `redChain u M` for the binding
`u'`.

**Decorrelated Codex (repo-grounded).** Independently reaches: the joint incidence-rank resolution gives
`min_strata C_{ℓ,s}/2 = T1` (`=½·minAdm`) **exhaustively (332/332 in-scope binding cuts, widths 2..8)** —
"NOT a wall; the hard configs are absorbed by the `z`-integration." Two flags, both consistent with the
above: (i) a **pointwise-in-`z`** bound is FALSE (a rank-drop `Q_p` gives a `δ^{5−2q}` blow-up) — the
domination must be **integrated** (i.e. JOINT, not factored — matches §2); (ii) Codex's route needs scope
`a+b ≤ M₂` (`detGram_lintegral_box_lt_top`). **corneradj (independent) resolves (ii): `a+b≤M₂` is an
ARTIFACT of the FACTORED corank-Gram route, NOT load-bearing for the joint `{Γ=0}`/rank-sector route.** It
is the factored front-charge convergence bound (`Ch<∞ ⟺ a+b≤ρ`, `=M₂` when `Zdeep` is full row rank) — i.e.
exactly the INTERIOR regime where the factored route works; beyond it (`a+b≥ρ+1`) the factored charge is
`+∞` and (A)/(D) exist precisely to replace it. The joint route NEVER forms the corank-Gram: the `ab/2` (top
stratum) is the codim of `{Γ=0}` via the polar `s^{ab−1}`; deeper strata use the CoV `Y=Γ·Q_b` onto the
rank-`r` IMAGE (dim `a·r`), whose `r×r` Gram is non-degenerate ON that stratum by construction — no global
Gram-integrability is invoked. `(2,1,2,2)@0` (`a+b=3 > M₂=2`, reaches `minAdm=2`) confirms it. **So drop
`a+b≤M₂` from (D)'s hypotheses.** The genuine structural bound is the **rank range `r ∈ 0..min(b,ρ)`**: if
`b>ρ`, `Q_b=A_cor·Zf` cannot reach rank `b` (rank `≤ρ`), so the TOP stratum is `r=ρ` (cut `u'=u+(b−ρ)`),
not `r=b` — a *shifted* top, still reaching `minAdm` via the min-over-cuts (verified `(2,3,1,1)`,
`(3,4,1,1)`, `(2,4,2,2)`, `strata_recursion.py`), NOT a wall.

## 2. Part 2 — the mechanism (one principle, two instances)

The corank and deep factors are **ENTANGLED**: the `ab/2` corank charge is realized only when the deep
factor `S=Zdeep`'s rank-drop is integrated jointly. Verified sharply: with `S` FIXED generic
(`joint_corank.py`) the corank charge undershoots `ab/2` (it computes corneradj's single-chain `red_r`); with
`S` integrated (the honest corner, `corner_rlct.py`) it reaches `½·minAdm`. So the resolution must be
**joint** (corank `(Γ, A_cor)` AND deep `S` together), never factored (corank-then-deep) nor pointwise-in-`z`.

**Two matrix shapes** (corneradj Q3 — do NOT collapse to one `frobSq` for the deep corank):
- **Deep corank (`a≥1, b≥1`, `k≥2`):** the two-block `freedSchurLoss = frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ +
  Γ·Q_b)`, `Q_b = A_cor·Zf`. The corank term carries the `(Γ, A_cor)` rank-sector; the pivot term is the
  `redChain` comparator. Same `shellSpineIntegrand` def, NOT recombined.
- **Saturated (`a=0`):** the corank term vanishes (0 rows), `z̃₀ = [P|B₁₂]·[z₀;A_cor]` recombines into the
  single `frobSq(z̃₀·Zdeep)` front reassembly (satred `satred-cert.md` §3). The rank-sector is on the front
  factor `[P|B₁₂]·Y`.

The **joint-rank-sector PRINCIPLE** unifies them: *the loss's own vanishing on the joint low-rank locus
pays the factor's density/charge singularity; `min` over the rank strata `= minAdm(M)`.* The `A>2Δ` (front,
`a=0`) and `k≥2` (corank, `a,b≥1`) shortfalls are dual (§1). **(D) is one lemma, two instances.**

## 3. Part 3 — Lean-friendly design

**Object.** The two shapes above (state `freedSchurLoss` for `a,b≥1`; the front reassembly `frobSq(z̃₀·Zdeep)`
for `a=0`). Target, per-exponent, `c' < ½·minAdm M`:

    shellSpineIntegrand M u κ ε r ⟨j⟩ c'  ≤  Σ_r  C_r(ε) · RouteMLayerBoxIntegral (redChain u_r M) (q_r) T★,
    u_r = u + (b − r),   q_r = c' − red_r,   with  min_r [ red_r-charge realized + ½minAdm(redChain u_r M) ] = ½minAdm M.

**The joint rank-sector reduction (steps, atomic, carry `|det J|`).**
1. **Minor chart on `Q_b`.** `Q_b = A_cor·Zf`; pick a full-rank `min(b,ρ)`-minor chart `Q_b = D·[I | X]`
   (Codex's `Q_b = D[I|X]`) — a finite cover by which `b×b`/`ρ×ρ` minor is invertible (cf. satred's
   full-rank-minor guard for `[P|B₁₂]`; the minor is bounded below a.e., det-P→0 benign). **Carry the minor
   Jacobian.**
2. **Shear** the pivot/corank coupling `H = P·U + B·D` (Codex) — the banked Schur shear that frees the
   corank block (measure-preserving, `RouteMSJChartShear`).
3. **Stratify `rank(A_cor·Zf) = r`, `r ∈ 0..min(b,ρ)`** and blow up each rank-`r` determinantal stratum.
   **Carry `|det J|`**: the `Γ`-polar part contributes `s^{ab−1}` (corneradj Step C); the `A_cor` rank-`r`
   part contributes the determinantal-stratum Jacobian (codim `(b−r)(ρ−r)` — the `C_{ℓ,s}` monomial
   exponents). **NEVER drop the Jacobian (the recurring tide-D KILL guard).** [Top stratum `r=min(b,ρ)`; if
   `b>ρ` it is `r=ρ`.]
4. **Reduce stratum `r` to `redChain u_r M`**, `u_r = u+(b−r)` (arity−1 IH), at exponent `q_r`. The residual
   deep integral is the comparator `RouteMLayerBoxIntegral(redChain u_r M)`, finite by the arity-IH. **[This
   `u_r`-cut map is the DEEP-CORANK (`a,b≥1`) instance. The SATURATED (`a=0`) instance uses a DISTINCT
   rank-sector — on the front factor `[P|B₁₂]·A₀` via the density-order `A` (satred `satred-cert.md` §4), NOT
   the `u_r`-cut map (`u` is already `min(M₀,M₁)`, cannot peel deeper). Same PRINCIPLE, different reduced
   object; the `A>2Δ` saturated cells are the ones needing (D)'s saturated instance, the `A≤2Δ` are clean.]**
5. **Sum/min over `r`.** The per-stratum exponents `red_r` (`=` `C_{ℓ,s}/2`) satisfy `min_r [ charge(u_r) +
   minAdm(redChain u_r M) ] = minAdm(M)` (the `minAdm` recursion, `strata_recursion.py`; banked
   `minAdm_le_peelCharge_add_redChain`, `RouteMSJResolution:204`). So the sum is finite for `c'<½minAdm M`.

**Banked pieces consumed.** `freedSchurLoss` / the weld / `blockSplitEquiv` (RouteMSJChartShear); the arity-IH
`∀ M':Fin(L+1+1), RouteMBoxThresholdFinite M'` (`sjStepHyp_of_coupled`, arch1build @4dff27df1); the `minAdm`
recursion (`peelCharge`, `minAdm_le_peelCharge_add_redChain`); corneradj's edge `{Γ=0}` polar-`Γ` (Step C,
the top stratum `r=min(b,ρ)`) + angular-`J`-finite (the `k=1`/`r=b−1` tie); `uniformWenn_proj_le` /
`offSector_cover_le` (shell cover, the deep rank on the shell). (`detGram_lintegral_box_lt_top` /
`a+b≤M₂` belongs to the FACTORED route only — the joint route does not invoke it, §1.) **New content:** the per-stratum
determinantal blow-up + the min-over-strata `= minAdm` recursion (the JOINT resolution). **Diamond guard:**
raw-`Pi` instances for all matrix products/reindexes (`lean/CLAUDE.md`).

**Discipline (from the corner over-call pattern + Codex).** (a) Keep the resolution **JOINT** — a
pointwise-in-`z` bound is FALSE (rank-drop `Q_p` blow-up); (b) do NOT lock to the single chain `redChain u M`
— it undershoots by `(k−1)/2` at `k≥2`; use the per-stratum chains `redChain u_r M`; (c) claim the VALUE
`½·minAdm`, not a multiplicity (the `r=b`/`r=b−1` tie gives a log at `k=1` — do not claim `m`); (d) coords
atomic, carry `|det J|`; (e) do NOT form the global corank-Gram / require `a+b≤M₂` (that is the factored route; the joint uses the rank-`r` image Gram, non-degenerate per stratum); carry the r-range `0..min(b,ρ)`.

## 4. Scope finding (for the controller / corneradj — the cut-selection axis)

The peel cut `t★` is **freely choosable** (cut-soundness `flagCharge_ge` holds for ALL cuts, not just
binding). Shells at `t★` have corank `k_j = k_0 − 2j` (`k_0 = M₀+M₁−2t★−ρ`). Choosing `t★` with `k_0 ≤ 1`
makes ALL shells clean (`k≤1`, edge/interior) — **avoidable for 1814/2401 chains** (widths ≤7). But **587
force `k_0 ≥ 2`** at every cut (e.g. `(1,4,1,1)`, `ρ=1`, min `k_0=2`) — and the **saturated shell `j=r` (cut
`min(M₀,M₁)`) is unavoidable** regardless of `t★`. So (D) is needed for: the *forced* deep-corank
(`a,b≥1`, `k≥2`) cells + the saturated `A>2Δ` cells. (This refines corneradj's open question: cut-selection
prunes MOST but not ALL deep-corank; the saturated corner is never pruned.)

## Close

- **Firmest result.** (D) CONVERGES — the joint rank-sector reaches `½·minAdm M` for the deep-corank AND
  saturated `A>2Δ` corners, verified three ways + the rigorous `⊆ RMBTF(M)|_chart` truth. The mechanism:
  the corank rank-drop `(b−r)` re-peels to cut `u_r=u+(b−r)`, reducing stratum `r` to `redChain u_r M`
  (arity−1 IH), and `min_r[peelCharge(u_r)+minAdm(redChain u_r M)] = minAdm(M)` — `minAdm`'s recursion
  geometrically. One principle, two instances (corank two-block; saturated front reassembly), dual
  shortfalls `(k−1)/2` ↔ `A/2−Δ`. **NO `(□)` wall.**
- **Most likely to break the BUILD (not the math).** A tide that (i) bounds pointwise-in-`z` (FALSE), or
  (ii) locks to the single chain `redChain u M` (undershoots by `(k−1)/2` at `k≥2`), or (iii) factors the
  corank-Gram out of scope `a+b≤M₂`, or (iv) drops a stratum Jacobian, will thrash on never-landed content.
  Keep it joint, multi-chain, det-Gram coupled, `|det J|` carried.
- **Next construction.** The formaliser builds the per-stratum determinantal blow-up (minor chart → shear →
  rank-`r` strata → per-stratum comparator ratio → min/sum). The exponent arithmetic (`min_r = minAdm`
  recursion) is the reusable, DONE certificate (`strata_recursion.py`; corneradj `strata.py`; Codex 332/332).
  The remaining labour is the chart maps + Jacobians + the per-stratum comparator ratio `C_r < ⊤` — explicit
  above, one genuinely-new determinantal-resolution lemma reused across both instances.

Files (absolute):
- `…/threads/genm-satred/D-cert.md` (this cert); `satred-cert.md` (the a=0 saturated design it extends)
- `…/threads/genm-satred/codex/D-{prompt}.md`, `D-run.log` (decorrelated Codex, repo-grounded)
- `…/threads/genm-satred/scripts/{joint_corank, corner_rlct, strata_recursion, AvsDelta}.py`
- `…/threads/genm-corneradj/edge-design-cert.md` (the k=1 edge + frontier map, consumed)
