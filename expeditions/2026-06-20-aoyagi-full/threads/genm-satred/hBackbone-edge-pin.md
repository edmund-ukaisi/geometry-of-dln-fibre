# hBackbone-edge-pin — the EDGE coupled descent lemma (edgefub's hBackbone), pinned

**Seat:** pen-and-paper (design, decorrelated), `genm-satred`. **Date:** 2026-07-16. **NO Lean edits.**
Pins the exact statement + proof design of the edge-tie coupled descent (edgefub's `hBackbone`), matching
`edgefub`'s EDGEREDUCED verbatim. Verified: exact-ℕ (`scripts/edge_coupled_reach.py`,
`edge_coupled_classify.py`, `edge_twochain.py`), decorrelated Codex xhigh (`codex/edgereach-{prompt,answer}.md`,
conclusion withheld), edgefub's banked leaf (`coupledInner_slice_le` @cf940ee47) + δ-atoms (`RouteMSJEdgeAtoms`).

---

## ★ VERDICT — the tie-log is NOT dissolved (but is HARMLESS); hBackbone is the TWO-CHAIN joint rank-sector

The controller's hope — the coupled route DISSOLVES the corank-one tie-log (cleaner than the decorated
route) — does **NOT hold**, and I verified this rather than assert the clean story:
- **Decorrelated Codex (Q2):** the coupling **RELOCATES** the tie-log (hides it as a rank-sector tie), it
  does NOT remove it; but "a logarithm is harmless for every strict inequality `c < ½minAdm(M)`."
- **Codex (Q1):** the single-chain-with-log route is **NOT justified** — log slack absorbs logs but cannot
  repair the positive **power deficit** the naive pointwise density fold leaves (`A > 2Δ+a` for a majority
  of b=1 cuts, `scripts/edge_coupled_classify.py`). So the edge is **NOT single-chain**.
- **Codex (Q3, model-independent = the `minAdm` recursion):** the **JOINT rank-sector** reaches
  `c < ½minAdm(M)` EXACTLY: `min_t(D(t)+R(t)) = minAdm(M)`, the `a<u` sphere costs nothing, and the sector
  logs affect only pole multiplicity — **no residual RLCT loss**.

**So hBackbone = the JOINT rank-sector descent (arity-IH), reaching `½minAdm(M)` exactly, with the tie-log a
HARMLESS multiplicity (δ-slack).** For `b=1` this is a clean **TWO-chain** reduction (verified reach
**0/1076** edge-tie cells, `scripts/edge_twochain.py`). This SUPERSEDES my earlier "single-chain
`RMBTF(redChain u M)(c'−a/2)`" steer to edgefub — that hypothesis alone is insufficient.

## 1. The object (edgefub's EDGEREDUCED, verbatim)

    EDGEREDUCED := ofReal(C_a · 2^a · 2^{a·u}) ·
      ∫_{p ∈ paramsBoxM (redChain u M) 1 ×ˢ matBox (M₁−u) M₂ 1} |v'_{j₀}(p)|^{−a} ·
        ∫_{pb ∈ outerPB} frobSq (P · Q̃ₚ(pb,p)) ^ (a/2 − c')

`u = t+j`, `a = M₀−u ≥ 1`, `b = M₁−u = 1` (edge), `a < u`, the tie `a = ρ = tailMinWidth M`;
`Q̃ₚ = Q_inl + P⁻¹B₁₂·Q_inr`, `Q_inl,Q_inr` from `hsQ M u (deeperFlagZdeep M u) p.1 p.2`; `C_a =
scaledRadialEuclid`'s constant (`∫_{ℝ^a}(1+‖s‖²)^{−c'}`, finite since `c'>a/2`); `a/2−c' = −(c'−a/2)`.
(Radial pre-collapsed by `scaledRadialEuclid_eq`, `|v'|^{−a}` kept jointly — my earlier (1)+(2).)

## 2. The pinned hBackbone statement

    edgeBackbone :
      (hIH : ∀ M' shorter chain, RouteMBoxThresholdFinite M')        -- the arity-IH (sjStepHyp_of_coupled)
      → (frame facts for deeperFlagZdeep M u from Brick F: hUs, hrank, hfloor, hagree)
      → (a.e.-positivity: v'_{j₀}(p)≠0 a.e., q_b≠0 a.e., W>0 a.e. — from the frame + rank-genericity)
      → (ht1 : 1 ≤ t) (hnd) (a<u) (b=1) (the tie a=ρ) (hc' : a/2 < c') (c' < ½minAdm M)
      → EDGEREDUCED < ⊤.

**Interface correction (vs my earlier single-chain steer):** the hypothesis is the **arity-IH** (all
shorter chains), NOT just `RMBTF(redChain u M)(c'−a/2)`. The proof (§3) consumes exactly two of them:
`RouteMBoxThresholdFinite (redChain u M)` and `RouteMBoxThresholdFinite (redChain (u+1) M)`. Both are
arity−1 (`u+1 = M₁ ≤ min(M₀,M₁)` since `M₀≥M₁` at the edge — verified valid 0/1076). edgefub's
`edge_coupledBox_lt_top` threads the arity-IH into `edgeBackbone`.

## 3. The proof design — the b=1 two-sector joint rank-sector

The C-integral is edgefub's banked leaf (`coupledInner_slice_le`, per-fixed-pb); the outer descent is:

**(D-a) Coupled identification.** `frobSq(P·Q̃ₚ) = frobSq([P|B₁₂]·[z₀;A_cor]·Z_deep) = frobSq(z̃₀·Z_deep)`,
`z̃₀ = X·Y`, `X=[P|B₁₂]` (u×M₁, full row rank u — det-P benign, satred), `Y=[z₀;A_cor]` (M₁×M₂),
`z̃₀·Z_deep = prod(redChain u M)` with the leading layer replaced by `z̃₀`. So `∫_{pb} frobSq(P·Q̃ₚ)^{−(c'−a/2)}`
is the front-layer integral of `redChain u M` at the shifted exponent.

**(D-b) Stratify `rank(A_cor·Z_deep) = r ∈ {0,1}`** (b=1 corank; the two critical sectors, D-cert §3, each
codim `a` — the corank-one TIE):
- **r = 1** (generic, `A_cor·Z_deep ≠ 0`): the `X·Y` identification reduces to `redChain u M` at
  `c'−a/2` (charge `a/2 = peelCharge(u)/2`, `peelCharge(u)=a·1=a`). Reaches via
  `RouteMBoxThresholdFinite (redChain u M)` and cut-soundness `a + minAdm(redChain u M) ≥ minAdm(M)`.
- **r = 0** (`A_cor·Z_deep = 0`, the codim event): re-peel to cut `u+1`, reduce to `redChain (u+1) M` at
  `c'−a/2`. Reaches via `RouteMBoxThresholdFinite (redChain (u+1) M)` and cut-soundness at `u+1`
  (`peelCharge(u+1) = (a−1)·0 = 0`, so `minAdm(redChain (u+1) M) ≥ minAdm(M)`).

**(D-c) The TIE → harmless log.** Both sectors have charge `a/2` (codim `a`); the coincidence gives a LOG.
It is absorbed by the **δ-slack** (`one_add_log_inv_le_rpow`, banked `RouteMSJEdgeAtoms`), using the STRICT
headroom `c'−a/2 < ½minAdm(each chain)` (both strict, verified 0/1076): pick `δ>0` with `c'−a/2+δ <
½minAdm(each chain)`, apply the IH at the bumped exponent. Harmless for strict `c'<½minAdm(M)` (Codex Q2/Q3:
multiplicity, no threshold shift).

**(D-d) The `|v'_{j₀}|^{−a}` disposal.** `∫_{ω} ‖Q̃ₚ ω‖^{−a} dω` finite iff `a<u` (`ker Q̃ₚ` codim u;
`corner_block_lintegral_lt_top`) — a bounded constant, **costs nothing** (Codex Q3: "the sphere factor costs
nothing precisely under `a<u`"). The per-p `j₀(p)` is a **measurable argmax** selector (`j₀(p) = argmax_j
|v'_j(p)|`, measurable since `v'(p)≠0` a.e.) — Brick-F-adjacent; edgefub offered to bank the standalone
helper `∃ measurable j₀ : ∀ᵐ p, v'_{j₀(p)}(p)≠0` (ACCEPT — self-contained given `v'≠0` a.e.).

**Net:** `EDGEREDUCED ≤ (const) · [RMBTF(redChain u M) term + RMBTF(redChain (u+1) M) term]`, both finite for
`c'<½minAdm(M)`; the tie-log is δ-folded. Reaches `< ⊤`.

## 4. Scope / ownership (edgefub's confirmed division)

edgefub OWNS: `coupledInner_slice_le` (the (C,Γ) leaf, per-fixed-pb, positivity as hypothesis) + the radial
collapse + `edge_coupledBox_lt_top` (= cell-drop a-fortiori ∘ `edgeBackbone` ∘ arity-IH). **edgeBackbone
OWNS:** the `outerDom`-peel, the a.e.-positivity (consumes Brick-F frame facts + rank-genericity), the
`|v'|`/`j₀` disposal, the coupled `[P|B₁₂]↔leading-layer` identification, the two-sector stratification, the
tie-log δ-fold. Banked for edgeBackbone: `outerDom_lintegral_prod`, `scaledRadialEuclid_eq/_lt_top`,
`one_add_log_inv_le_rpow` + `sigmaLog_integral` (`RouteMSJEdgeAtoms`), `corner_block_lintegral_lt_top`,
`minAdm_le_peelCharge_add_redChain` (cut-soundness), the Brick-F frame contract. **Diamond guard:** raw-`Pi`.

## ★ hFrontReduce — the ROUTE-AGNOSTIC front-block reduction interface (for edgefub half-B)

edgefub builds `edge_coupledBox_lt_top` conditional on the abstract, route-agnostic box-finiteness of the
TWO sector chains. This is the exact reduction shape (my seam) — the DISCHARGE (u≤2 plain-RMBTF vs u≥3
decorated, per q2gate's split) folds in at assembly, so this statement is route-AGNOSTIC.

**The route-agnostic predicate** (edgefub instantiates it; hFrontReduce is indifferent):

    boxFinite (M' : Fin (L+1+1) → ℕ) (e : ℝ) : Prop  :=  routeMLayerBoxIntegral M' e 1 < ⊤

(`routeMLayerBoxIntegral` is the reduced box integral; `boxFinite` is satisfied by plain-RMBTF at u≤2 and by
the decorated/weighted box at u≥3 — the discharge picks which, at assembly. hFrontReduce only consumes
`boxFinite`, never how it's proven.)

**The pinned statement** (edge scope: `u = t+j`, `a = M₀−u`, `b = M₁−u = 1`, `a < u`, the tie):

    hFrontReduce {L} (M : Fin (L+1+1+1) → ℕ) (t j : ℕ) (κ : Fin (t+j) ↪ Fin (M 1))
      {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
      (hb1 : M 1 - (t+j) = 1)                                  -- b = 1  (edge)
      (hau : M 0 - (t+j) < t+j)                               -- a < u
      (hc' : ((M 0 - (t+j) : ℕ) : ℝ)/2 < c')                  -- c' > a/2  (= ab/2 at b=1)
      (hcarr : c' < carrierThreshold M)                       -- c' < ½·minAdm M
      (hnd : ∀ i, 1 ≤ M i) (ht1 : 1 ≤ t)
      -- the ROUTE-AGNOSTIC box-finiteness of the TWO sector chains, both at the SHIFTED exponent c'−a/2:
      (h_u  : boxFinite (redChain (t+j) M)     (c' - ((M 0 - (t+j) : ℕ):ℝ)/2))     -- sector r=1 (generic)
      (h_u1 : boxFinite (redChain (t+j+1) M)   (c' - ((M 0 - (t+j) : ℕ):ℝ)/2))     -- sector r=0 (A_cor·Z_deep = 0)
      -- Brick-F frame facts + a.e.-positivity (rank-genericity of Q_inl; v'_{j₀}≠0 a.e.; the measurable j₀ selector):
      (hframe : <the Brick-F frame data for deeperFlagZdeep M (t+j) + the a.e.-positivity clauses>) :
      EDGEREDUCED M (t+j) κ ε c' < ⊤

where **`EDGEREDUCED M u c'` is edgefub's PER-CELL form (NO κ, ε — corrected; κ/ε are consumed upstream in
`shellSpine_le_coupledBox` → the per-cell `coupledBoxIntegrand M u c' p`):**

    EDGEREDUCED M u c' := ofReal(C_a · 2^a · 2^{a·u}) ·
      ∫_{p ∈ paramsBoxM (redChain u M) 1 ×ˢ matBox (M₁−u) M₂ 1} |v'_{j₀}(p)|^{−a} ·
        ∫_{pb ∈ outerPB u (M₁−u) 1} frobSq(P · Q̃ₚ(pb,p)) ^ (a/2 − c')

`v'(p) = Q_inl(p)·ω(p)`, `ω(p) = q_b(p)/‖q_b(p)‖`, `Q_inl/q_b` from `hsQ M u (deeperFlagZdeep M u) p.1 p.2`,
`j₀` the measurable selector (`exists_measurable_nonzero_index`); `C_a = scaledRadialEuclid` const. **LOCK
to edgefub's verbatim half-A Lean def when it lands** (edgefub OWNS the `EDGEREDUCED` def — I target it).
[The earlier `EDGEREDUCED M u κ ε c'` was shell-spine-level, one level too high; the per-cell form is what
`GenericCellFinite`/`h_edge_b1` needs.]

**Both sector hyps at the SAME shifted exponent `c'−a/2`** (b=1 ⟹ peelCharge = a·b = a ⟹ shift = a/2; both
sectors codim a — the corank-one tie), and **both reach for `c'<½minAdm M`** via cut-soundness (verified
0/1076 `scripts/edge_twochain.py`: `a + minAdm(redChain (t+j) M) ≥ minAdm M` and `a + minAdm(redChain
(t+j+1) M) ≥ minAdm M`; `u+1 = M₁` is a valid cut since M₀≥M₁ at the edge).

**Proof shape (my seam, route-agnostic — edgefub does NOT build this discharge):** stratify `rank(A_cor·Z_deep)
∈ {0,1}`; r=1 (generic) → the coupled `[P|B₁₂]↔leading-layer` X·Y identification reduces `∫_{pb} frobSq(P·Q̃ₚ)^{−(c'−a/2)}`
to `boxFinite(redChain (t+j) M)(c'−a/2)` (`h_u`); r=0 (`A_cor·Z_deep=0`, re-peel to cut u+1) → `boxFinite(redChain
(t+j+1) M)(c'−a/2)` (`h_u1`); the `|v'_{j₀}|^{−a}` disposed by the `a<u` sphere-finiteness; the corank-one
tie-log δ-folded (`one_add_log_inv_le_rpow`, banked, via the strict headroom). **The u≥3 X·Y-descent wall
(decstep's crux) lives INSIDE proving `boxFinite` (the discharge), NOT in hFrontReduce** — so edgefub's
half-B (which consumes `h_u`,`h_u1` abstractly) is fully off that wall.

**Composition + OWNERSHIP (corrected):** `edge_coupledBox_lt_top = cell-drop ∘ coupledInner_slice_le` (edgefub's
half-A leaf) `∘ hFrontReduce`. **I DESIGN hFrontReduce (the two-sector reduction math — this §, pinned);
edgefub BUILDS it in Lean (half-B), consuming this design + the abstract `boxFinite`** (I'm pen-and-paper,
NO Lean — my earlier "I own/build" was a misstatement; per the controller's steer, edgefub builds the
reduction). The two `boxFinite` hyps are discharged at ASSEMBLY (decstep): u≤2 → plain RMBTF; u≥3-inheritors
→ the decorated/weighted box. Route-agnostic here. I'm available for the design details (the X·Y
identification, the |v'|^{−a} a<u sphere, the tie-log δ-fold) as edgefub builds.

## Close

- **Firmest result.** hBackbone (edge, b=1) = the two-chain joint rank-sector: `r∈{0,1}` → `redChain u M`
  and `redChain (u+1) M`, both at `c'−a/2`, both reaching via cut-soundness (0/1076), the corank-one TIE a
  harmless-multiplicity log (δ-slack). Takes the arity-IH (not single-chain). Reaches `EDGEREDUCED < ⊤` for
  `c'<½minAdm(M)`. **The tie-log is RELOCATED not dissolved (Codex-confirmed) — but harmless at strict c'.**
- **Most likely to break the BUILD.** (i) Stating hBackbone single-chain (`RMBTF(redChain u M)` alone) —
  INSUFFICIENT (Codex Q1: log can't repair the power deficit); must take the arity-IH and use BOTH chains.
  (ii) Trying to make the edge log-FREE (a clean fold) — impossible (Codex Q2); the δ-slack is required.
  (iii) The `j₀` selector needs measurability (argmax) — not a bare `Classical.choice`. (iv) Forgetting the
  `a<u` hypothesis (the sphere disposal diverges at `a≥u`).
- **Next.** Pin done. edgefub wires `edge_coupledBox_lt_top` once this is banked; the standalone `j₀`
  measurable-selector helper is edgefub's to bank (accepted). A dedicated tide builds `edgeBackbone`
  (the two-sector descent + δ-fold) — the analytic core; everything it consumes is banked.

Files (absolute):
- `…/threads/genm-satred/hBackbone-edge-pin.md` (this pin); `D-cert.md` §2/§3 (the joint rank-sector),
  `satred-cert.md` (the X·Y coupled identification), `brickD-pin.md` (the interior sibling)
- `…/threads/genm-satred/codex/edgereach-{prompt,answer}.md` (decorrelated, conclusion withheld)
- `…/threads/genm-satred/scripts/{edge_coupled_reach,edge_coupled_classify,edge_twochain}.py` (exact-ℕ)
