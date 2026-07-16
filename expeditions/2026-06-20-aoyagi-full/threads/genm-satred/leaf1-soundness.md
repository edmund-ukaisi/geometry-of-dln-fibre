# leaf1-soundness — route α (bare-constant front) is UNSOUND for the A>2Δ interior shells

**Seat:** pen-and-paper (design, decorrelated), `genm-satred`. **Date:** 2026-07-16. **NO Lean edits.**
Resolves brickf's HIGH-priority leaf-1 (`shellSpine_le_hsQ_box`) unprovability flag. Decorrelated Codex
xhigh (`codex/leaf1-{prompt,answer}.md`, conclusion withheld) + exact-ℕ (`scripts/leaf1_threshold{,2}.py`).

---

## ★ VERDICT

**brickf is correct: leaf-1 with `pivotShell(ε)` is FALSE for j≥1, and route α (bare-constant front `C_hle`)
is genuinely UNSOUND for ~8% of interior shells (the A>2Δ, small-a-b cells).** Those shells need route β
(the `det(GGᵀ)^{−·}` factor carried to the IH via qbox) — which does NOT fit `deeperFlagCore + L1` (the
`au/2` vs `ab/2` shift). So `deeperFlagCore + L1` (bare constant) covers ONLY the "easy" interior shells;
the "hard" A>2Δ shells belong with the edge tie / waist in a joint-rank-sector mechanism.

## 1. The pivotShell(ε) bug (Codex Q1, PROVEN)

`hsQ = [z₀;A_cor]·Z_deep` is a ROW-PERMUTATION of `prod(tailChain)A' = A'₀·Z_deep`, so shares its singular
values. On shell-j (`weakEigCount ε (prod) = j`, j≥1) exactly j SVs are `< ε`, so `hsQ·hsQᵀ ⋡ ε²·1`, so
`A_cor ∉ pivotShell(ε) = {hsQ·hsQᵀ ⪰ ε²·1}`. **pivotShell(ε) and the shell are DISJOINT** — restricting the
nonneg integral to `matBox ∩ pivotShell(ε)` drops the shell-j mass, so `shellSpine ≤ RHS` is FALSE for j≥1.
Root cause: the draft conflated `pivotShell(ε)` (full M₁-hsQ floor at ε) with the FRAME good-set
`G_frame(ε') = {weakEigCount ε' (Z_deep) ≤ M₂−m}` at the RESCALED `ε' ≤ ε/√(M₁M₂)` — the shell provably
sits in the latter (`hsSplit_good_of_shell`, Ky-Fan), NOT the former.

## 2. The bare-constant ceiling (Codex Q2/Q3 + my refinement)

- **Full matBox is non-uniform (Codex Q2, PROVEN):** the frame floor controls `Zf`, not
  `G = [z₀;A_cor]·Zf`; along `G_t = t·G₁`, `I(G_t) = t^{−2c''}·I(G₁)` — no bare constant (degenerates at
  `z₀=A_cor=0`). So "drop pivotShell → full box" fails.
- **The uniform ceiling is `u(M₁−j)/2`:** keeping the SHELL-domain, the shell gives `σ_{M₁−j}(G) ≥ ε`
  (`M₁−j = b+t` Gram-eigenvalues ≥ ε²), so `‖X·G‖ ≥ ε‖X·U_{M₁−j}‖` (U the top-(M₁−j) frame) yields a
  UNIFORM front bound iff `2c'' < u(M₁−j)` (the D-B on G's own top frame). This is the best uniform bound
  (the SVs beyond M₁−j are `< ε`, unconditioned → non-uniform). Codex's frame-m threshold `um`
  (m=min(M₁,M_last)−j) is weaker; the draft's `uρ` is **unjustified** (the shell conditions only the
  top-(M₁−j), not top-ρ; uρ needs `σ_ρ(G)≥ε`, false on the shell when M₁−j < ρ).

## 3. The easy/hard split (exact-ℕ, `scripts/leaf1_threshold2.py`, 76832 interior shells)

The `u(M₁−j)/2` bare-constant reaches `½minAdm(M)` (via `c'' = c'−ab/2 < u(M₁−j)/2`) **iff
`minAdm(M) ≤ ab + u(M₁−j)`**:
- **EASY (70742 shells): `minAdm(M) ≤ ab + u(M₁−j)`** — route α works: keep the shell-domain, threshold
  `u(M₁−j)/2`, bare constant → `deeperFlagCore + L1`.
- **HARD (6090 shells): `minAdm(M) > ab + u(M₁−j)`** — route α UNSOUND (bare constant caps at
  `u(M₁−j)/2 < needed`). E.g. `(2,2,3,3)@t=1,j=0` (a=b=u=1, minAdm=4 > ab+u(M₁−j)=3, undershoot ½).
  **UNAVOIDABLE** (for (2,2,3,3) the only interior shell is t=1,j=0). These are exactly satred's **A>2Δ**
  regime (small a,b). They need route β (carry `det(GGᵀ)^{−·}` to the IH via qbox).
  (Codex's `um` threshold fails for 15409; the refined `u(M₁−j)` recovers 9319 of those but 6090 remain.)

## 4. Architectural recommendation

Every route splits **easy** (bare-constant / clean fold) vs **hard** (A>2Δ, joint rank-sector, det-factor
to IH). The interior is NOT uniformly `deeperFlagCore + L1`:
- **easy interior** → `deeperFlagCore + L1` (bare constant, threshold `u(M₁−j)/2`, shell-domain kept);
- **hard interior (A>2Δ) + edge tie + waist saturated** → ONE joint-rank-sector mechanism (coupled,
  direct RMBTF, `det(GGᵀ)^{−·}` to the IH) — the SAME mechanism, differing only in which factor is
  stratified. This unifies the "hard" cells across all three routes.

**leaf-1 fix:** keep the shell-domain (the good-set where `σ_{M₁−j}(G)≥ε`, via `hsSplit_good_of_shell` /
the frame good-set), NOT `pivotShell(ε)` and NOT full matBox; threshold `u(M₁−j)/2`; guard
`minAdm(M) ≤ ab + u(M₁−j)` (the easy-shell scope). The hard shells route to the joint-rank-sector.

## Close

- **Firmest.** brickf's leaf-1 flag is correct (Codex-proven): `pivotShell(ε)` is disjoint from shell-j;
  the bare-constant front bound has ceiling `u(M₁−j)/2`; 6090/76832 unavoidable A>2Δ interior shells exceed
  it and need route β. Route α = easy interior only.
- **Most likely to break.** Building a bare-constant leaf for the hard shells (unsound); using `pivotShell(ε)`
  (false) or full matBox (non-uniform); the `uρ` threshold (unjustified).
- **Next.** Controller's architecture call: build the easy-shell leaf now (guarded) + a unified joint-rank-
  sector for hard interior + edge + waist. I'll pin the unified hard-cell mechanism (it's the coupled
  det-factor → qbox/IH, = the edge/waist route generalized) on the steer.

Files (absolute): `…/threads/genm-satred/leaf1-soundness.md` (this); `codex/leaf1-{prompt,answer}.md`;
`scripts/leaf1_threshold{,2}.py`; `brickD-pin.md`, `brickD-sublemmas.md`, `satred-cert.md` (A>2Δ regime).
