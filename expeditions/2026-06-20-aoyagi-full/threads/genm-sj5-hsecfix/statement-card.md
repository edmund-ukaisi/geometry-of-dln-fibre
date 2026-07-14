# Statement card — `genm-sj5-hsecfix` (j=0 SECTOR borderline over the `U_s` `m`-frame)

**Module:** `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJSectorBorderline.lean`
**Branch:** `genm-sj5-hsecfix` (base `origin/genm-sj5-good`).
**Status:** `sorry-free`; all results axiom-clean `[propext, Classical.choice, Quot.sound]` (forced
`#print axioms`, olean deleted before re-elaboration). Green under `scripts/lb`.

Discharges the CORRECTED j=0 sector route for hole (d) (`dcoverhunt` verdict: the sector keys off the
effective deep rank `ρ_Z = tailMinWidth = min(M₁,…,M_last)`, NOT `M₂`). Delivers the reusable analytic
core + the two structural facts; the mechanical composition into `hsector` (via the still-open
cross-lane Bricks F/D of `RouteMSJDeeperFlagCore`) is controller rendezvous wiring.

## Delivered theorems (one line each)

- `shell_corankOffSector_borderline_le_unif` — SECTOR BORDERLINE bound, `m`-frame keyed: on the shell
  `Z Zᵀ ⪰ ε²·(U_s U_sᵀ)` (`U_sᵀU_s=1`, `b≤m≤M₂`, `m≤Z.rank`), `θ∈[0,1)`,
  `∫_{A_cor}∫_Γ (w + frobSq(Ccross + Γ·(A_cor·Z)))^{−c'} ≤ deeperFlagBorderlineConst … (vol sΓ)·w^{−(c'−θab/2)}`.
  The constant is an EXPLICIT `Z`/`w`/`Ccross`-free term (mirroring `deeperFlagUnifConst`), so it factors
  out of a pointwise-in-`(z,v)` application — the reshape after reviewer Finding 1 (the earlier `∃ C₁`
  form did not deliver the uniformity its name asserts). The borderline analogue of the banked
  `shell_corankOffSector_le_unif`; closed by `enn_geom_interp` + `borderline_real_identity`.
- `deeperFlagBorderlineConst` (+ `_lt_top`) — the `Z`/`w`-free per-shell borderline constant, finite iff
  `θ·a < m−b+1` (⟺ `θ<1` at the border), via the `m`-frame `shellCorankWeight_real_le_unif` +
  `strongBlock_unif_const_lt_top` (NOT the `M₂`-keyed `corankWeight_bpos_lt_top`).
- `uniformWenn_proj_real_le` — real-exponent (`s≥0`) analogue of `uniformWenn_proj_le`: shell-floor
  projection `Z→U_s`, factor `ε^{−sb}`.
- `shellCorankWeight_real_le_unif` — `Z`-uniform bound on the θ-scaled corank weight
  `∫ det((A·Z)(A·Z)ᵀ)^{−s/2} ≤ ε^{−sb}·(fixed-box weight)`, via the `m`-frame.
- `tailMinWidth_le_min_head_last` — structural fact (1) automatic leg: `tailMinWidth M ≤ min(M₁,M_last)`,
  UNCONDITIONAL.
- `min_head_last_eq_tailMinWidth_of_nonempty` — structural fact (1): at a nonempty sector
  (`min(M₁,M_last) ≤ tailMinWidth M`) `min(M₁,M_last) = tailMinWidth M`.
- `minAdm_cons_succ_le_of_le` — the conditional increment helper (induction on tail arity):
  `1≤u → minAdm(cons u tail) ≤ u·w → minAdm(cons (u+1) tail) ≤ minAdm(cons u tail) + w`. The sharp
  `tailMinWidth`-keyed key (uses only the single budget hypothesis at `u`).
- `bindingCut_corank_add_le_tailMinWidth_succ` — structural fact (2): at a nondegenerate binding cut `t`
  (`1≤t`, `t+1≤min(M₀,M₁)`, `hbind`, `hpiv : minAdm(redChain t M) ≤ t·tailMinWidth M`),
  `(M₀−t)+(M₁−t) ≤ tailMinWidth M + 1`. (LOWER convexity `minAdm_redChain_succ_ge` ∧ UPPER increment.)
- `bindingCut_corank_add_le_tailMinWidth_succ'` — the `t = bindingCut M` specialisation (binding identity
  read off `Nat.find_spec`).
- `minAdm_two`, `minAdm_cons_singleton`, `redChain_cons_tail` — supporting `minAdm`/`Fin.cons` lemmas.

## Fidelity notes / hypotheses (caveats next to claims)

- **Fact (2) genuinely needs `hpiv` AND the binding cut** (numeric sweep, arity 3–6 widths 1–7): for a
  GENERAL `t` (non-binding) satisfying `hpiv` + genuineness the bound FAILS (202004 fails); at the binding
  cut with `hpiv` it holds (0 fails). Without `hpiv` it also fails even at the binding cut (1501 fails,
  e.g. `(4,2,3)`). The unconditional `a★+b★ ≤ deepRank+1` (deepRank `= min(M₂,…,M_last)`) is provable but
  is LOOSER than `tailMinWidth+1` in waist cases; `hpiv` is what sharpens it. Codex (xhigh, decorrelated)
  designed and independently verified the increment-helper proof.
- **Fact (1) equality's `hne` leg is the shell-0 GEOMETRIC nonemptiness** (`min(M₁,M_last) ≤ tailMinWidth`),
  supplied at wiring by the frame/emptiness routing — correcting the covervalid `m ≤ M₂` filter to the
  sharp `m ≤ tailMinWidth`. The automatic leg (`tailMinWidth ≤ min(M₁,M_last)`) is unconditional.
- **Anti-regression:** every proof is keyed to `ρ_Z = tailMinWidth`/the `U_s` `m`-frame; `M₂`-as-rank and
  the `M₂`-keyed lemmas (`uniformWenn_le`, `corankOffSector_borderline_le`, `corankWeight_bpos_lt_top`)
  appear ONLY in docstrings (explaining their inapplicability), never in a proof term.

## Wiring owed (controller rendezvous)
The full `hsector` (`shellSpineIntegrand … < ⊤`) composes this borderline bound with `headSplit_domination`
(Brick D) + `exists_headSplitFrame` (Brick F) — both still open `(□)` in `RouteMSJDeeperFlagCore`, owned by
the finfin lane — plus the emptiness routing for shells with `min(M₁,M_last) > tailMinWidth`.
