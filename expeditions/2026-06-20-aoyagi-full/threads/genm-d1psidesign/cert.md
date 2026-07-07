# Design certificate — the general-`L` joint move `psiSplitRawGen` (#120 `hstep2`, LINK-1 crux)

**Seat:** pen-and-paper (witness). **Question:** pin the concrete general-`L` joint move
`psiSplitRawGen` and adjudicate its two load-bearing invariants — the germ-satisfiability of
`deepestEFull` invariance (Invariant A) and the core→`Score` untwist (Invariant B) — BEFORE a
formaliser sinks a multi-tide build on a possibly-unsatisfiable definition.

## HEADLINE — Invariant A is SATISFIABLE. The move EXISTS, exactly, and does NOT re-open #120.

There is an explicit, origin-fixing joint move with `D(psiSplitRawGen − id)(0) = 0` that keeps
`deepestEFull` invariant while the per-layer cores realise the untwist to `Score`. It is **not** a
pure up-block (Y-tag) move — the L=2 template does not generalise verbatim — but the extra ingredient
is a **single down-block edit `Z₀`**, not a research wall. Verified EXACTLY (exact rational, finite
data near the origin) for `L ∈ {3,4,5}`, core width `m ∈ {1,2,3}`, pivot `r ∈ {1,2}`, two seeds each.

Concretely the move keeps every pivot `A_s` FIXED, edits the up-blocks `Y_s` at all layers, edits
ONE down-block `Z₀`, and reconstructs the cores to hold the target per-layer Schur core `(1−K_s)S_s`.

## The objects (faithful abstraction of the Lean setup)

In the `r ⊕ m` block frame (interior frames `Pf=Qf=I`; `J = frontEmbed` ⟹ the last-layer column split
IS the threshold split, so all layers are uniform shape), layer `s` of `framedParamsPivot q` is

    C_s = [[ A_s , Y_s ],       A_s = I_r + X_s   (X_s = gaugeReadX_s, pivot read),
           [ Z_s , T_s ]]       Y_s = gaugeReadY_s (up),  Z_s = gaugeReadZ_s (down),
                                T_s = core-slot block (paramsEquivFlat deepestM).

`P = C_0·C_1·…·C_{L−1} = prod(framedParamsPivot q)` reindexed; write `P = [[P11,P12],[P21,P22]]`.

* `deepestEFull q = (P11 − I_r, P12, P21)` — the reg residual the loss squares (`∑ deepestEFull²`).
* `deepestCoreF (deepestCoreAbsorbConj q).2.1 = ‖∏_s S_s‖²` — the conj-absorb reads the FROBENIUS of the
  **plain product of the per-layer Schur cores** `S_s = T_s − Z_s A_s⁻¹ Y_s` (verified via
  `deepestCoreF_coreAbsorbConj_eq_prodSchur`: absorbed core `= decode.core_s + schurCorrectionConj_s =
  T_s − Z_s A_s⁻¹ Y_s`).

Partial products `Q_s = C_0…C_{s−1} = [[B_s,R_s],[D_s,H_s]]` (`Q_0 = I`). Normalised data:
`u_s = B_s⁻¹R_s` (r×m), `V_s = Z_s A_s⁻¹` (m×r), `W_s = H_s − D_s B_s⁻¹R_s` (m×m Schur of the partial
product), `N_s = I_r + u_s V_s` (r×r). The couplings and target:

    K_s = Z_s (Q_{s+1})₁₁⁻¹ (Q_s)₁₂       (K_0 = 0)        [= V_s N_s⁻¹ u_s, VERIFIED]
    M_s = I_m − K_s                                          [M_0 = I]
    S̃_s = M_s S_s = (1−K_s) S_s     (target per-layer Schur core; S̃_0 = S_0)
    coreProd = S_0 (1−K_1) S_1 … (1−K_{L−1}) S_{L−1} = blockSchur(P)   [Schur recursion, F2]

`Score(x) = ‖blockSchur(framed residual)‖² = ‖coreProd‖²`.

## 1. The concrete `psiSplitRawGen` (formaliser-ready coordinate map)

The move keeps the pivots fixed and edits `(Y_s, Z_0, T_s)`:

    (pivot)   A'_s = A_s                    — gaugeReadX UNCHANGED, all s
    (up)      Y'_s = Y_s + N_s⁻¹ u_s (S_s − S̃_s)          for all s = 0..L−1
    (down)    Z'_0 = (V_0 + ΔV_0) A_0 ,   Z'_s = Z_s (s ≥ 1)
    (core)    T'_s = S̃_s + Z'_s A_s⁻¹ Y'_s                for all s

where `ΔV_0 = a_L − ã_L` is the mismatch of two left-column accumulators over the chain:

    a_0 = 0,   a_{s+1} = a_s + W_s V_s N_s⁻¹ B_s⁻¹                    (original chain)
    ã_0 = 0,   ã_{s+1} = ã_s + Ŵ_s V_s N_s⁻¹ B_s⁻¹ ,   Ŵ_0 = I,  Ŵ_{s+1} = Ŵ_s · M_s · S̃_s   (edited)

(all inverses — `A_s`, `B_s`, `N_s` — are units in a neighbourhood of the deepest point: at the origin
`A_s = I`, `B_s = I`, `N_s = I`, so the map is a genuine analytic germ.)

**Why it is built this way (the mechanism):**
* The up-edit `Y'_s` is exactly the amount that keeps the partial-product pivot `B_s` and the normalised
  up `u_s` UNCHANGED for every `s` — hence `P11` and `P12` (the whole top block-row) are preserved
  automatically. This is the clean generalisation of the L=2 `Y`-tag correction.
* Editing the interior cores changes the **normalised left column `P21·P11⁻¹`** through the later down
  blocks (`W_s V_s …` couplings). This is invisible at L=2 (`P21` there is `Z_0 A_1 + T_0 Z_1`, free of
  the last-layer edit) but real at `L ≥ 3`. The single down-edit `Z'_0` cancels the accumulated
  mismatch `ΔV_0`, restoring `P21`. `Z_0` suffices because `V~_0` sits leftmost, so its shift feeds the
  whole left-column accumulator.
* Any `(A'_s, Z'_s, w'_s)` reconstruction with `T'_s = S̃_s + Z'_s A_s⁻¹ Y'_s` gives the moved layer
  Schur core `= S̃_s` regardless — so Invariant B is automatic for this move family.

## 2. INVARIANT A verdict — SATISFIABLE (exact)

`deepestEFull(psiSplitRawGen q) = deepestEFull(q)` — i.e. `(P'11, P'12, P'21) = (P11, P12, P21)`.
Verified EXACTLY (exact-rational finite data near the origin), for the FULL move above:

| L | r | m | seeds | M_s = I−K_s | up-only fixes (P11,P12,P21) | up+Z₀ fixes (P11,P12,P21) & Inv B |
|---|---|---|-------|-------------|-----------------------------|------------------------------------|
| 3 | 1 | 1 | 5,11  | ✓ | (✓,✓,✗) | (✓,✓,✓) & ✓ |
| 3 | 1 | 2 | 5,11  | ✓ | (✓,✓,✗) | (✓,✓,✓) & ✓ |
| 4 | 1 | 1 | 5,11  | ✓ | (✓,✓,✗) | (✓,✓,✓) & ✓ |
| 4 | 1 | 2 | 5,11  | ✓ | (✓,✓,✗) | (✓,✓,✓) & ✓ |
| 5 | 1 | 1 | 5,11  | ✓ | (✓,✓,✗) | (✓,✓,✓) & ✓ |
| 3 | 1 | 3 | 5,11  | ✓ | (✓,✓,✗) | (✓,✓,✓) & ✓ |
| 3 | 2 | 2 | 5,11  | ✓ | (✓,✓,✗) | (✓,✓,✓) & ✓ |
| 5 | 1 | 2 | 5,11  | ✓ | (✓,✓,✗) | (✓,✓,✓) & ✓ |

`sympy/codex_construction.py` (exact rationals; block-`.inv()`, `simplify == 0`).

**SCOPE (load-bearing for the formaliser):** the L=2 "edit last-layer `Y`-tag only" move does **not**
generalise. Up-block edits alone preserve `(P11,P12)` but leave `P21` broken at `L ≥ 3` (for every
`m`, including scalar). The general move needs the extra down-block edit `Z₀`. It does **not** need
pivot (`X`) edits.

## 3. INVARIANT B verdict — HOLDS

`blockSchur(P) = coreProd` (the F2 Schur recursion) AND `∏_s (per-layer factor) = coreProd = Score`,
so the moved point's conj-absorb reads `Score`. Verified exactly (`sympy/verify_B_deriv.py`,
`sympy/model.py`):

* `blockSchur(P) == coreProd`: ✓ at `L = 2,3,4`, `m = 1,2`.
* plain product of `(S_0, (1−K_1)S_1, …)` `== coreProd == Score`: ✓ at `L = 3,4`, `m = 1,2`.
* For the moved point (Codex construction) the plain product of the NEW per-layer Schur cores equals
  `blockSchur(P) = coreProd`: ✓ (the `InvB` column above).
* `M_s = I − K_s` reconciles the normalised (`V_s N_s⁻¹ u_s`) and the `Kcoup` (`Z_s (Q_{s+1})₁₁⁻¹
  (Q_s)₁₂`) forms: ✓.

## 4. `D(psiSplitRawGen − id)(0) = 0`  (the banked `DeepestPsiFlatCutGen` triple fires)

Under the origin germ (data `= ε · generic`), `sympy/deriv_orders.py`:

    core untwist  S̃_s − S_s = O(ε³)   (K_s = O(ε²), S_s = O(ε))
    up edit       Y'_s − Y_s = O(ε⁴)
    down edit     Z'_0 − Z_0 = O(ε⁵)   (= 0 for L = 2)
    ⟹ psiSplitRawGen − id = O(ε³)   ⟹  D(psiSplitRawGen − id)(0) = 0   (Hessian vanishes too).

The move fixes the origin (`psiSplitRawGen 0 = 0`: at `q = 0` all reads and cores vanish, `S_s = 0`,
so every edit is `0`).

## 5. Decorrelated Codex (xhigh) — AGREEMENT, and it CORRECTED my methodological error

Consult: `codex/psidesign-prompt.md` / `codex/psidesign-answer.md` (setup + question given; my empirical
findings and my tentative verdict WITHHELD).

* **Agreement on the verdict:** Codex independently reached "correction EXISTS (germ), high
  confidence — no obstruction," matching my exact result. No divergence on satisfiability.
* **Codex supplied the clean explicit construction** (pivots fixed; up-blocks + `Z₀`), which I then
  implemented and verified EXACTLY (§2). Its block-LDU derivation of *why* `Z₀` suffices (the
  normalised left column `P21 P11⁻¹` shifts through later down blocks) is corroborated by the up-only
  data (`P21` is precisely the block that up-edits miss).
* **DIVERGENCE — and Codex was right:** my own first-pass order-by-order germ solver
  (`germ_fast.py`, greedy "set free coefficients to 0" per order) reported `OBSTRUCTED` for the
  up-only, up+down (`wZ`), and up+pivot families at `m ≥ 2`, which had led me toward a WRONG
  "full reg gauge (incl. pivot) required" reading. Those were **false obstructions** — artefacts of
  the greedy choice on *under-determined* families (a locally-consistent low-order pick paints the
  higher orders into a corner). Codex's construction is an explicit point inside the up+down family,
  and it verifies exactly — so that family IS solvable; the greedy solver's "obstructed" was spurious.
  **Correction registered:** pivot edits are NOT needed; the determined tests (up-only scalar `L=3`
  solvable) and the exact finite-data verification of the Codex construction are the trustworthy ones,
  not the greedy under-determined germ runs.

Lesson for future exact-algebra germ tests: a greedy order-by-order solve is only a valid
satisfiability test on DETERMINED systems; on under-determined ones it can report false obstructions —
verify with an explicit candidate or a non-greedy (carry-the-freedom) solve.

## 6. Formaliser-facing build order

Everything below LINK-1 (`deepest_diffeo_bridge_gen_conj_impl`, `deepest_diffeo_bridge_gen_assembled`),
Step Θ (`link2_at_wstar_gaugeReg_gen`), the corner facts (`deepBlk_boundary_gen`,
`deepBlkA_isUnit_gen`), the analytic cutoff plumbing (`DeepestPsiFlatCutGen`), and the Schur recursion
(`schur_product_ldu_rec`, `coreProd`, `Kcoup`, `Kcoup_zero`) are already banked. What `psiSplitRawGen`
adds, in dependency order:

1. **`def` the normalised partial data** `u_s, V_s, N_s, W_s, B_s` off `partProd`/`framedParamsPivot`
   (all units near the deepest point — carry `Invertible` witnesses `B_s(0)=I`, `N_s(0)=I`).
2. **`def` the per-layer targets** `S̃_s = (I − Kcoup C s)·S_s` (reuse `Kcoup`; `M_0 = I` via
   `Kcoup_zero`). Feeds **item 2 `hsub4core`**: `∏ S̃_s = coreProd` is `schur_product_ldu_rec`
   read on the moved cores — the plain product of the moved per-layer Schur cores equals `coreProd`,
   hence conj-absorb reads `Score`.
3. **`def` the up-edit** `Y'_s = Y_s + N_s⁻¹ u_s (S_s − S̃_s)` and prove the **top-row lemma**:
   it leaves `B_s` and `u_s` (hence `P11`, `P12`) unchanged for every `s`. (This is the clean half of
   **item 3 `hsub3reg`**.)
4. **`def` the accumulators** `a_s, ã_s, Ŵ_s` and the down-edit `Z'_0 = (V_0 + (a_L − ã_L))·A_0`;
   prove the **left-column lemma**: it restores `P21`. Together with step 3, this is the full
   **item 3 `hsub3reg`** (`deepestEFull(psi q) = deepestEFull q`, hence the `∑ ²` germ).
5. **`def` `psiSplitRawGen`** assembling the reg-slot edit (write `gaugeReadY` at all layers +
   `gaugeReadZ_0`; leave `gaugeReadX`) and the core-slot edit (`T'_s = S̃_s + Z'_s A_s⁻¹ Y'_s` via
   `paramsEquivFlat`). Then `psiSplitRawGen 0 = 0` (origin) and `D(psiSplitRawGen − id)(0) = 0`
   (all edits `O(‖q‖³)`) discharge the `DeepestPsiFlatCutGen` hypotheses.
6. Feed items 2/3 into `deepest_diffeo_bridge_gen_assembled` (`hsub4core`/`hsub3reg`), closing
   `hstep2` at `L ≥ 3`.

**Firmest result:** the move exists exactly and both invariants hold (verified `L ≤ 5`, `m ≤ 3`,
`r ≤ 2`), with `D(psi−id)(0)=0`; #120 is not re-opened.
**Most likely thing to break it (for the formaliser, not the math):** the down-edit `Z'_0` accumulator
`Ŵ_{s+1} = Ŵ_s M_s S̃_s` and the left-column lemma — the one genuinely new, `L`-recursive identity
beyond the L=2 template (the top-row/up-edit half mirrors L=2). Rectangular cores and the
`partProd`/dependent-width cast bookkeeping (per `lean/CLAUDE.md`) are the labour, not a wall.
**Next construction/consult that would settle the open part:** a Lean-level proof that the up-edit
fixes `(B_s, u_s)` for all `s` (the top-row lemma) — a clean induction on `partProd`; once it and the
left-column lemma land, `hsub3reg` is mechanical.

## Files (exact-algebra artefacts, all exact-rational / symbolic; no floats load-bearing)

* `sympy/model.py` — Invariant B (Schur recursion) + core-only-move breaks `deepestEFull`.
* `sympy/solvability.py` — exact-rational + Jacobian tests (initial, up-only-focused).
* `sympy/germ_fast.py` — order-by-order germ solver (⚠ greedy: reliable on DETERMINED systems only;
  its under-determined "obstructed" verdicts were false — see §5).
* `sympy/verify_B_deriv.py` — Invariant B at non-scalar `m=2` + correction-start order.
* `sympy/codex_construction.py` — **the decisive test**: implements the explicit construction and
  verifies (A)+(B) EXACTLY across `L,m,r,seed`.
* `sympy/deriv_orders.py` — edit orders ⟹ `D(psi−id)(0)=0`.
* `codex/psidesign-prompt.md`, `codex/psidesign-answer.md` — the decorrelated consult.
