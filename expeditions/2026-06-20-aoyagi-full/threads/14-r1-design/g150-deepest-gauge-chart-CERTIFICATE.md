# DeepestGaugeChart — exact-algebra certificate for #44 sub-lemmas 3+4 (pp-hall, 2026-06-22, #150)

**The pen-and-paper cert gating #44's two heavy sub-lemmas** (`deepest_gauge_chart_exists` +
`deepest_loss_in_gauge_coords`), the #131/g131 pattern applied to the L2/D1 deepest-point normal form.
Produces the explicit `DeepestGaugeChart` construction on a rank-r-exact node + the det-unit/non-MP
Jacobian fact + the loss-form germ + `chart_zero`. crux2 transcribes into the #44 sub-lemmas 3/4. NB the
**NON-MP** transport (`rlctAtOn_unit_invariant_aux` + germ-locality, NOT `comp_homeomorph`).

## Setup (rank-r-exact deepest point, the `IsDeepLayers` scope-cut)
At a deepest point `w0` with `IsDeepLayers H r B w0` (`w0 ∈ optimalSet H B ∧ ∀ s, (w0 s).rank = r` —
every layer rank EXACTLY `r`), gauge-slice each layer `C_s : H_s × H_{s+1}`. By `block_elimination` there
are units `P_s, Q_s` with `P_s (w0 s) Q_s = blockdiag[I_r, 0]`. In the gauge coords (the local deviation
from `w0`), each layer is

    C_s = [[ I_r + X_s , Y_s ], [ Z_s , T_s ]]
          (X_s: r×r, Y_s: r×(H_{s+1}−r), Z_s: (H_s−r)×r, T_s: (H_s−r)×(H_{s+1}−r) = the REDUCED block).

The **reduced widths** `M_s = H_s − r`; the **reduced core** is `‖∏ T_s‖² = dlnLoss M 0`.

## The construction (sub-lemma 3, `deepest_gauge_chart_exists`)
**The 2-factor block-product (folded over `L`).** For two rank-r layers (`g150_gauge_chart.py`),
`C_1·C_2` has blocks:
- `(0,0) = (I_r+X_1)(I_r+X_2) + Y_1 Z_2 = I_r + (regular)` — regular;
- `(0,1) = (I_r+X_1)Y_2 + Y_1 T_2` — regular;
- `(1,0) = Z_1(I_r+X_2) + T_1 Z_2` — regular;
- `(1,1) = Z_1 Y_2 + T_1 T_2` — the **reduced block**. NB on `{E=0}` (solving `B,U,Z`) this is
  `T_1 (I−V Y)^{-1} T_2` (an internal gauge unit `(I−VY)^{-1}`), NOT raw `T_1 T_2` — see the CORRECTED
  loss-form below; the reduced core is the gauge-normalized `T̃_1···T̃_L`.

**The regular coordinates** are the **product regular-residual blocks**
`E := (∏C − blockdiag[I_r,0])` restricted to the `(0,0),(0,1),(1,0)` positions; the **reduced
coordinates** are the `T_s` blocks. Verified (`g150_jac_fix.py`): the regular residuals `(E00,E01,E10)`
have **Jacobian rank `= 3`** over the gauge regular coords at `w0` (linear parts `E00 ↔ {X_1,X_2}`,
`E01 ↔ Y_2`, `E10 ↔ Z_1`), so they are independent regular directions; completing them with a transversal
(e.g. `X_1, Y_2, Z_1`) gives a **det-unit coordinate change**, KEEPING the `T_s` as reduced.

**`nReg = r(H_0 + H_last − r)`** (the rank-r gauge-orbit slice dimension — the regular residuals live at
the two chain ENDPOINTS, the interior rank-r spine absorbed). Verified to match the interface for
`(2,2,2)r1→3`, `(3,3,3)r2→8`, `(4,3,2)r2→10`, `(2,2,2)r2→4`, `(3,2,1)r1→4` (`g150_general_r.py`).

## The loss-form germ (sub-lemma 4, `deepest_loss_in_gauge_coords`) — CORRECTED (Codex #150)
Near `w0` (all regular coords `→ 0`):

    dlnLoss H B ∘ chart  =ᶠ[𝓝 0]  (∑ᵢ E_i²)  +  ‖T̃_1 ··· T̃_L‖²,    ‖T̃_1···T̃_L‖² = dlnLoss M 0 (gauge-normalized).

The split is **EXACT** (a germ equality via the c-o-v, NOT a squeeze) — BUT the reduced core's blocks are
the **GAUGE-NORMALIZED** `T̃_s`, NOT the raw `T_s`. **(Decorrelated Codex caught a real error in my first
draft: the raw-`T` split is FALSE.)** Solving the chart coords `(E00,E01,E10,T,S,A,Y,V)` for `(B,U,Z)` on
the product-regular zero locus `{E=0}` gives (verified exact, `g151_codex_check.py`):

    P_{11} | {E=0}  =  T (I − V Y)^{-1} S   ≠   T S   (the cross `ZU` does NOT vanish — it becomes an
                                                       invertible INTERNAL gauge factor `(I−VY)^{-1}`).

So the literal "cross absorbed ⟹ reduced block `= T_1 T_2`" is **wrong** (my g150_loss_form over-restricted
by zeroing the gauge coords X,Y,Z, masking `VY`). The CORRECT reduced core is `‖T̃_1···T̃_L‖²` where
`T̃_s` = the raw `T_s` with the internal gauge units `(I − V_s Y_s)^{-1}` (a UNIT at `w0`, `=I` when
`V=Y=0`) absorbed — equivalently the **product Schur complement** `R = P_{11} − E_{10}(I+E_{00})^{-1}E_{01}`
factored as `R = T̃_1···T̃_L` after the det-unit Schur/Gaussian coordinate change. The endpoint-regular
leak `E_{10}(I+E_{00})^{-1}E_{01}` is endpoint-regular×endpoint-regular, absorbed into `∑E²`. Then a
parameterized analytic Morse/splitting lemma gives the exact germ `ℓ∘Φ = ∑E² + ‖T̃_1···T̃_L‖²`. This is
the #131 pattern (residual = smaller matrix-chain core) — but the reduced chain is in the GAUGE-NORMALIZED
blocks (internal units absorbed), `dlnLoss M 0` in those coords, NOT the literal raw `T_s`. (Verified
`g151_gauge_normalized.py`: `g = (I−VY)^{-1}` is a unit at `w0`; the reduced core `T·g·S` is an honest
2-factor reduced chain with the middle unit absorbed.)

## The det-unit / NON-MP Jacobian (the KEY — sub-lemma 5 input)
The chart's Jacobian determinant is a **bounded UNIT** near `w0` (`jac_unit`: `∃ U ∈ 𝓝 0, ∃ a b, 0 < a ∧
∀ x ∈ U, a ≤ |det Dchart| ≤ b`), but is **NOT identically 1** — the regular-residual c-o-v
(`E = product residuals`, which mixes the gauge blocks nonlinearly) has a Jacobian that is the rank-3
unit block × the spectator identity, a unit `≠ 1`. So the RLCT transport is **NON-MP**:
`rlctAtOn_unit_invariant_aux` (peel the bounded-unit `|det Dchart|` weight) + `rlctAtOn_germ_local`
(the germ equality) — **NOT `rlctAtOn_comp_homeomorph`** (which requires MP, `det = 1`). This is the
exact distinction the dispatch flagged: the deepest-gauge chart is a genuine c-o-v with a nontrivial
(but unit) Jacobian, transported by the unit-invariance + germ-locality lemmas, not the MP-homeomorph one.
**Explicit (Codex #150):** the inverse-coordinate Jacobian determinant is `det(A)^{-(r+M_2)}·det(B)^{-M_0}`
(up to sign), where `A = (∏C)`'s leading `r×r` block ≈ `I_r` near `w0` — so it is bounded away from `0`
and `∞`, plainly NOT identically `1`. The `weightedThreshold_transport` use-site (S1.1) carries the
`|det Dπ|` weight; the bounded-unit peel then strips it (the weight is a unit near `w0`).

## `chart_zero` (the basepoint pin)
`chart 0` is the gauge origin (all deviation blocks `= 0`), which by `block_elimination`'s `P_s,Q_s`
units maps back to `w0 = deepestPoint H r B`: `(paramsEquivFlat H).symm (chart 0) = deepestPoint H r B`.
So the chart fixes the deepest point — the transport's basepoint is `w0` (the singular zero of the loss),
exactly where the RLCT is computed (the #130 `χ 0 = 0` discipline, here `chart_zero`).

## The `r = 0` base (clean)
`r = 0`: `hB : B.rank = 0 ⟹ B = 0`; `IsDeepLayers` forces all layers rank 0 ⟹ `deepestPoint = 0`;
`M = H − 0 = H`, `nReg = 0·(H_0+H_last) = 0`. The gauge chart is the **IDENTITY** (no regular block, no
gauge to fix), and `dlnLoss H 0 ∘ id = dlnLoss M 0` directly. So sub-lemma 1 (`deepest_regular_core_r0`):
`rlctAt (dlnLoss H 0) 0 = rlctAtOn (dlnLoss M 0) 0` by `rlctAtOn_eq_rlctAt`. No chart needed
(`g150_general_r.py`).

## The scope-cut (Codex, adopted)
Prove the chart for **arbitrary `w0` with `IsDeepLayers H r B w0`**, then apply `deepestPoint_isDeep` to
specialise to `deepestPoint`. The algebra reduces to a **2-factor block-multiplication lemma folded over
`L`** (the per-layer-pair block product above; the regular residuals accumulate at the chain endpoints,
the reduced core is the `∏ T_s` chain). This avoids the full `L`-fold expansion — each fold step is the
2-factor block product, the interior rank-r spine contracting to the next reduced factor.

## What crux2 transcribes (the #44 sub-lemma map)
- **sub-lemma 3 `deepest_gauge_chart_exists`:** the `DeepestGaugeChart` structure with `chart` = the
  gauge-slice + regular-residual c-o-v (block_elimination units per layer, det-unit completion), `split`
  = `(E_reg, T-reduced, spectators)`, `nReg = r(H_0+H_last−r)`, `nGauge` = the spectator count,
  `chart_zero` (gauge origin ↦ `w0`), `hasDeriv` + `jac_unit` (the bounded-unit Jacobian), `loss_form`
  (the germ split below).
- **sub-lemma 4 `deepest_loss_in_gauge_coords`:** the germ `dlnLoss H B ∘ chart =ᶠ ∑E² + dlnLoss M 0`,
  via the 2-factor block product (regular residuals + the reduced `∏T` core, cross terms ∈ ideal(reg)
  absorbed into `E`). Uses `dlnLoss_nonneg` for the `Real.sqrt (dlnLoss M 0)` wrapper (`G := √∘dlnLoss M 0`,
  `G² = dlnLoss M 0`).
- feeds **sub-lemma 5** (`deepest_nonMP_chart_transport_unit`): `jac_unit` + `weightedThreshold_transport`
  + bounded-unit peel (NON-MP, NOT `comp_homeomorph`).

## Most likely thing to break this
The det-unit completion: the regular residuals `(E00,E01,E10)` are independent (Jacobian rank
`= nReg`), but completing them to a FULL det-unit coordinate change needs the spectator directions
(`nGauge` coords — the gauge redundancy `block_elimination`'s `P_s,Q_s` removes) to be chosen so the
total Jacobian is a unit. The gauge-fixing (`P_s,Q_s` units, `det ≠ 0`) supplies this — the gauge slice
is a transversal to the `GL_r × GL_r` gauge orbit, so the spectator block is the orbit-tangent
complement, det a unit. The one Lean-side check: the per-layer gauge units `P_s, Q_s` (from
`block_elimination`, `IsUnit`) compose into a det-unit chart Jacobian — `block_elimination` gives `IsUnit
P_s`/`IsUnit Q_s` (det `≠ 0`), and the product of units is a unit; the regular-residual c-o-v on top is
the rank-`nReg` unit block. So `jac_unit` holds, but the explicit `a, b` bounds need the compactness of a
small nbhd of `w0` (standard). [Decorrelated Codex check FOLDED (#150): it CAUGHT the raw-`T` split error (`P_{11}|{E=0} = T(I−VY)^{-1}S
≠ TS`); the corrected reduced core is the gauge-normalized `T̃` / product Schur complement (above). The
exact germ + det-unit + nReg all survive the correction. Decorrelated + pp-hall exact — converged.]

## Provenance
The #44 normal-form (`g147-normalform-skeleton-answer.md`, sub-lemmas 3+4), the #131/g131 pattern
(residual = smaller matrix-chain core), `block_elimination` (`Skeleton.lean:279`, the rank-r normal form),
`IsDeepLayers`/`deepestPoint` (`Skeleton.lean:502/932`). Exact algebra: `g150_gauge_chart.py` (the gauge
slice + block product), `g150_loss_form.py` (the loss-form germ + cross-term ∈ ideal(reg)), `g150_jac_fix.py`
(the det-unit Jacobian rank `= nReg`), `g150_general_r.py` (general-r + the `nReg` formula + the `r=0`
base) — all in `g129-scripts/`. NON-MP transport (`rlctAtOn_unit_invariant_aux` + germ-locality), the key
distinction from the MP/blow-up work. **Codex #150 correction folded:** the raw-`T` loss split is FALSE
(`P_{11}|{E=0} = T(I−VY)^{-1}S ≠ TS`); the reduced core is the gauge-normalized `T̃` / product Schur
complement (`g151_codex_check.py`, `g151_gauge_normalized.py`). Decorrelated Codex (gpt-5.5 xhigh) +
pp-hall exact-algebra — converged after the correction.

---

## CORRECTION (#61, pp-hall, 2026-06-22) — the per-layer core is the SCHUR complement `S_s`, NOT the unit `T̃_s`

**cobuild-sub34's g153/g156 litmus caught a real mis-specification in the per-layer gloss above.** The
FULL product Schur `R = P11 − E10(I+E00)⁻¹E01` framing was right; the per-layer factorization
`R = T̃_1···T̃_L` with `T̃_s = T_s·(I−V_sY_s)⁻¹` (the UNIT form) is **WRONG**. The correct per-layer
object is the **per-layer Schur complement**

    S_s  =  T_s − Z_s (I + X_s)⁻¹ Y_s            (X_s = (0,0)-deviation, Y_s=(0,1), Z_s=(1,0), T_s=(1,1)).

**Ground truth (the g153 counterexample, parametrization-free, `g172_perlayer_schur_groundtruth.py`).**
L=3, r=1, H=(2,2,2,2): `C1=[[1,0],[−ε²,ε]]`, `C2=[[1,ε],[ε,0]]`, `C3=[[1,−ε²],[0,ε]]` ⟹ `∏C =
blockdiag[1,−ε⁴]`, `loss = ε⁸`.
- **per-layer UNIT / raw `∏T_s`:** `T=(ε,0,ε)` ⟹ `∏T_s = 0` ⟹ core = 0 ≠ ε⁸. **WRONG** (`T2=0` kills it).
- **per-layer SCHUR `S_s`:** `S1=ε`, `S2 = 0 − ε·ε/1 = −ε²`, `S3=ε` ⟹ `∏S_s = −ε⁴` ⟹ `‖∏S_s‖² = ε⁸ =
  loss`. **RIGHT.** The decisive entry is `S2`: raw `T2 = 0`, but the Schur correction `−Z2Y2 = −ε²`
  carries the whole loss.
- **full product Schur `R`:** `R = −ε⁴` ⟹ `‖R‖² = ε⁸ = loss` (right here, where reg=0).

**Why my g151 read "unit".** `g151_codex_check.py` solved `P11|{E=0} = T(1−VY)⁻¹S` for an L=2 slice and I
mislabeled that as "the gauge-normalized core". On cobuild-sub34's generic L=3 slice
(`g171/g172`), `P11|{E=0} = t1·(t2 − zy)·t3 = S1·S2·S3` — the per-layer **Schur** product, not the
per-layer unit product. The `(I−VY)⁻¹` was an artifact of the particular L=2 elimination order, not the
honest reduced core.

**The corrected deepestCoreF.** `deepestCoreF(core) = ‖S_1 ··· S_L‖² = dlnLoss (H−r) 0` on the
**Schur-reduced** layer factors `S_s = T_s − Z_s(I+X_s)⁻¹Y_s` (internal units absorbed by the det-unit /
analytic core change). Everything else in this cert survives: the EXACT germ split `ℓ∘Φ =ᶠ ∑E² +
‖∏S_s‖²`, `nReg = r(H_0+H_last−r)`, the bounded-unit (NON-MP) Jacobian, `chart_zero`, the `r=0` base.
Only the per-layer block's NAME changes: `T̃_s = T_s(I−V_sY_s)⁻¹` (unit, wrong) → `S_s = T_s −
Z_s(I+X_s)⁻¹Y_s` (per-layer Schur, right). Aligns with cobuild-sub34's #54 `R` + crux2's coreAbsorb (both
corrected to `S_s`).

**The downstream subtlety cobuild-sub34/Codex flagged (preserved):** the full product Schur `R` depends on
the regular residuals `P10,P01` OFF `{reg=0}`; the additive split `rlct_additive_smooth_block` needs a
core-coords-only object. The route (g156): `R = G(core) + Σ E_i H_i` with bounded analytic `H_i`, so
`∑E² + ‖R‖² ≍ ∑E² + ‖G(core)‖²` and the additive split applies to `G(core) = ∏S_s` alone. The
`reg`-dependence of `R` is a bounded perturbation peeled like the endpoint-regular leak.

---

## PRECISION (#62 follow, pp-hall, 2026-06-22) — the LITERAL loss core is the FULL-product Schur `‖R‖²`; `‖∏S_s‖²` is its UNIT-PEELED reduced form

cobuild-sub34's g157 sharpens the per-layer Schur correction above: even the per-layer SCHUR PRODUCT
`∏S_s` is NOT the literal loss core — the literal core is the **full-product Schur** `‖R‖²`,
`R = P_{11} − P_{10} P_{00}⁻¹ P_{01}`, and `R ≠ ∏S_s` as polynomials. They are related by an inter-layer
unit (verified exact, `g157_check.py`/`g157_reconcile.py`, 2-layer scalar):

    R  =  S_1 · g · S_2,        g = AB/(AB + VY)   (the inter-layer gauge unit),

where `g` is a **bounded unit at `w0`**: `g(w0) = 1` (A=B=1, Y=V=0), `g → 1` nearby. Hence

    ‖R‖²  =  g² · ‖∏S_s‖²,     g² a bounded unit  ⟹  ‖R‖²  ≍  ‖∏S_s‖²     (same `rlctAt`, via the unit peel).

So the honest hierarchy (three precision levels, all consistent — the same RLCT object):
1. **the loss core (literal):** `‖R‖²`, the FULL-product Schur complement — what `dlnLoss H B` actually
   carries off `{E=0}` (the `−B` and the regular residuals couple into `R`). This is g157 / cobuild-sub34's
   #54 `R`, exactly right.
2. **`‖R‖² ≍ ‖∏S_s‖²`** up to the bounded inter-layer unit `g²` (a SQUEEZE / unit-comparability, tight at
   `w0`, NOT exact equality — the SAME pattern as the `c₁<c₂` squeeze, not the false `c₁=c₂=1` exact germ).
3. **`‖∏S_s‖² = dlnLoss(M)0`** (the per-layer Schur-reduced chain) — the unit-peeled reduced form, the
   object fed to `rlct_additive_smooth_block`. RLCT-equivalent to `‖R‖²`, not literally equal.

**The overstatement this corrects in the body above:** the CORRECTION section wrote `‖∏S_s‖²` as if it
were the literal reduced core (`R = T̃_1···T̃_L` "after the det-unit Schur change"). The precise version:
the loss core is `‖R‖²` (full-product); `‖∏S_s‖²` is `‖R‖²` with the inter-layer unit `g` peeled
(RLCT-equivalent, via the bounded-unit transport `rlctAtOn_unit_invariant_aux` — the same NON-MP machinery).
Both the unit→Schur correction (`T̃_s → S_s`, g172 above) AND this `∏S_s → R` precision are instances of
the recurring lesson: the honest object is reached by peeling a bounded unit, and the comparability is a
unit-SQUEEZE, never an exact germ. (`ofExactGerm`, `c₁=c₂=1`, is un-dischargeable here — the exact germ is
FALSE; the genuine `core_comparability_squeeze`, `c₁<c₂`, is the constructor to use — flagged to crux2.)

**Consistency with the D1 g173 L2-at-general-v cert:** the core fed to the additive split there is `‖R‖²`
(`≍ ‖∏S_s‖²` via the unit), so the constant-active-block split is against the full-product `R` at the
induced basepoint `D(v)` — consistent with g157.

---

## PRECISION (#62 follow-2, pp-hall, 2026-06-22) — EXACT-via-Morse-c-o-v vs SQUEEZE-in-raw-coords (the two coordinate frames)

cobuild-sub34's final sharpening (g158): "the exact germ is FALSE" was itself too strong — the precise
truth is a TWO-FRAME distinction, both valid:

- **RAW gauge-block coords (no further c-o-v):** the loss is a SQUEEZE, NOT exact:
      dlnLoss  =  ∑E²  +  ‖R‖²  +  (2⟨R, leak⟩ + ‖leak‖²),     leak = E_{10}(I+E_{00})⁻¹E_{01}.
  The correction `2⟨R,leak⟩ + ‖leak‖²` is nonzero, bounded by `∑E²` (c₁<c₂→1 at `w0`), the genuine
  two-sided squeeze `core_comparability_squeeze` (c₁=(2(1+t²))⁻¹, c₂=2+2t²). This is the **Lean datum** —
  no explicit change of variables built.
- **AFTER an analytic MORSE / splitting-lemma c-o-v `φ`:** the germ IS exact:
      dlnLoss ∘ φ  =  ∑Ẽ²  +  ‖R‖²        (c₁=c₂=1, the exact germ).
  This holds because (verified, `g158_morse_exact.py`) the correction is `O(reg²·core)` and higher —
  EVERY term carries factors of the regular coords `E_{10}·E_{01}` (numeric: `corr/∑E² → 0` as `→ w0`),
  with **NO pure-core term**. That is exactly the splitting-lemma condition: the regular block
  `(E_{00},E_{01},E_{10})` is nondegenerate (Jacobian rank `= nReg` at `w0`) and the correction is a
  higher-order-in-`E` perturbation absorbable by `Ẽ_i = E_i + h.o.t.(E, core)` completing the square. The
  c-o-v `φ` **exists** (real theorem); it is **not formalized**.

**Reconciliation of the cert lineage (the apparent flip-flops, all consistent):**
- #48/g150 "exact germ via the gauge chart" — TRUE under the exact-via-`φ` reading (the g150 body did say
  "a parameterized analytic Morse/splitting lemma gives the exact germ"). NOT an overclaim.
- g155 squeeze-downgrade — TRUE under the raw-coords reading (what the Lean builds). NOT a contradiction.
- The two describe the two coordinate frames (with/without `φ`), not opposite truth-values.

**What the Lean uses:** the SQUEEZE (`core_comparability_squeeze`, c₁<c₂), sidestepping the construction
of `φ`. `ofExactGerm` (c₁=c₂=1) is dischargeable IN PRINCIPLE (build `φ`) but strictly harder and
unnecessary — the squeeze suffices for the RLCT. So `ofExactGerm` is a trap as a *required* constructor
(flagged to crux2); the genuine datum is the two-sided squeeze.

**The complete honest hierarchy (all four levels, RLCT-equivalent, decreasing literalness):**
1. raw-coords loss `= ∑E² + ‖R‖² + O(reg²·core)`  — SQUEEZE (c₁<c₂→1 at `w0`), the formalized datum;
2. via `φ`: `∑Ẽ² + ‖R‖²`  — EXACT (c₁=c₂=1), the underlying truth, `φ` not formalized;
3. `‖R‖²`  — the literal core (full-product Schur `R = P_{11} − P_{10}P_{00}⁻¹P_{01}`);
4. `‖R‖² ≍ ‖∏S_s‖²` via the inter-layer unit `g` (g174 above); `‖∏S_s‖² = dlnLoss(M)0` the reduced chain
   fed to `rlct_additive_smooth_block`.
Each `≍` is a bounded-unit comparability (a squeeze, tight at `w0`), never an exact equality without a
further c-o-v. The recurring lesson: the honest object is reached by peeling bounded units; name the
comparability a unit-squeeze, and name which coordinate frame the "exact" claim lives in.
