# g156 — soundness adjudication: is the general-M headline comparability-free via the COVER route?

**Seat.** pen-and-paper (obstruction/soundness adjudication), DLNFibre aoyagi-full, task #10.
**Method.** exact symbolic algebra (sympy 1.14, ℚ-exact) + a fresh DECORRELATED xhigh Codex pass
(hypothesis withheld). No Lean. **Verification:** `g156-adjudication-scripts/adjudicate_g156{,_B,_C,_D}.py`
(all consistent). **Codex:** `codex/g156-adjudication-cover-route-prompt.md` (independent derivation,
confirms cover comparability-free).

> **HEADLINE VERDICT.** The general-M headline
> `rlctAtOn(dlnLoss M 0)(deepest) = ½·minAdm(M)` is **SOUND AS-IS via the comparability-free COVER
> route (R1)** — verdict **(a)**. The false `‖R‖² ≍ ‖∏S_s‖²` full-product comparability (the g156
> finding) is a **squeeze-route (L2) issue and is NOT load-bearing**: it is consumed by NOTHING on the
> integration headline branch (`fm3/routem-ga-transport`); the headline routes through the
> route-INDEPENDENT `BindingSpine` whose `hstep` producer is the weighted-cover, which recurses on the
> REAL child loss `dlnLoss(red M) 0` and never forms `R` or `∏S_s`. No `(NC)` / scalar-reduced-core
> restriction is needed for the headline, even though reduced-dim ≥ 2 IS DLN-achievable.

---

## The two routes, and what each consumes (the architectural fact, VERIFIED against the Lean)

The headline reaches the per-node atom by ONE of two designs:

- **L2 SQUEEZE** (`deepest_loss_squeeze`, branch `fm2/deepest-gauge-chart-sub34`). Peels ALL `L`
  layers at once: normal form `Φ = ∑E² + ‖∏S_s‖²-core`, comparing the LOSS-side full-product Schur
  core `R` against the absorbed per-layer product `∏S_s` (`DeepestGaugeChart.lean` §contract: "the
  full-product `R` (`= ∏S_s` only on `{E=0}`) is the LOSS-SIDE comparison … via
  `core_comparability_squeeze`"). **NEEDS** `‖R‖² ≍ ‖∏S_s‖²`.
- **R1 COVER** (`RouteMNodeDescent.descentStep` + the outer product-min, branch
  `fm3/routem-ga-transport`). Blows up ONLY the deepest layer (`A = y₀·Â`), `F = y₀²·core`,
  `|Jac| = y₀^{mk−1}`, then recurses on the SINGLE-STEP Schur child `‖S·Bred‖² = dlnLoss(red M) 0`,
  `S = D − b·a` the Schur complement of ONE layer. **NEVER forms** `R` or `∏S_s`.

**Decisive wiring fact (Lean, `git grep` on `fm3/routem-ga-transport`):**
`deepest_loss_squeeze` / `core_comparability` / `DeepestGaugeChart` are consumed by **NOTHING** on the
headline branch. `BindingSpine.binding_rlct_eq_lambdaCore_of_hstep'` is **route-independent** (takes
`hstep`/`hbase` abstractly) and is instantiated with `rlctOf := fun M => rlctAtOn (dlnLoss M 0)(deepest)`
— the REAL loss. The file's own route note: *"the actual producer of `hstep` … is the WEIGHTED-COVER
route (#104), NOT the MP-chart bridge `RouteMO1Bridge` (re-scoped as flawed-for-blow-ups)."* So the
L2 squeeze's false comparability is **redundant for the headline**, exactly as the controller hypothesised.

---

## Q1 — Does the COVER route establish the per-node `min` recursing on the REAL child, WITHOUT `‖R‖²≍‖∏S_s‖²`? **YES.**

The cover atom is two composed pieces, BOTH comparability-free:

**OUTER product-min** (`S1WeightedProductMin.weightedProductMin_rlct`, fully proved, three legs):
`weightedThreshold (G·H, ρ) = min( weightedThreshold G ρ , rlctAtOn H 0 )`, instantiated `G=y₀²`,
`H=core`, `ρ=|y₀|^{mk−1}`. I read all three legs of the proof:
- `wpm_le_left`, `wpm_le_right`: use only integrand positivity + the rectangle Fubini split.
- `wpm_ge` (the **LE / below-threshold-divergence leg — the controller's flagged suspect**): uses ONLY
  the **down-set extractors** `hdown` / `hdownH` — "for `q < rlctAtOn H 0`, the child integrand `|H|^{−q}`
  is integrable on some nbhd of `0`". This is the *definition* of `rlctAtOn H 0` as a sup, applied to
  `H = core` directly. **It references NO product-of-Schur object.** The LE leg does NOT secretly need
  `core ≍ ∏S_s`; it needs only that `core`'s own RLCT is a down-set — true by construction. (FACT, read
  from `S1WeightedProductMin.lean:159-191`.)
- `S1BoxProductMin` supplies the box-form integrability the cover's `g5_flat_cover` finite-sum consumes;
  again positivity + Fubini split, no comparability. (FACT.)

**INNER core squeeze** (`schur_recursion_step_squeeze` / `IsSchurStraightenSqueeze`,
`GeneralR1Recursion.lean`): squeezes `core` by `Φ = ∑Erow² + G²` where the structure pin is
`redCore_eq : ∀ y, G y² = dlnLoss S.red 0 (redEmbed y)` — **`G²` IS the real reduced-chain DLN loss**.
The squeeze rests on `flatCore − Φ ∈ ideal(E)` via `schur_row_decomp`: the lower product rows are
`lower = b·Erow + S·Bred`, `S = D − b·a`, certified as the exact row identity (verified §B). This is the
SINGLE-STEP Schur complement of ONE layer, not `∏S_s`.

The child is closed by `ReducedTransport.descent`: `rlctAtOn(G²)0 = rlctAtOn(dlnLoss S.red 0)(deepest)`
via a det-1 MP reindex — recursing on the **genuine DLN reduced chain** `S.red = (M⁰−1, M¹−1, M², …)`,
layer count `L` preserved. **Verdict: the cover establishes the per-node `min` recursing on the real
child, comparability-free. (FACT for the OUTER min legs + the row-decomp; the assembly into the headline
is open formalisation, see §Status.)**

---

## Q2 — Is the L2 squeeze LOAD-BEARING for the headline, or redundant given R1? **REDUNDANT.**

`git grep` on `fm3/routem-ga-transport` for `deepest_loss_squeeze`, `deepest_gauge_squeeze_exists`,
`DeepestGaugeChart`, `core_comparability` returns **nothing** in `lean/`. The headline (the `#151`
instantiation of `binding_rlct_eq_lambdaCore_of_hstep'` with `rlctOf = rlctAtOn(dlnLoss · 0)(deepest)`)
consumes the cover `hstep`, not the L2 squeeze. Nothing the headline depends on routes through L2
part-(4). **The false comparability is an L2-only issue; the headline does not touch it.**

---

## Q3 — The g156 counterexample, and whether the SINGLE-STEP comparability survives it. **It survives; the mechanism cannot attack it.**

**The L2 counterexample reproduces EXACTLY** (§A, `adjudicate_g156.py`): `L=2, r=1, reduced-dim=2,
ε=1/7`, `K₁=ε e₂, Y₂=ε e₁ᵀ, S₁=ε E₁₁, S₂=ε E₁₂`, `Y₁=−Y₂S₁, K₂=−S₂K₁` ⟹ `E=0` exactly,
`∏S_s = S₂S₁ = 0`, but `R = P₁₁ − P₁₀P₀₀⁻¹P₀₁ = −ε⁴E₁₁ = −1/2401·E₁₁ ≠ 0`. So `‖R‖² ≤ γ‖∏S_s‖²`
fails (RHS=0 < LHS). The leakage is `R − ∏S_s = −S₂K₁H⁻¹Y₂S₁`, inter-layer cross-talk.

**The single-step R1 comparability is a DIFFERENT, sound statement** (§C, `adjudicate_g156_C.py`):
`core ≍ Φ = ∑Erow² + ‖S·Bred‖²` near `b→0`. Exact facts:
- `{core=0} = {Φ=0}` exactly: `Φ=0 ⟹ Erow=0 ∧ S·Bred=0 ⟹ core=0`; and `core=0 ⟹ Erow=0` (1st block)
  `⟹ S·Bred = −b·Erow = 0 ⟹ Φ=0`. Same zero-set. (FACT, sympy.)
- `core − Φ ∈ ideal(b)`: every monomial of `core − Φ` carries a factor `bᵢ` (min total `b`-degree = 1),
  so it vanishes at the deepest point `b=0`. The comparison is a **bilipschitz change of variables**
  `(Erow, S·Bred) ↦ (Erow, b·Erow + S·Bred)` (identity Jacobian at `b=0`), NOT a product-cancellation.
  (FACT, sympy; Codex Q2 confirms independently.)
- **The ε mechanism has nothing to attack:** it required REPLACING the real child by a product-of-Schur
  surrogate (`R` vs `∏S_s`) and exploiting their inter-layer cancellation. The R1 `Φ` uses
  `‖S·Bred‖² = dlnLoss(red M) 0` — the real child — **verbatim, no surrogate**. There is no
  `∏`-of-cores to cancel against. (INFERENCE, structural; Codex Q2.4 confirms: in the single-step map
  `S·Bred` enters linearly inside an invertible CoV, so zeroing it forces the whole block to vanish.)

---

## Q4 — DLN-dischargeability of `(NC)`; is reduced-dim ≥ 2 DLN-achievable at a deepest point?

**Reduced-dim ≥ 2 IS DLN-achievable** (§D, NOT an abstract-matrix artifact). reduced-dim `= H_s − r`;
the ε example has `r=1`, reduced-dim `=2`, i.e. an intermediate width `H=3` at a rank-1 deepest point —
a perfectly legal DLN node. So the `(NC)` / scalar-reduced-core hypothesis (all intermediate reduced
dims `=1`) is **NOT automatic** for general DLN. **Therefore `(NC)` is NOT dischargeable from the DLN
deepest-point structure, and the L2 route — IF it were load-bearing — would be genuinely scoped (only
sound under scalar-reduced-core).**

**But `(NC)` is moot for the headline**, because the cover route does not need it:
- The cover recursion descends the WIDTH vector `(m,k,n) → (m−1,k−1,n)` (real chain reduction), and each
  child loss is `dlnLoss(red M) 0` = the genuine DLN reduced-chain loss (Lean: `hredCore`,
  `ReducedTransport.descent`). The `∏S_s` object is **never assembled**, so the inter-layer cross-talk
  `R − ∏S_s` that breaks L2 never arises. (FACT for the Lean pin; INFERENCE that this holds at every
  recursion step — generic-status is inductively preserved because each child loss is again a
  two-free-matrix product loss by the V3 reduced-core identity; Codex Q1/Q4 confirm.)

---

## BOTTOM LINE

| question | verdict |
|---|---|
| Headline soundness | **(a) sound AS-IS via the comparability-free cover route** |
| `‖R‖²≍‖∏S_s‖²` (L2) | FALSE (ε=1/7 reproduced exact); **NOT load-bearing** (consumed by nothing on the headline branch) |
| Cover LE leg needs comparability? | **NO** — `wpm_ge` uses only the down-set property of `rlctAtOn(core)` itself |
| Single-step comparability `core ≍ ∑Erow²+‖S·Bred‖²` | **SOUND** (same zero-set; `core−Φ ∈ ideal(b)`; bilipschitz, not cancellation) |
| `(NC)` / scalar-reduced-core needed for headline? | **NO** (cover never forms `∏S_s`) |
| reduced-dim ≥ 2 DLN-achievable? | **YES** (intermediate width `≥ r+2`); so `(NC)` is NOT automatic — but moot for the headline |

**Most likely thing to break it.** The OUTER product-min's `≥`/down-set legs are proved, and the
single-step row-decomp is exact — the soundness is firm. The residual RISK is **not soundness but
COMPLETENESS of the assembly**: (i) the per-node `descentStep` currently proves the INNER relation
`rlctAtOn(flatCore)(0,0) = nReg/2 + rlctAtOn(child)`, which is `rlct(core)`, NOT `rlct(F)` — the OUTER
`min{mk/2, ·}` must wrap it (cert-104b §2, the `min{mk,n+R}=nReg+R` reconciliation with
`nReg=min{mk−R,n}`); feeding the inner squeeze with `nReg:=n` at a WIDE-TAIL node (smallest `(2,2,4)`)
WITHOUT the outer min would over-count (the cert-104 obstruction). (ii) `RouteMRecursion.lean` carries a
named `sorry` for the GENERAL pivot branch (the realizability/coverage theorem). These are open
formalisation, flagged so a formaliser wraps the outer min and does not transcribe a bare `nReg:=n`
squeeze as `rlct(F)`.

**Next construction to settle the open part.** Land the OUTER weighted product-min as the per-node
`rlct(F) = min{mk/2, rlct(core)}` wrapper (the `weightedProductMin_rlct` lemma EXISTS; the gap is the
cover-vs-single-chart surjectivity correction in cert-104b §4 — the argmax/pivot COVER, glued by
finite-cover-locality, since `φ₁` alone is non-surjective). Then the arithmetic collapse
`min{mk/2, n/2+R/2} = nReg/2 + R/2` reconciles to the spine `hstep`, closing the headline — all
comparability-free.

---

## ADDENDUM — the recursion SHAPE: clean point-min vs threaded box-integrability

(Added per controller follow-up + a5f5ceb1's GE-leg gate finding. Scripts: `box_geometry.py`,
`interior_sing.py`, `deepest_is_min.py`; Codex: `codex/g156-adjudication-box-vs-pointmin-prompt.md`.)

**The question.** Does the node RLCT cleanly equal `min{mk/2, n/2 + rlctAtOn(child)}` (a POINT-MIN
recursion, box-recursion internal to the proof), or does it genuinely depend on the child's FULL-BOX
integrability (strictly stronger than the child's point-RLCT), forcing box-integrability into the
atom↔spine interface? The cover GE-leg owner (`S1NodeCoverGE.lean`) states the latter.

**Finding: the VALUE statement is the clean point-min; the GE-leg PROOF threads box-integrability, and
the two coincide ONLY because the deepest point is the global-minimum-RLCT point of the child.** This
is more subtle than a pure germ argument (and corrects one Codex INFERENCE).

1. **The chart `z`-coordinates are RATIOS, NOT shrinkable with `U`.** On pivot chart `φ_p`,
   `a₀ⱼ = y₀·uⱼ` etc., so `z = (u,v,W) = (off-pivot entries)/y₀`. Shrinking the cover nbhd `U` (small
   `‖A‖`) does NOT bound the ratios: a small `a₀ⱼ` over an even smaller `y₀` gives large `u`. Codex's
   INFERENCE "shrink `U` ⟹ `φ⁻¹(U) ⊂ {|y₀|<ε}×W_z`" is **WRONG** for the ratio coords. (FACT,
   `box_geometry.py`.)

2. **The argmax cell fixes the ratio box SCALE-INVARIANTLY.** The sound cover uses the argmax cells
   `{|a₀₀| = maxᵢⱼ|aᵢⱼ|}`, where `|u|,|v|,|W| ≤ 1` — a FIXED box `[-1,1]^{mk−1}`, independent of `‖A‖`.
   The blow-up trades a small `A`-region for `{|y₀|<ε} × {ratios in fixed [-1,1]}`. So the core's
   `z`-integral genuinely runs over a **fixed** ratio box `Vz`; it does not shrink. (FACT.) Hence the
   GE-leg's `hKint` (= `|core|^{−c} integrable over Vz`) is **not** discharged by the child's
   point-RLCT germ alone — `S1NodeCoverGE`'s author is correct that the proof threads full-box
   integrability.

3. **Box-integrability `⟺ c < rlctAtOn(child, deepest)` — coincides with the point-RLCT — BECAUSE the
   deepest point is the global-min-RLCT point.** On `Vz` the only singularities of `|child|^{−c}` are
   along `{child = 0} = {S·Bred = 0}` (the zero-product variety, which has MANY strata, not just the
   origin). Box-integrability requires `c <` the local RLCT at EVERY point of `Vz ∩ {child=0}`. The
   structural fact (paper / Aoyagi-LR): the all-zero deepest point has the MAXIMAL simultaneous
   rank-drop, so it achieves the **minimum** local RLCT over the whole zero-locus; any partial-vanishing
   stratum drops fewer ranks ⟹ `rlct(child, p) ≥ rlct(child, deepest)`. Verified on `(1,1,2)`: deepest
   `1/2` (the min); `(s=0,b≠0)` ties at `1/2`; `(s≠0,b=0)` is `1` (larger). (FACT, `deepest_is_min.py`.)
   So by compactness on the fixed `Vz`, `∫_{Vz}|child|^{−c} < ∞ ⟺ c < rlctAtOn(child, deepest)` — the
   box-fact and the point-fact have the SAME threshold value.

4. **Architecture verdict.** The **value-level recursion `rlctOf(M) = min{mk/2, n/2 + rlctOf(child)}`
   is the correct RLCT-level statement** — the binding-spine `hstep` does NOT need reshaping to carry
   box-integrability as a value. BUT the **GE-leg PROOF interface** does thread box-integrability: to
   prove `rlctOf(M) ≥ c` over the argmax-cover, the recursion must supply `∫_{Vz}|child|^{−c} < ∞`,
   which recurses as the CHILD's own argmax-cover (a further blow-up `recStep`, the `(2,2,2)`
   `resolved_residual_lt_top` precedent on the fixed `cube8`), NOT the child's point-RLCT as a black
   box. The box-recursion is **internal to the GE-leg proof**; it coincides with the point-min value
   exactly because of the global-min-RLCT structural fact in (3).

**What this means for a617 (the spine) and the formaliser.**
- The spine statement `rlctOf M = min{...}` (or its `bindNReg/2 + child` reconciliation) is the right
  shape — keep it at the point-RLCT value level. (No reshaping.)
- The per-node GE-leg producer must emit, recursively, the child's **box-integrability over its argmax
  ratio box**, NOT just invoke `rlctAtOn(child)` abstractly. Concretely: the recursion carried by the
  cover is "argmax-cover at each node, recurse on the child's argmax-cover over its fixed ratio box,"
  bottoming out at the leaf monomial — exactly the `g5`/`recStep` shape, dimension-uniform.
- The load-bearing LEMMA the general proof needs (beyond the `(2,2,2)` instance): **the deepest point is
  the global-minimum-RLCT point of `dlnLoss` over any bounded region** (equivalently, every
  partial-vanishing stratum of `{∏Aₛ = 0}` is less singular than the all-zero point). This is the
  structural input that makes box-integrability collapse to the point-RLCT value. It should be NAMED in
  the atom↔spine interface as the side-fact the GE-leg consumes — currently implicit in the
  fixed-cube `recStep` machinery.

**Soundness impact: NONE on the headline value.** The headline `rlctAtOn(dlnLoss M 0)(deepest) =
½·minAdm(M)` is the correct value and the point-min recursion computes it. The box-threading is a
PROOF-SHAPE fact (the GE-leg recurses on box-integrability, governed internally by the global-min-RLCT
structure), not a value-level restriction. **Verdict (a) stands**; the addendum sharpens the
proof-interface a617/the formaliser must carry (box-integrability recursion + the named global-min
side-fact), and confirms it is comparability-free throughout (no `∏S_s` anywhere in the box recursion).

---

## ADDENDUM 2 — the DLN box-collapse: clean point-min HOLDS for ALL DLN nodes (reduced-dim irrelevant)

(Per controller's sharpened follow-up after a5f5ceb1's GREEN Lean confirmed the GENERAL cover interface
threads child FULL-BOX integrability `hKint = IntegrableOn |core|^{−c'} over Vz`, not `rlctAtOn core 0`.
Scripts: `dln_box_collapse.py`, `interior_rlct_exact.py`, `interior_rlct_2.py`, `reconcile.py`,
`verify_collapse_final.py`; Codex: `codex/g156-adjudication-global-min-rlct-prompt.md`. A self-correction
of Addendum-1's rank model is recorded — see (0).)

**The settled general fact (a5f5ceb1).** For ARBITRARY M, the cover GE leg threads the child's full-BOX
integrability over the fixed argmax ratio box `Vz`, NOT the child's point-RLCT — green axiom-clean Lean
(`chart_pullback_lt_top_of_boxpm`). So the proof-interface genuinely carries box-integrability.

**The DLN-specific question (this addendum).** Does the DLN child loss, over `Vz`, have its WORST RLCT
at the all-zero deepest point — so box-integrability `⟺ c' < rlctAtOn(child, deepest)` and the clean
point-min `rlctAtOn(node) = min{mk/2, n/2 + rlctAtOn(child)}` holds at the VALUE level — or does
reduced-dim ≥ 2 create an interior stratum with strictly smaller RLCT, forcing genuine box-recursion?

**VERDICT: the clean point-min interface HOLDS for ALL DLN nodes, reduced-dim ≥ 2 INCLUDED. The
box-collapse is NOT equivalent to scalar-reduced-core (that framing is a red herring); it holds via
rank-profile minimality of `minAdm`, which is dimension-free.**

**(0) Self-correction.** Addendum-1's "rank-ρ stratum ⟹ smaller codim" model was WRONG: a product of
rank ρ > 0 has loss > 0, so it is NOT on `{F=0}`. The correct picture: `{F=0} = {∏Aₛ = 0}`, and EVERY
singular point of `|F|^{−c}` has product EXACTLY zero. The strata are by the rank PROFILE of the partial
products (all giving product 0), which are exactly the LR admissible profiles. (FACT, `reconcile.py`.)

**(1) Local RLCT at each stratum = ½·mval(M, R(p)).** At a point `p ∈ {∏Aₛ = 0}` with partial-product
rank profile `R(p)`, the loss pulls back on a slice as `u^{mval(M, R(p))}·(unit)`, so
`rlct(F, p) = ½·mval(M, R(p))`. This is the LR/Aoyagi resolution structure (each rank-profile stratum's
exceptional divisor contributes `½·mval`). **STATUS: CITED** (LR Thm / Aoyagi resolution) — I did not
re-derive the slice-normal-form in general; I verified its CONSEQUENCE on small cases (§below). The
`rlct = ½·codim` reading itself rests on the cited `rlct ≤ ½·codim` analytic bound (per CLAUDE.md).

**(2) `mval(M, T) ≥ minAdm(M)` for every admissible profile `T` — DEFINITIONAL.** `minAdm(M) = min_T
mval(M, T)` over admissible `T`. Verified over M ∈ {(2,2,1),(2,2,2),(3,3,2),(3,3,3),(2,2,4),(3,2,5),
(4,3,2),(2,4,3),(5,4,7)}: every admissible profile has `mval ≥ minAdm`. (FACT, `verify_collapse_final.py`.)

**(3) Every zero-product stratum is an admissible profile — no escape.** The GL-orbit decomposition of
`{∏Aₛ = 0}` is indexed EXACTLY by the LR admissible rank profiles (the Gabriel/Kostant translation).
reduced-dim ≥ 2 widens the AMBIENT but the orbit strata remain admissible profiles. So there is NO
stratum outside the admissible set that could have `mval < minAdm`. (CITED: the LR orbit↔Kostant
correspondence; the engine the harness formalises in `DLNFibre.Core`.)

**Composing (1)+(2)+(3):** `rlct(F, p) = ½·mval(M, R(p)) ≥ ½·minAdm(M) = rlct(F, deepest)` for EVERY
`p ∈ {F=0}` and every M. Ties occur when `R(p)` realizes `minAdm` (e.g. one factor entirely zero,
the `{s=0,b≠0}` tie at `1/2` for (1,1,2)); never strictly below. Worked exact checks: (1,1,2) deepest
`1/2`, interior strata `1/2` (tie) and `1`; (2,2,1) deepest `1`, interior `1` (tie). (FACT,
`interior_rlct_exact.py`, `reconcile.py`.) Decorrelated xhigh Codex independently derived the same:
*"all-zero is global-min-RLCT (ties ok): point-min collapse HOLDS because every other stratum's mval is
≥ minAdm(M)."*

**Consequence — the box collapses to the point-min VALUE.** Box-integrability of `|F_child|^{−c'}` over
the fixed `Vz` is governed by the smallest local RLCT over `Vz ∩ {F_child=0}`. Since the deepest point
achieves that minimum (ties harmless — a tie stratum is integrable at the SAME threshold `c' < ½·minAdm`),
`∫_{Vz}|F_child|^{−c'} < ∞ ⟺ c' < rlctAtOn(F_child, deepest)`. Therefore:

> **`rlctAtOn(node, deepest) = min{ mk/2 , n/2 + rlctAtOn(child, deepest) }` holds at the VALUE level,
> for ALL DLN nodes.** The spine recursion `rlctOf M = min{…}` / `bindNReg/2 + child` is the RIGHT
> RLCT-level statement and needs NO reshaping. The box-integrability that a5f5ceb1's GE leg threads is
> the PROOF MECHANISM that REALIZES this value (the recursion supplies the child's box-integrability via
> its own argmax-cover, bottoming at the leaf), governed internally by the global-min structural fact.

**Answer to the controller's `box-collapse ⟺ scalar-reduced-core` framing: NO, it is NOT that
equivalence.** The collapse holds for reduced-dim ≥ 2 too. The deciding invariant is NOT scalar-ness of
the reduced core but **rank-profile minimality**: every stratum of `{∏Aₛ=0}` is admissible, hence
`mval ≥ minAdm`, hence the deepest point is the global-min RLCT — dimension-free. The g156 scalar/`(NC)`
question (which DID matter for the refuted L2 `∏S_s` route) is a RED HERRING for the cover's
box-collapse.

**Honest scope of what is PROVED here vs CITED.**
- VERIFIED exact (mine): `mval ≥ minAdm` definitionally over a width census; the local-RLCT VALUES at the
  zero-product strata on small cases (1,1,2), (2,2,1) — deepest is the min, ties never dip below.
- CITED (LR/Aoyagi, the harness's engine + analytic bound): (i) `rlct(F, p) = ½·mval(M, R(p))` per
  stratum (resolution structure); (ii) the zero-product orbit strata = admissible profiles (Kostant);
  (iii) `rlct = ½·codim` (the `rlct ≤ ½·codim` direction, Aoyagi/Watanabe).
- The headline VALUE soundness does not hinge on (i)–(iii) being re-proved by the cover: the cover's GE
  leg directly establishes box-integrability `< mk/2` (the `y₀` divisor) AND recurses the child box; the
  global-min fact is what lets the recursion CLOSE at the point-min value. For a fully self-contained
  Lean proof, the load-bearing NAMED side-fact is: **the all-zero deepest point is the global-minimum
  local RLCT of `dlnLoss M 0` over any bounded region** — provable in-engine from "every zero-product
  stratum is admissible ⟹ `mval ≥ minAdm`", NOT requiring the external `rlct ≤ ½·codim` cite for the
  ORDERING (the ordering is combinatorial: `mval(M,R(p)) ≥ minAdm(M)`).

**Action item refinement for a617/the formaliser.** Name in the atom↔spine interface the side-fact
**`global_min`: `∀ p ∈ {dlnLoss M 0 = 0}, rlctAtOn(dlnLoss M 0) p ≥ rlctAtOn(dlnLoss M 0) deepest`**,
reducing (in-engine) to the combinatorial `mval(M, R(p)) ≥ minAdm(M)` (admissible-profile minimality) +
the per-stratum `rlct = ½·mval` (CITED). This is what collapses the GE-leg's box-integrability to the
point-min value — dimension-free, comparability-free (no `∏S_s`).

---

## ADDENDUM 3 — correction to the `global_min` statement shape (deriv-finish's `T=0` catch)

(deriv-finish, formalising #11, flagged a fidelity subtlety that sharpens the `global_min` statement
and CORRECTS the framing of Addendum-2's "deepest achieves minAdm". Script: `clarify_deepest.py`.)

**The catch.** The all-zero EXPONENT vector `T=0` (Aoyagi `t⁽ʲ⁾`, a rank-PROFILE) gives
`Mval(M, T=0) = M⁰·M¹` (only the `j=0` term survives), which is NOT the `minAdm` minimizer in general:
(2,2,1) `Mval(T=0)=4` vs `minAdm=2` (argmin `T∈{(1,0),(2,0)}`); (2,2,2) `Mval(T=0)=4` vs `minAdm=3`
(argmin `(1,0)`). So "the deepest achieves `minAdm`" is NOT the trivial reading "`T=0` minimizes `Mval`"
— `T=0` is the TRIVIAL top-stratum codim, the largest top divisor. (FACT, `clarify_deepest.py`.)

**The correction (sharpens, does not weaken, the verdict).** The exponent-vector `T` (a rank profile)
and the deepest PARAMETER point (all `Aₛ=0`) are different objects. `minAdm = ½·min_T Mval` is the min
over the WHOLE admissible cone; the deepest PARAMETER point's local RLCT equals that full min because it
sits under ALL the blow-up centers (the binding divisor is the min-`T`, not `T=0`). **Identifying the
deepest-parameter-point RLCT with `½·minAdm` IS the cited Aoyagi resolution — and is CIRCULAR with the
headline** (`rlct(deepest) = ½·minAdm` is the headline) AND beyond the only-S2 cite budget. So the
`Mval`/`rankProfile`/`rlct=½mval`-per-stratum decomposition of Addendum-2 is the WRONG constructive
route, even though its inequality `mval ≥ minAdm` is true.

**The honest `global_min` statement (what #11 should be).** `global_min` needs ONLY the RLCT-ORDERING
among PARAMETER points — `∀ v in the fibre, rlctAtOn(F, deepest) ≤ rlctAtOn(F, v)` — which is the
VALUE-FREE "most-degenerate point has the smallest RLCT", provable from **homogeneity + lower
semicontinuity** with NO `Mval`/`minAdm`/`rankProfile`/per-stratum value and NO Aoyagi cite. This is
ALREADY PROVEN on `fm/deriv-frame-resume` as `deepest_le_of_homogeneous_core` (`DeepestMinRlct.lean`:
L1-a ray-scaling-invariance + L1-b lsc, zero sorries). So:
- **rlct-ordering leg of #11** = the existing value-free `deepest_le_of_homogeneous_core`. No cite.
- **box-collapse leg of #11** (the genuinely-new PROVED content) = from the ordering, a finite-subcover
  of the compact `Vz ∩ {F=0}` (each `v` has a local-integrability nbhd for `c' < rlctAtOn(F,v) ≥
  rlctAtOn(F,deepest)`; compactness ⟹ finite subcover ⟹ box lintegral finite). This is the
  `(ii)⟹box-integ` bridge a5f5ceb1's `hKint` consumes.

**Status of Addendum-2's reduction.** The `mval(M,T) ≥ minAdm(M)` reduction + the exact small-case
checks remain valid as the **independent soundness CROSS-CHECK** that the ordering is correct for all M
(decorrelated from the constructive `deepest_le` path) — NOT the constructive route. This is the
controller's framing and the right division of labour: the adjudication seat supplies the
exponent-combinatorial confirmation; the formaliser builds the value-free homogeneity+lsc route.

**Verdict (a) unchanged.** The headline is sound; the recursion is the clean point-min value; the
box-collapse bridge is value-free and Aoyagi-cite-free. Addendum-3 only corrects the SHAPE of the named
`global_min` interface (drop the exponent-vector detour; use the proven `deepest_le` + finite-subcover),
removing a circularity-with-the-headline that the `Mval`-per-stratum framing would have introduced.

---

## ADDENDUM 4 — what the box-collapse bridge (#11) actually consumes: the ORDERING only

(deriv-finish, building #11, asked whether "deepest realizes minAdm" is a confirmed general-M FACT to
cite. The precise answer pins the Proved/Cited boundary and closes a circularity. Script:
`what_collapse_needs.py`.)

**What the GE value-closing bridge consumes — decomposed.** The bridge `IntegrableOn |F|^{−c'} Vz ⟸
c' < rlctAtOn(F, deepest)` decomposes as:
- `∫_{Vz}|F|^{−c'} < ∞ ⟸ ∀v ∈ Vz, ∃ W_v nbhd, ∫_{W_v}|F|^{−c'} < ∞` (finite subcover of the compact
  `Vz ∩ {F=0}`; off the zero-locus the integrand is bounded);
- `∫_{W_v}|F|^{−c'} < ∞ ⟸ c' < rlctAtOn(F, v)` (the DEFINITION of `rlctAtOn` as the sup over admissible
  neighborhoods — the down-set extractor).

So, given `c' < rlctAtOn(F, deepest)`, the bridge needs `∀v, c' < rlctAtOn(F, v)`, which holds **iff
the ORDERING `rlctAtOn(F, deepest) ≤ rlctAtOn(F, v) ∀v`** — and NOTHING else. No `minAdm`, no `Mval`,
no `rankProfile`, no realizer identity. (FACT, `what_collapse_needs.py`.)

**The circularity, named.** "Deepest realizes `minAdm`" (i.e. `rlctAtOn(F, deepest) = ½·minAdm`) IS true
for general M (Aoyagi/LR: the deepest parameter point's maximal-rank-drop profile has local RLCT equal
to the full-cone min, binding divisor the min-`T`, NOT `T=0`). BUT this equality **IS the headline**.
Using it inside #11 would cite `rlct(deepest)=½·minAdm` to prove the box-collapse that proves
`rlct(deepest)=½·minAdm` — circular — and it exceeds the only-S2 cite budget. So it must be kept OUT of
#11; it is the CONCLUSION the edifice produces, not an input. There is no "fourth cited hyp" to add.

**The honest #11 statement (final).**
> `(F homogeneous) → (∀v in fibre, rlctAtOn F deepest ≤ rlctAtOn F v) → (∀ c' < rlctAtOn F deepest,
> IntegrableOn |F|^{−c'} Vz)`.

Inputs: (a) the ordering `deepest_le_of_homogeneous_core` (PROVEN, value-free, homogeneity+lsc, NOT
Aoyagi); (b) compactness of `Vz ∩ {F=0}`; (c) the `rlctAtOn`-def down-set extractor. The genuinely-new
PROVED content is the finite-subcover assembly (b)+(c). The realizer/`minAdm` question lives entirely on
the headline-VALUE side (the spine `lambdaCore = ½·minAdm` + the `y₀`-divisor `mk/2`), reached by the
value-free recursion, never through this bridge.

**Net.** #11 carries NO `Mval`/`Adm`/`rankProfile`/Kostant/`rlct=½mval`/deepest-realizes-minAdm — none
of it. The exponent-vector route (Addenda 2's reduction) is retained ONLY as the decorrelated soundness
cross-check that the ordering is correct for all M. This is the final, honest, circularity-free shape;
verdict (a) unchanged throughout.

---

## ADDENDUM 5 — the #11 box→point bridge: PROVED core vs the open glue + an L2 docstring landmine

(Prepping the general-M consult, against the actual `S1NodeCoverBridge.BoxThresholdBridge` interface.
Includes a SELF-CORRECTION of Addenda 1-4's implicit "deepest_le covers the box directly" reading.
Scripts: `check_core_homog.py`, `correct_collapse.py`, `bridge_K_resolve.py`.)

**The interface (fm3, `S1NodeCoverBridge.lean`).** `BoxThresholdBridge K := ∀ c' < rlctAtOn K 0,
∀ bounded measurable Vz, |K|^{−c'} integrable on Vz`. `chart_pullback_lt_top_of_bridge` (PROVEN)
discharges the GE leg's `hKint` FROM it. So #11 = prove `BoxThresholdBridge` at the right `K`.

**SELF-CORRECTION.** Addenda 1-4 spoke of "the ordering `rlctAtOn(F,deepest) ≤ rlctAtOn(F,v)` via
`deepest_le_of_homogeneous_core`" as if it applied to the chart core. It does NOT apply to `K = core`:
`core = ‖Â·B‖²` with `Â = [[1,u],[v,W]]` is NOT homogeneous in the ratio coords (the unit pivot `(0,0)=1`
is unscaled — verified `check_core_homog.py`). `deepest_le` is for the HOMOGENEOUS raw loss `dlnLoss N 0`
(degree `2L`) on its parameter space. So the box-collapse is NOT a one-node homogeneity argument on the
chart core.

**The PROVED core of #11 (clean, now).** `BoxThresholdBridge (dlnLoss N 0)` for the HOMOGENEOUS raw
loss IS provable: `deepest_le_of_homogeneous_core` gives `rlctAtOn(dlnLoss N 0, 0) ≤ rlctAtOn(dlnLoss N
0, w)` for ALL `w` (global homogeneity ray), then a finite-subcover of the compact `Vz ∩ {dlnLoss=0}`
(each `w` has a sub-threshold-integrable nbhd since `c' < rlctAtOn(·,0) ≤ rlctAtOn(·,w)`; compactness ⟹
finite subcover ⟹ box lintegral finite). Value-free, cite-free, dimension-uniform. **This is #11's
provable deliverable; prove it at `K = dlnLoss N 0`.**

**The open glue.** The GE leg's `chart_pullback` feeds `K = core` (the non-homogeneous chart function),
not `dlnLoss N 0`. The lift `hKint(core) ⟸ hKint(child)` needs: `core ≍ Φ = ∑Erow² + dlnLoss(child)`
UNIFORMLY on the box `Vz` (not just locally near `0`) + Morse-additivity + `BoxThresholdBridge(dlnLoss
child)`. Whether the R1 single-step squeeze is BOX-UNIFORM (the proven `IsSchurStraightenSqueeze` is
LOCAL, `∃ U ∈ nhds 0`) is the load-bearing open check. ALTERNATIVELY (cleaner): re-point `chart_pullback`'s
`K` to the child loss directly via the reduced-transport (which already supplies `G² = dlnLoss(child)`),
making the lift unnecessary — worth checking on the GE producer.

**L2 DOCSTRING LANDMINE (flagged to controller).** `DeepestGaugeBlocks.fullProduct_core_split`'s
docstring asserts: *"`R − ∏S_s ∈ ideal(E)`, so the two squeeze the same."* This is the **REFUTED g156
claim** (the ε=1/7 counterexample: `E=0`, `∏S_s=0`, `R=−ε⁴≠0` ⟹ `R−∏S_s ∉ ideal(E)`). The Lean LEMMA
`core_comparability_squeeze` itself is SOUND (it compares `∑E²+‖P₁₁‖²` to `∑E²+‖R‖²` with `R = P₁₁−leak`,
`leak ∈ ideal(E)` — no `∏S_s`); only the DOCSTRING's parenthetical `∏S_s` reconciliation is false. Since
this is L2 (redundant for the headline) the soundness impact is nil, but the docstring states a refuted
fact as true — a conceptual-slop item for the controller's bedrock call (correct the docstring, or
confine the L2 lemma so the false claim is not cited by the R1 lift).

**Verdict (a) unchanged.** The headline is sound; #11's provable core (`BoxThresholdBridge` at the
homogeneous raw loss) is clean and value-free; the open glue (box-uniform R1 single-step squeeze, or
re-pointing `K` to the child loss) is the precise general-M remaining piece — and must NOT route through
the L2 `R`-core squeeze carrying the refuted comparability.

---

## ADDENDUM 6 — cone-vertex/stratification reconciliation: the ordering CLOSES (cite-free), box-localization is a non-issue

(deriv-finish's cone-vertex resolution of the `T=0` subtlety, cross-checked against the stratification
cert. This CLOSES the "open glue" of Addendum 5's ordering leg. Script: `confirm_cone_vertex.py`.)

**The two routes to the ordering `rlctAtOn(F,0) ≤ rlctAtOn(F,p) ∀p` AGREE (independent derivations).**
- **Cone-vertex / homogeneity (deriv-finish, the route #11 USES):** `F = dlnLoss N 0` is homogeneous
  degree `2L`, so `rlctAtOn` is constant along the ray `t·p` (ray-scaling-invariance) and lsc at the
  limit `0`, giving `rlctAtOn(F,0) ≤ rlctAtOn(F,p)` for EVERY `p`. The all-zero point is the CONE VERTEX
  of `{∏A=0}` (in the closure of every zero-product stratum); homogeneity makes its germ the inf. NO
  `Mval`/Kostant/resolution — in-engine, cite-free, ~30 LoC over the proven `deepest_le_of_homogeneous_core`.
- **Stratification (Addendum 2, the decorrelated CROSS-CHECK):** per-stratum `rlct = ½·mval ≥ ½·minAdm`
  = the vertex value (CITED). Same inequality, via the per-stratum values.

They never disagree: the homogeneity route gives `≤` for every `p` with NO stratum structure; the
stratification route gives the same with the per-stratum values. The cone-vertex IS the rigorous "vertex
sees the min", and it dissolves the `T=0`-≠-minimizer subtlety (the vertex's RLCT is the min as a LIMIT,
not as the value of the `T=0` stratum). The homogeneity route is strictly better for #11; the
stratification stays as the independent confirmation that the ordering holds for all M.

**Box-localization is a NON-ISSUE (confirmed).** `rlctAtOn(F, w*)` is a GERM — sup over `c'` with
`|F|^{−c'}` integrable on SOME nbhd of `w*` — intrinsic to `w*`, independent of any box `Vz`. The box
enters ONLY in the finite-subcover collapse, never in a `rlctAtOn` value: the ordering is point-vs-point
and global (homogeneity everywhere), so it covers every `p ∈ Vz` and its closure trivially; the collapse
uses `c' < rlctAtOn(F,0) ≤ rlctAtOn(F,p)` ⟹ each `p` has a sub-threshold-integrable nbhd, `Vz∩{F=0}`
compact ⟹ finite subcover, plus `{F≠0}∩Vz` bounded-integrand. The box supplies COMPACTNESS only.
Restricting to `Vz` does not change which strata are "present" in any way that matters.

**Caveat carried (Addendum 5):** the homogeneity ordering is for the RAW loss `dlnLoss N 0`, NOT the
chart `core` (non-homogeneous). So `BoxThresholdBridge` must be instantiated at `K = dlnLoss N 0` (the
raw / child loss). If the GE leg's `chart_pullback` feeds `K = core`, re-point it to the child loss via
the reduced-transport (`G² = dlnLoss(child)`, cleanest) — then the homogeneity ordering applies and the
collapse closes.

**#11 final shape (cite-free, mostly-proved).** ORDERING leg = PROVEN (`deepest_le_of_homogeneous_core`
+ ~30-LoC homogeneity, deriv-finish's cone-vertex route). BOX-COLLAPSE leg = the finite-subcover
(`IsCompact (Vz∩{F=0})` + glue local-integrabilities into the `Vz` lintegral) — the only genuinely-new
content. No `Mval`/Kostant/resolution/Aoyagi cite anywhere in #11. Verdict (a) stands; the headline's R1
completion now hangs only on this subcover assembly + the value-side telescope (#12).

---

## ADDENDUM 7 — resolving the Addendum-5 squeeze caution: the uniform-on-box squeeze IS the sound R1 single-step

(Closing note. Verified against `GeneralR1Recursion.lean:575+` on `fm/deriv-frame-resume-cont`.)

Addendum 5 cautioned that the only `*_squeeze_unif` lemma I had then found (`schur_node_squeeze_unif`
in `DeepestGaugeBlocks`, the L2 file) squeezed against the full-product `‖R‖²` core carrying the
refuted `R−∏S_s ∈ ideal(E)` docstring — so I flagged the R1 lift must NOT route through it. RESOLVED:
there are TWO `schur_node_squeeze_unif` family lemmas. The R1 one (`GeneralR1Recursion.lean`, the one
ROUTE A actually uses) squeezes `Φ = ∑Erow² + ∑‖SΓ‖²` against `F = ∑Erow² + ∑(b·Erow+SΓ)²` with `SΓ`
an ABSTRACT `M→n→ℝ` and the sole hypothesis `∑b² ≤ T²` — and `schur_straighten_squeeze_exists` binds
`∑‖SΓ‖² = G² = dlnLoss(S.red) 0` (`hredCore` + the `hnode` presentation), the GENUINE single-step
reduced-chain child. So it is the SOUND R1 single-step object, NOT the L2 `‖R‖²` full-product core. The
refuted comparability lives only in the disjoint L2 `fullProduct_core_split` (docstring corrected per the
controller's bedrock ruling, #13); the R1 ROUTE A path never touches it. `hnode` is an explicit interface
hypothesis (no plumbing smuggled). So ROUTE A's uniform-on-box squeeze closes value-free, and the R1
recursion is sound and comparability-free — consistent with verdict (a). This closes my Addendum-5
caution.
