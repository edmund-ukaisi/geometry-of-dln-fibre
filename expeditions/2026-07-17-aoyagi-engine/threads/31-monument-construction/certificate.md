# Certificate — Aoyagi's Cases-1&2 recursion inhabits the v4.2 `Resolution` record at full generality

Pen-and-paper `pnp-monument` (thread 31, LANE 5), 2026-07-21. Target: the v4.2 Lean record at commit
`093475db3` — `Core/Aoyagi/ProductResolution.lean` (`Chart` / `Resolution`) and
`DLN/Aoyagi/LearningCoefficient.lean` (`exists_coreResolution`, incl. `he_lin`). All instance numbers
exact (recomputed here + threads 27/28 Gröbner). Decorrelated Codex `xhigh` consult ran on the
construction BEFORE this verdict (`./codex/construction-{prompt,answer}.md`); it converged on every
load-bearing point and sharpened three, all folded in below.

**VERDICT: YES-with-gaps(named).** Aoyagi's Cases-1&2 recursion produces, for the concrete flattened
core family `coreGen d e` (with `e` a LINEAR measure-preserving origin-fixing homeomorphic flatten), an
object satisfying every `Chart` / `Resolution` field at full generality (all `L`, all positive width
vectors, monotone and non-monotone). The derivations are structural inductions on the recursion, not
instance checks. **Two residuals remain, both detail-at-scale (NOT new-math frontiers), each already the
named residual of a v4.2 frontier leaf:** (I) the finite compact-atlas a.e.-cover bookkeeping
(`= rlctAt_sumSqFam_eq_iInf_charts`'s named residual); (II) the `hattain` minimiser-realisation
(`= exists_coreResolution`'s `∃`-obligation; banked as compass `minAdm ∈ P`). Two paper defects are
recorded that the ideal-route record **structurally avoids** (§d).

The single load-bearing soundness fact under everything (threads 27/28, re-confirmed): the pulled-back
loss is `Σ(∏C∘g)² = Σbᵢ²·(analytic factor ≠ 1)` — the resolution is ideal-preserving but NOT
Frobenius-preserving — so the RLCT equality is transported by the ideal identity (`hideal_fwd`/`_bwd`
+ weighted Object A), never by a norm/change-of-variables identity. The record routes through
`RegionRepresents` + `wrlctAt_sumSqFam_eq_of_germ_eq`, which is exactly this and only this. The record
is faithful to the mechanism.

---

## (a) The atlas construction — the recursion as an explicit finite chart family

**Objects.** `F = coreGen d e : Fin (d_L·d_0) → (Fin D → ℝ) → ℝ`, `D = flatDim d = Σᵢ d_{i+1}d_i`,
`Fₖ(u) = (∏_{s} C^{(s)})_{ij}(e u)` — the entries of the matrix product `∏C` in the flat coordinates
`u`, at the deepest point `x₀ = 0` (all `C^{(s)} = 0`; `e 0 = 0`). Since `e` is LINEAR (`he_lin`), each
`Fₖ` is a polynomial in `u`; hence analytic, and `Σ Fₖ² = ‖∏C‖²_F ∘ e`. (The `he_lin` guard is
load-bearing and sound: a non-linear origin-fixing homeomorphism, e.g. `e u = u|u|`, makes `coreGen`
non-analytic and no analytic-`g` chart can resolve it — the record rejects it, correctly.) At `x₀=0`
the reduced widths equal the full widths `M^{(s)} = d_{s-1}` (no regular rank-`r` block to peel at
`r=0`), so the resolution is of `⟨∏C⟩`, widths `d`, at the origin.

**The recursion is a finite rooted tree.** State `(S, J, D_J)`, `0 ≤ S ≤ L`, `0 ≤ J ≤ M(S+1)`, with the
running minimum `M(S) = min{M^{(s)} : 1 ≤ s ≤ S}`. Root: `(0, 0, D_0 = ∏C)`. The maintained ideal
identity (worked.tex:477–480):

    ⟨∏_{s=1}^{L} C^{(s)}⟩ = ⟨ diag(b_1,…,b_{M(S)}) · [[E_J, O],[O, D_J]] · ∏_{s=S+1}^{L} C^{(s)} ⟩,

`D_J` the `(M(S)−J)×(M^{(S+1)}−J)` residual block; the `bᵢ` monomials in the exceptional coordinates
`u_{s,k}` introduced so far, `b_0=1`, `bᵢ = (∏_{t̃_{s,k}=i−1} u_{s,k})·b_{i−1}`.

**One step (worked.tex:499–520).** At `(S,J)` inspect the equal run of the `b`-sequence above `J` and
blow up the corresponding determinantal locus. The blow-up's affine charts are the branch points; we
follow one chart per branch:
- **Case 1** (partial equal block `b_{J+1}=…=b_{J+J₁} ≠ b_{J+J₁+1}`, `J₁ < M(S)−J`): blow up
  `{d_{ij}=0 (J<i≤J+J₁, J<j≤M^{(S+1)}), u_{s,k}=0}`. Splits into **1(1)** (d-block `= u_{s,k}·d'`: set
  `t̃_{s,k}=J`, add `M'_{s,k}=M_{s,k}+J₁(M^{(S+1)}−J)` to that divisor's Jacobian exponent — an inner
  recursion on an existing divisor) and **1(2)** (first row normalised, `u_{s,k}=u_{S,J+1}·u'_{s,k}`:
  introduce `u_{S,J+1}`, regular `Q,P` reduce `D_J″ → [[1,O],[O,D_{J+1}]]`, advance `J`).
- **Case 2** (full block `b_{J+1}=…=b_{M(S)}`): blow up `{d_{ij}=0 (J<i≤M(S), J<j≤M^{(S+1)})}`.
  Introduce `u_{S,J+1}` at threshold `J` (deep layers) with exponent `M'_{S,J+1}=(M(S)−J)(M^{(S+1)}−J)`
  — the codimension of the blown-up residual block, running-min governed. Regular `Q,P` reduce
  `D_J″ → [[1,O],[O,D_{J+1}]]`, advance `J`.
Each step advances `J` (bounded by `M(S+1)`) or increments `S` (bounded by `L+1`), and Case 1(1) is an
inner recursion decrementing a finite divisor count — so the tree is **finite**. Terminal leaves: at
`S=L+1`, `⟨∏C⟩ = ⟨diag(b_1,…,b_{M(L+1)})⟩` and `‖∏C‖² = Σᵢ bᵢ²` (normal crossing).

**The atlas.** `numCharts` = the number of root→leaf paths; each terminal branch is one `Chart`. The
composed `g` per leaf = the composition of the monomial blow-up substitutions along the path (each
affine-chart substitution is `(…,u,v,…) ↦ (…,u,uv,…)`, monomial); the regular transforms `Q,P` enter as
**ideal-generator changes** (Lemma-1 / ideal-invariance), i.e. as the `RegionRepresents` cofactors, not
as coordinate changes. (Equivalent framing: fold `Q,P` into `g`; then `g`'s Jacobian carries the
pivot-determinant unit. Both inhabit the record; the pure-monomial framing below is cleaner and closest
to Aoyagi's Hironaka map.) `g` is polynomial, `g 0 = 0` (each substitution fixes 0).

### The suffix-update invariant — the ∀-general divisibility chain (the structural core)

Iterating the update `bᵢ = (∏_{t̃=i−1} u)·b_{i−1}` gives the **closed form**

    bᵢ = ∏_{ s,k : t̃_{s,k} < i } u_{s,k}          (b_0 = 1).

The index sets `{t̃ < i}` are nested increasing, so `b_1 | b_2 | … | b_M` — the divisibility chain, with
`b_1` the divisibility-minimal generator (`k₀ = 1`). Every step preserves the closed form (verified
per-step, decorrelated-confirmed by Codex):
- **Case 2:** a new `v` born at threshold `J` scales every residual row `i > J`, so it multiplies exactly
  the suffix `b_{J+1},…,b_M`.
- **Case 1(1):** the chosen old divisor `u` has threshold `q = J+J₁`; before, `u` sits in rows `i > q`,
  not in `J < i ≤ q`. Scaling that block by `u` puts one `u` in every row `i > J`; the threshold moves
  `q ↦ J`. Still a suffix (now `i > J`).
- **Case 1(2):** write `u = v·u'`. Rows `J < i ≤ q` (no `u`) gain one `v` from the block scaling; rows
  `i > q` (already one `u`) gain one `v` via `u=vu'` but no block scaling. So `v` occurs once on the
  suffix and nowhere else.
A width drop (non-monotone `d`) truncates the chain at the new running minimum; it cannot create a
non-suffix support. **The chain is threshold-based, and this holds at all `L` / all positive widths.**

Two consequences of the closed form, both load-bearing for the record:
- **`b_1 = ∏_{t̃=0} u` is a nontrivial monomial** (`hbind`): at `(S,J)=(·,0)` the initial equal block
  forces a Case-2 blow-up whose divisor has threshold 0; it stays in `b_1`. Equivalently: at the chart
  origin `(∏C∘g)(0)=(∏C)(0)=0`, so `b_1(0)=0`, so `b_1 ≠ 1`. (Empty-width `d_k=0` is excluded by
  `hpos`; there the core is not singular.)
- **`b_1` is squarefree** (`hunit_mult`): each `u_{s,k}` occurs at most once in each `bᵢ` (membership is
  binary in `t̃`); *repeated* use of a divisor accumulates **Jacobian** exponent (`M_{s,k}`, the `jac`
  field), never *loss* exponent (`bexp`). So `bexp k₀ d ∈ {0,1}`, `= 1` on binding axes.

---

## (b) Per-chart field discharge (each v4.2 field, with its derivation)

For a general terminal branch (leaf), `D = flatDim d`, `M = d_L·d_0`:

| `Chart` field | how the construction provides it |
|---|---|
| `g` | composition of the monomial blow-up substitutions along the leaf path (polynomial). |
| `hg0 : g 0 = x₀` | each substitution `(…,u,uv,…)` fixes 0; `x₀ = 0`. |
| `hg_cont`, `hg_analytic` | `g` polynomial ⟹ continuous + `AnalyticOnNhd ℝ g univ`. |
| `hFmeas` | `Fₖ = coreGen` polynomial ⟹ measurable. |
| `dom` compact `∋ 0`, `nbhd` open `⊇ dom` | `nbhd` = the affine-chart pivot-nonvanishing open (§c); `dom` a compact set inside it whose images cover (the residual, §c). Both `∋ 0`. |
| `excep`, `hexcep_meas`, `hexcep_null`, `hg_inj` | `excep` = the finite union of the contracted coordinate hyperplanes (`{u_{s,k}=0}`); a proper closed subvariety ⟹ measurable, `volume = 0`; each blow-up chart is an iso off its exceptional divisor, so the composite `g` is injective on `nbhd \ excep`. |
| `M'`, `bexp`, `k₀` | `M' = M(L+1)`; `bexp k = ` exponent vector of `bₖ = ∏_{t̃<k} u` (from the closed form); `k₀ = 1` (divisibility-minimal, = `b_1`). |
| `hchain : ∀ k d, bexp k₀ d ≤ bexp k d` | nested supports `{t̃<1} ⊆ {t̃<k}` — the suffix-update invariant (§a). |
| `hbind` | `b_1 = ∏_{t̃=0} u` nontrivial (§a) ⟹ `bindingAxes(bexp k₀) ≠ ∅`. |
| `hunit_mult : bexp k₀ d = 1 on binding axes` | `b_1` squarefree (§a): `bexp k₀ d ∈ {0,1}`. This is Aoyagi's `k_j ≡ 1` (worked.tex:495). |
| `jac : Fin D → ℕ` | `jac(u_{s,k}) = M_{s,k} − 1` (accumulated Jacobian power, worked.tex:492–497); `jac = 0` on residual/free axes. `jac_d + 1 = M_{s,k}` on binding axes. |
| `unit`, `hunit_cont`, `hunit_ne`, `hjac` | pure-monomial `g` ⟹ `|det Dg| = jacWeight jac` with `unit ≡ 1` (`|unit| = 1`), continuous + nonvanishing everywhere ⟹ `hjac` on all `nbhd`. (Folded-`Q,P` framing: `unit` = product of pivot determinants, nonvanishing on `nbhd = {pivots ≠ 0}`.) |
| `hideal_fwd`, `hideal_bwd` (`RegionRepresents`, coeffs `ContinuousOn nbhd`) | the accumulated regular transforms `U,V` (products of the `Q,P`, evaluated at the substituted coords) give `U·(∏C∘g)·V = diag(b)`: **bwd** `diag(b)` entries `= Σ` of `(∏C∘g)` entries with cofactors = entries of `U,V`; **fwd** `(∏C∘g) = U⁻¹·diag(b)·V⁻¹`, cofactors = entries of `U⁻¹,V⁻¹`. All cofactors are rational in the chart coords, regular (continuous) on `nbhd = {pivot dets ≠ 0}`. They MAY vanish (off-diagonal / monomial ratios) — `RegionRepresents` needs only `ContinuousOn`, not nonvanishing (§c, the trap the record avoids). |

`Resolution` fields: `numCharts` = #leaves; `charts` = the leaves; `hne` (≥1 leaf, from `hbind`/
singularity); `U ∈ 𝓝 0` and `hcover : volume(U \ ⋃_c g_c '' dom_c) = 0` — the a.e.-cover (§c).

`Chart.chartMin = inf_{a ∈ bindingAxes(bexp k₀)} (jac a + 1) = min{M_{s,k} : t̃_{s,k}=0 in this chart}`;
`Resolution.divisorMin = min_c chartMin_c = min over ALL terminal divisors of M_{s,k} = ½·(2·rlct_core)`
(worked.tex:537). Object C (`monomialSumSq_two_mul_wrlctAt_eq_min`, under `hchain` + `hunit_mult`) gives
`2·wrlctAt = chartMin` per chart; Object B's atlas-min CoV gives `2·rlctAt = divisorMin`.

---

## (c) The cover, and the min-attainment obligations

### The a.e.-cover (`hcover`) — RESIDUAL (I), detail-at-scale

The iterated blow-up `g : Q → V` is **proper** (Hironaka), so the preimage of a closed ball
`B̄(0,ρ) ⊆ V` is compact and covered by finitely many affine-chart restrictions; the exceptional locus
(image of the contracted divisors) is a proper subvariety, `volume 0`. Hence `U = B(0,ρ)` is a.e.-covered
by finitely many `g_c '' dom_c` with `dom_c` compact — this is `hcover`.

The residual bookkeeping (the concrete `dom ⊆ nbhd`): each affine chart `i` is the **max-pivot sector**
(the locus where the `i`-th minor is the invertible pivot, normalised to 1). There the projective ratios
lie in `[−1,1]` (compact) and the normalised pivot stays nonzero throughout the sector, so `nbhd_i =
{pivot_i ≠ 0}` carries the dom-wide certificates and contains a compact `dom_i` whose images cover the
sector. Assembling the finite tree of such sectors into a single finite compact atlas with an a.e.-cover
is **standard detail-at-scale (proper-map partition), not new resolution mathematics** — but it is a
genuine obligation if the construction only asserts "the pivot is nonzero *near* the chart origin". This
is exactly the named residual of the Lean frontier leaf `rlctAt_sumSqFam_eq_iInf_charts` ("the
pushforward integrability and the partition of the neighbourhood over the atlas' compact domains").
Decorrelated Codex flagged this as the likeliest remaining gap and agrees it is detail-at-scale.

**The trap the record avoids (Codex, load-bearing).** If `hideal_fwd`/`_bwd` required the *cofactors* to
be **nonvanishing**, the record would be UNSOUND: the ordinary blow-up `g(u,v)=(u,uv)` of `⟨x,y⟩` has
`y∘g = v·u`, whose only continuous cofactor `a` with `uv = a·u` is `a = v`, so `a(0)=0` — nonvanishing is
impossible. The v4.2 record requires cofactors only `ContinuousOn nbhd` and reserves nonvanishing for the
Jacobian `unit` alone (`hunit_ne`). The construction inhabits it precisely under this correct split.

### Min-attainment (`exists_coreResolution`'s two `∧`-conjuncts)

The obligations quantify over `a ∈ bindingAxes((charts c).bexp k₀)` — and `bindingAxes(bexp k₀) =
support(b_1) = {u_{s,k} : t̃_{s,k}=0}` = exactly the **terminal divisors**. So the record's quantifier
*already* implements the paper's `t̃=0` read-off restriction (worked.tex:537); the non-binding `t̃>0`
divisors (whose exponents can be `< qipMin`) are correctly excluded (they don't divide `b_1 = k₀`). This
is a structural fidelity point: an unrestricted `∀ k` would be FALSE (companion fact,
`verify-case2-rawwidth-defect.md`); the record's `bindingAxes(bexp k₀)` is the right filter.

**`hlb` (no undershoot): `∀ c, ∀ a ∈ bindingAxes, qipMin ≤ jac a + 1`.** For a terminal divisor,
`jac a + 1 = M_{s,k}`, the accumulated exponent. Its running-min physical profile
`t_i = r_{i+1} (i<S), = J (i≥S)` (`r_s = min(M^{(1)},…,M^{(s)})`) is weakly-decreasing and within the
running-min bounds, hence **admissible**, and its envelope-prefix `Mval`-terms vanish
(`(M^{(1)}−r_2)(M^{(2)}−r_2)=0`, `(r_j−r_{j+1})(M^{(j+1)}−r_{j+1})=0`), leaving `Mval(t) =
(r_S−J)(M^{(S+1)}−J)` = the Case-2 exponent exactly; the Case-1 tail-lowering `q=J+J₁ → J` changes `Mval`
by `J₁(M^{(S+1)}−J)` = Aoyagi's accumulated update. So **every terminal exponent = `Mval(t)` for an
admissible `t`**, hence `≥ min_{admissible} Mval = qipMin` (Object D: `cCodim_eq_qipMin`, banked). ✓
(Derivation reproduced independently by Codex.)

**`hattain` (`∃ c, ∃ a ∈ bindingAxes, jac a + 1 = qipMin`) — RESIDUAL (II), detail-at-scale.** This does
NOT follow from `hlb`; it needs the minimiser to be **realised** as a terminal divisor. Not every
admissible profile is realised (e.g. at widths `(3,3,4,2,3)` the profiles `(2,2,2,0)`, `(3,2,2,0)` are
stranded) — so the paper's implicit "resolution realises every admissible profile" is false (compass F5
realization ledger). But **every minimiser IS realised**: an admissible profile with a forbidden descent
from a saturated running minimum (a non-envelope prefix) can be replaced by its running-min envelope, which
contributes 0 while the original prefix contributes strictly `> 0` (boundary/suffix unchanged) — strictly
decreasing `Mval`. So a non-envelope-clearable profile cannot minimise; the minimiser is clearable, and a
clearable profile is reached by steering the Case-1(2) descents. This "exponent-ledger + steering
induction" is detail-at-scale (Codex agrees), and is exactly the compass's proved `minAdm ∈ P`. The
attaining chart/axis: the leaf whose steering reaches the QIP-minimising envelope profile `t*`, on the
`t̃=0` axis carrying `M_{s,k} = Mval(t*) = qipMin`.

---

## (d) Case-2 re-adjudication (standing F5 condition)

**Method note (honest).** No PDF renderer / text-extractor is available in this worktree (no
poppler-utils, no python PDF lib), so I could not read the p.20 page IMAGE directly. The re-adjudication
below rests on (i) the transcribed formulas in `worked.tex` (which carry BOTH the exponent rule and the
label rule and flag the conflict), (ii) the v4.2 record's field structure (read directly), and (iii)
thread-27's exact non-monotone recursion + `verify-case2-rawwidth-defect.md`. The load-bearing conclusion
is a STRUCTURAL fact about the target record, independent of the page image.

**The defect (p.20).** Case 2 sets the divisor's head-reset **label** as `t^{(i)} := M^{(i+1)}` (RAW
width) while the same step's **exponent** uses `(M(S)−J)(M^{(S+1)}−J)` with `M(S)` the RUNNING minimum.
At a non-monotone width (interior increase, `M^{(i+1)} > M(i+1)`) the label and exponent conflict. Minimal
instance `(2,2,3,2)` (recomputed here): the raw label `(2,3,0)` gives `Mval = 6`, but the physical
accumulated (running-min) exponent is `4 = Mval(2,2,0)`, and `(2,3,0) ∉ Adm` (weak-decrease fails 2<3).

**Re-adjudication — the running-min form is what the construction needs, and the ideal-route record
structurally cannot carry the defect.** The `Chart` record has NO rank-profile "label" field — only
`bexp` (monomial support, threshold-based) and `jac` (accumulated Jacobian exponent per axis). The
`hlb`/`hattain` read `jac + 1` (the physical accumulated exponent) on `bindingAxes(bexp k₀)`. The
accumulation formula (worked.tex:516,533) already uses the running minimum `M(S)`, not the raw `M^{(S)}`.
So the defective raw-width label has no representation in the record, and the quantities the record reads
are running-min-governed by construction. For `(2,2,3,2)`: the record stores `jac + 1 = 4` on that
divisor; since `qipMin(2,2,3,2) = 3 < 4`, the divisor is **non-binding** — it neither undershoots
(`hlb`: 4 ≥ 3 ✓) nor is it the attaining axis. The fork **dissolves** (thread-27's verdict, confirmed):
the running-min governs, no label primitive exists in the ideal route, and the defect sits on a
non-binding divisor. **No discrepancy surfaced; the record is faithful.**

**Second recorded defect (Codex-found, does not affect the record).** Aoyagi's stronger claim that the
carried `T`-profiles are totally comparable is FALSE: at widths `(2,2,1,1)` the profiles `(1,1,1)` and
`(2,1,0)` are componentwise-incomparable (`Mval = 1` for both, recomputed). This does not touch the
record: `hchain` is a divisibility chain on the **b-monomials** (`bexp`, threshold-based), which stays a
chain (§a); the record stores no profiles, so profile-incomparability has no representation. Recorded so
the truth is not re-derived.

---

## (e) Instance cross-checks (kill-set adequacy: 27/28 reproduced)

The general construction specialises correctly to every verified instance (`Mval` recomputed exactly
here from worked.tex:533; matches the certificates):

| instance | binding profile | `Mval` = `2·rlct` = `qipMin` | rlct | `b_1` = `bexp k₀` | binding axes |
|---|---|---|---|---|---|
| (3,3,4) | (1,0) | 8 (of {9,8,9,12}) | 4 | `E` | {E}, jac_E+1=8 |
| (4,4,4) | (2,0) | 12 (of {16,13,12,13,16}) | 6 | `E` | {E}, jac_E+1=12 |
| (3,3,2,2) | (2,1,0) | 4 | 2 | `vz`-shared | binder z, +1=4 |
| (3,3,3,2,2) | (2,2,1,0) | 4 | 2 | `wy` (2 divisors, diff depths) | {w,y}: jac_w+1=6, jac_y+1=4 (y attains) |

- **(3,3,4)/(4,4,4):** single joined divisor `E` (corner blow-up), `b_1 = E` principal, one binding axis;
  `chartMin = jac_E+1 = 8` resp. `12`. Matches thread 27 (`E⁷`, loss `E²·unit`, rlct 4) and thread 28
  (`E¹¹`, rlct 6).
- **(3,3,3,2,2):** `b_1 = wy` — a PRODUCT of two divisors at different depths, `bexp k₀` supported on
  `{w,y}` (both exponent 1, squarefree ✓ `hunit_mult`), `bindingAxes` has TWO elements, `chartMin =
  min(6,4) = 4` attained on `y` (`hattain` picks the y-axis). This exercises the multi-binding-axis
  `inf'` shape of `chartMin` — the record accommodates it. Matches thread 28 (`⟨wy⟩` principal, rlct 2).
- **(2,2,3,2):** the defect instance — physical `jac+1 = 4` on the mis-labelled divisor, `qipMin = 3`, so
  non-binding; `hlb` holds (§d). Matches the ledger.

No mismatch. Any mismatch would have indicted the general construction; none appears.

---

## (f) Honest gaps (named; the formaliser decomposes the `exists_coreResolution` discharge against these)

The construction inhabits every `Chart` / `Resolution` / `exists_coreResolution` field at full generality
**modulo** two residuals, both detail-at-scale (standard mathematics, decomposable proof-engineering — NOT
new-math frontiers) and each already the named residual of a v4.2 frontier leaf:

1. **RESIDUAL (I) — the finite compact-atlas a.e.-cover** (`Resolution.hcover` / the CoV split in
   `rlctAt_sumSqFam_eq_iInf_charts`). Existence is Hironaka properness; the explicit finite partition into
   max-pivot-sector compact `dom ⊆ nbhd` with dom-wide certificates + an a.e.-cover is the bookkeeping.
   The far-region continuity is handled by the max-pivot-sector structure (ratios in `[−1,1]`, normalised
   pivot ≠ 0 on the sector), so it is NOT an obstruction — but the assembly over the recursion tree is a
   genuine missing lemma if only germ-at-origin data is on hand. Detail-at-scale.

2. **RESIDUAL (II) — the `hattain` minimiser-realisation** (`exists_coreResolution`'s `∃`-conjunct;
   banked as compass `minAdm ∈ P`). `hlb` (no undershoot) is derived at full generality (§c). `hattain`
   needs the "minimisers are envelope-clearable, hence realised by steering the Case-1(2) descents"
   argument (§c) — detail-at-scale (exponent ledger + steering induction), Object-D-adjacent.

Inherited (not this thread's, but load-bearing for the payoff, per threads 27/28 and the record):
- **Object A** (`wrlctAt_sumSqFam_eq_of_germ_eq`, two-sided ideal-invariance) — the category-NEW workhorse
  the record consumes; a Mathlib-absent BUILD, not a monument. The Frobenius-non-preservation makes it
  strictly necessary (the norm route is category-dead, F1).
- **Object C** (`monomialSumSq_two_mul_wrlctAt_eq_min`, the S2 boxed rule for a single normal-crossing
  monomial × unit under the chain) — the one analytic input the method permits; a `@[blueprint]` leaf.
- **The reduction** (`coreReduction`, `exists_flatten`) — bookkeeping (Thm 4 deepest-point + linear
  measure-preserving flatten + ℝ≥0∞→ℝ carrier bridge).

Everything else in `Chart` / `Resolution` — `g` analytic with `g 0 = 0`; `dom`/`nbhd`/`excep` null +
a.e.-injectivity; `bexp`/`k₀`/`hchain`/`hbind`/`hunit_mult` (the divisibility chain + squarefree `b_1`);
`jac`/`unit`/`hjac` (Jacobian monomial × unit ≡ 1); `hideal_fwd`/`hideal_bwd` (the unimodular `U,V`
cofactors, `ContinuousOn`); `hlb` — is DERIVED at full generality by the structural inductions in §a–§c,
faithful to Aoyagi's Cases 1&2. **Verdict: YES-with-gaps(named).**

## Most likely thing to break it / next construction

The two residuals are the load: (I) if the formaliser cannot realise the compact-atlas partition from the
germ-level chart data without a properness lemma Mathlib lacks, RESIDUAL (I) is heavier than "detail" — it
would need a Hironaka-properness interface (a cite-or-build call for the controller). (II) is safer (a
finite exponent-ledger induction). Next construction if (II) is contested: a Lean-checkable statement of
"every QIP minimiser is a running-min-envelope profile" (the strict envelope-replacement inequality),
which discharges `hattain` from Object D directly. The single most likely error, per decorrelated Codex,
would have been mis-requiring nonvanishing ideal-cofactors — the record does not, so that risk is closed.
