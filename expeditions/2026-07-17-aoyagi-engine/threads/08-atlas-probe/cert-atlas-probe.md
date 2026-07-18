# Cert — Atlas-closure probe (pen-and-paper thread 08, DECORRELATED R2 gate)

*Seat: `pen-and-paper` (pnp08), commissioned by council #3 as the **decorrelated** atlas-closure
probe — deliberately independent of the construction seat (architect-t02). Worked from the Aoyagi
2023 **page images** p.14–22 (every formula pinned below) + exact `sympy`/rational algebra; the Lean
engine modules were **not** read. One decorrelated Codex consult fired
(`codex/atlas-probe-{prompt,answer}.md`, gpt-5.x `xhigh`, hypothesis withheld). Batteries under
`battery/`, all exit-0, integer/rational only (no float, no Monte-Carlo).*

**Register key:** [OBS] source-pinned fact; [CERT] exact-verified here; [SCOPE] scoped/what-checked;
[SPEC] plausible-no-proof; [Q] open.

---

## Page-pins (the load-bearing transcriptions, read from PAGE IMAGES)

Verified directly against the images (the flagged "third page-reading surface" — the per-case
`T`-settings — is pinned here):

- **Init (p.14):** `t^(s)_{S,k}=M^{(s+1)}`, `t̃_{S,k}=M(1)`, `M_{S,k}=0`. `M(S)=min{M^{(s)}:s≤S}`.
  **Def 4 (p.14):** `T≤T'` iff `t_1≤t'_1,…,t_L≤t'_L` (componentwise). Total-comparability invariant
  `T_{s,k}≤T_{s',k'} or ≥` (p.15).
- **Divisibility chain (p.15):** `b_0=1`, `b_i=(∏_{t̃_{s,k}=i-1} u_{s,k})·b_{i-1}`. Jacobian power of
  `u_{s,k}` is `M_{s,k}-1`.
- **Case-1 tie-break (p.15):** run `b_{J+1}=…=b_{J+J₁}≠b_{J+J₁+1}` (i.e. `{t̃=i}=∅` for
  `i=J+1..J+J₁-1`); **fix `u_{s,k}` with `t̃_{s,k}=J+J₁` AND `T_{s,k}≤T_{s',k'}` for all `t̃_{s',k'}=J+J₁`**
  — a full-vector `≤` (Def 4).
- **Case 1(1) (p.16):** mutate the fixed `u_{s,k}`: `t^(S)=…=t^(L):=J` (head `t^(1..S-1)` **unchanged**);
  `M'_{s,k}=M_{s,k}+J₁(M^{(S+1)}-J)`; does **not** advance `J`; decrements `#{u:t̃=J+J₁}` by one.
- **Case 1(2) (p.17):** new `u_{S,J+1}`: `t^(i):=t^(i)_{s,k}` for `i<S` (**INHERITED** from the fixed
  parent), `t^(S)=…=t^(L):=J`; `M'_{S,J+1}=M_{s,k}+J₁(M^{(S+1)}-J)`; advances `J` (or `S`).
- **Case 2 (p.20):** new `u_{S,J+1}`: `t^(i):=M^{(i+1)}` for `i<S` (**RESET** to widths, not inherited),
  `t^(S)=…=t^(L):=J`; `M'_{S,J+1}=(M(S)-J)(M^{(S+1)}-J)`; advances `J` by one per step (p.21) (or `S`).
- **Read-off (p.22):** `λ_core = ½·min{M_{s,k} : t̃_{s,k}=0}`,
  `M_{s,k}=(M^{(1)}-t^{(1)})(M^{(2)}-t^{(1)})+∑_{j=2}^{L}(t^{(j-1)}-t^{(j)})(M^{(j+1)}-t^{(j)})`.

**Both L=2 instances are RRR cores** (three widths). PDF page numbers = paper page numbers (verified).

---

## Verdict 1 — ATLAS CLOSURE / no-undershoot  (direction: OBSTRUCTION; empty hunt = the evidence)

**Computation.** Five decorrelated legs at `M=(2,2,2)` then `(3,3,4)`
(`battery/atlas-value-undershoot.py`, `codim-stratum-check.py`, reused
`map/battery/g-coverage-sharing-killcond.py`, `g-coupled-binding-334.py`, + the Codex tree replay).

**Exact result.**
- **Value.** min over admissible nested profiles `t` (`t^{(L)}=0`) of `Mval(t)` **= minAdm**, achieved
  at `t=(1,0)`:
  - `(2,2,2)`: profiles `{(0,0),(1,0),(2,0)}`, `Mval={4,3,4}`, min `3=minAdm`, `λ_core=3/2`.
  - `(3,3,4)`: profiles `{(0,0),(1,0),(2,0),(3,0)}`, `Mval={9,8,9,12}`, min `8=minAdm`, `λ_core=4`.
  The minAdm recursion **IS** the paper's own `min_t Mval` (`[CERT]`, `atlas-value-undershoot.py`),
  and the ground-truth anchors match (`(2,2,2)→3/2`, `(3,3,4)→4`, `(2,1,2)→1`, `(1,1,3)→½`).
- **No undershoot — hunt came back EMPTY on all five legs:**
  1. `[CERT]` every admissible-profile exponent `Mval(t) ≥ minAdm` (min *is* minAdm; nothing below).
  2. `[CERT]` **independent dimension count**: `Mval(t) = exact codim{rank C^{(1)}=t^{(1)} ∧ C^{(1)}C^{(2)}=0}`
     `= (M^1-t^1)(M^2-t^1)+t^1 M^3` (elementary; `codim-stratum-check.py`). min codim = minAdm; no
     stratum below. (This is a VALUE cross-check; the identity `rlct=½·codim` is **not** invoked.)
  3. `[CERT]` **coordinate-weight (toric) valuation LP**: best ratio `(∑w)/ord_w(J)=M^{(2)}·min(M^1,M^3)`
     `= 4` for `(2,2,2)`, `= 9` for `(3,3,4)`. Both **exceed** `minAdm` (3, 8) → no toric undershoot,
     **and are loose** (never reach minAdm). ⇒ **the binding divisor is a genuine rank blow-up, not a
     coordinate monomial** — coverage is intrinsically **non-toric** (a Newton-polytope/toric argument
     cannot prove R2). Corroborated by `g-coupled-binding-334` (corank-≤1-restricted min `9>8`).
  4. `[CERT]` the **actual** undershoot mechanism — mis-tracked sharing — reproduces on the banked
     kill-cond: conflating separate supports gives `½<1` at `(2,2,1)`, independentising shared ones
     gives `3<4` at `(3,3,4)`. So an undershoot appears **only under mis-tracking**; the `diag(b)`/`t̃`
     tracking is load-bearing for the ≥-leg.
  5. `[OBS, Codex]` independent chart-tree replay: same atlas, **no `t̃=0` divisor below minAdm**. It
     flags a genuine subtlety — small-exponent **positive-`t̃`** divisors exist (`(2,1):M=1` at
     `(2,2,2)`, `(2,2):M=1` at `(3,3,4)`) but do **NOT** undershoot: a `t̃=q>0` coordinate first divides
     `b_{q+1}`, not `b_1`, so `∑b_i²` has order 0 along it — `M/2` is inapplicable. Aoyagi's `t̃=0`
     restriction (p.22) is exactly what fences these off; correct `t̃`-tracking prevents a spurious
     undershoot here too.

**Scoped-claim wording.** `[CERT]` *At `M=(2,2,2)` and `(3,3,4)`, the terminal `t̃=0` divisor
exponents equal the rank-stratum codimensions, their minimum equals `minAdm` (3, 8), and no admissible
profile, coordinate-monomial valuation, or correctly-tracked divisor gives a ratio below `½·minAdm`; a
strictly-below ratio arises only under a sharing MIS-track.* `[SCOPE]` the hunt is at the
profile + codim + coordinate-weight + mis-track + Codex-tree level — **not** a proof of the proper
chart-image cover. **Coverage-as-a-theorem is NOT discharged** and remains the genuine R2 obligation:
`[OBS, Codex]` it must instantiate the **full residual-`d` pivot-chart cover**, not the representative
"corner" chart — a fixed-corner-only reading has an explicit gap (`C^{(1)}=[[0,ε],[0,0]], C^{(2)}=0`
misses the `c₁₁`-pivot chart). The rank strata do cover `{∏C=0}` tautologically and the binding
stratum `(1,0)` is admissible and emitted, so **attainment** holds; the open content is the exhaustive
proper cover, which — leg 3 — is provably non-toric.

**→ 1(b): NO undershoot in the faithful construction (five empty legs). The R2 hard part is the
proper coverage/cover-image theorem, confirmed genuinely non-toric.**

---

## Verdict 2 — FULL-`T` NECESSITY  (adjudicates council verdict 3a)

**Computation.** Search for a Case-1 node with ≥2 divisors at the selected level `t̃=J+J₁` carrying
**different** full `T` (then Def-4 `≤` must select; `t̃=min` is equal for both). Rule-level + Codex
tree (`tiebreak-necessity.py`, `codex/atlas-probe-answer.md`).

**Exact result.**
- `[SCOPE]` **At `(2,2,2)` and `(3,3,4)`: NO genuine full-`T` tie-break fires** — every Case-1 selected
  level has a **sole** candidate (Codex's tree; consistent with the rule-level fact that at `L=2` the
  head has length ≤1 and the two head-values never co-occupy a *live* Case-1 level before the layer
  ends). Instance I *terminates* with `(1,1)` and `(2,1)` both at `t̃=1` — comparable but distinct —
  they simply never become co-competing candidates.
- `[CERT]` **Full-`T` necessity is nonetheless real and is forced at `L≥3` (first three widths ≥2)**,
  witness `M=(2,2,2,2)`: at node `(S,J,J₁)=(3,0,1)` two divisors sit at `t̃=1` —
  `(1,1,1)` (born `S=1`, keep-rank-1) and `(2,1,1)` (born `S=2` Case-2, head reset to `M^{(2)}=2`,
  tail `=J=1`) — **distinct, comparable `(1,1,1)<(2,1,1)`, same `t̃=1`**. Def-4 selects `(1,1,1)`;
  `t̃` alone (`=1` for both) cannot. (`minAdm(2,2,2,2)=3`, `λ_core=3/2`, a genuine value-3 core.)
- `[CERT]` **Comparability adjudication.** Total comparability forces divisors at a common `t̃` into a
  **chain, NOT into equality** — so the tie-break genuinely reads the full `T`; it is **not**
  `t̃`-decidable. Two mechanisms *tree-independently* read head components `t̃` discards: the Case-1(2)
  **inheritance** (`t^(i):=t^(i)_{parent}`, p.17) and the Def-4 `≤` **comparison** (p.15). This
  confirms fork-7's founding WHY ("the unary invariant cannot pin the parent-referencing merge").

**Scoped-claim wording.** `[CERT]` *The p.15 minimality tie-break is provably NOT reducible to a
`t̃`-only rule: total comparability yields a chain, not equality, and the creation rules (Case-2
head-reset vs Case-1(2)/`S=1` head) produce distinct-but-comparable `T` at a common `t̃`. It is
VACUOUS at `(2,2,2)`/`(3,3,4)` (sole candidates) and FIRES at `(2,2,2,2)`, node `(3,0,1)`, selecting
`(1,1,1)` over `(2,1,1)`.*

**→ 2: necessity witness NOT at the L=2 mandate instances (scoped negative); FORCED at `L≥3`,
witness `(2,2,2,2)`. Council verdict 3a (full-`T` in the State) upheld — but the necessity bites at
`L≥3`, coinciding with the SchurCore depth-≥3 wall (task #7); a corank-2 `L=2` spike does NOT
exercise the tie-break.**

---

## Verdict 3 — FULL-`T` UPDATE-RULE COST  (prices council verdict 3a's cost risk)

**Computation.** Trace the full-`T` update through one Case-1(1) merge + one Case-2 step at `(3,3,4)`
from the page rules (`t-update-trace-334.py`); classify the data-structure operation.

**Exact result.** `[CERT]` every traced record lives on the **fixed** index set `{1,2}`, and each
exponent equals `Mval(T)`:
- **Case 2, `S=1,J=0`:** create `u_(1,1)`; head empty, tail `t^(1..2):=0` → `T=(0,0)`,
  `M=(3-0)(3-0)=9=Mval(0,0)`.
- **Case 2, `S=2,J=0`:** create `u_(2,1)`; head `t^(1):=M^{(2)}=3` (**reset**), tail `t^(2):=0` →
  `T=(3,0)`, `M=(3-0)(4-0)=12=Mval(3,0)`.
- **Case 1(1), node `S=2,J=0,J₁=1`, parent `B=(1,1)` (`M=4`):** tail `t^(2):=J=0`, head `t^(1)`
  **unchanged** → `T=(1,0)`; `M'=4+1·(M^{(3)}-0)=4+4=8=Mval(1,0)` — **the binding divisor**
  (`8=minAdm`, `λ_core=4`). The `L=2` minimizer profile `(1,0)` is produced by this single merge on the
  `S=1` rank-1 divisor.

**Classification (page-pinned).** The `T`-update is a **clean componentwise rule** over the fixed
index set `{1..L}`: a **tail-slice write** `t^(S..L):=J`, plus a head that is **unchanged** (1(1)) /
**inherited** (1(2)) / **reset to `(M^{(2)},…,M^{(S)})`** (Case 2). **No index is inserted or deleted;
no vector is merged.** The split point is `S` (the current layer), already in the State. The dynamic /
re-indexing work belongs to the **`b`-chain** (which divisor sits at which `b`-level, the divisibility
products) — which is **derived** from the `t̃` values, not a carried structure. `[CERT]` full-`T` is a
fixed-length `ℕ^L` field with an `O(L)` update/compare; **cheap** (constant-size for fixed depth).

**Scoped-claim wording.** `[CERT]` *The full-`T` update is a clean 3-way componentwise rule on the
fixed index set `{1..L}` (tail-write + head unchanged/inherit/reset); it involves NO re-indexing and
NO vector merge, and each step's exponent equals `Mval(T)`. Carrying full `T` (vs `t̃`) is `O(L)`
storage/compare — cheap.*

**→ 3: CLEAN RULE, not a balloon. The balloon risk is a DIFFERENT field — support propagation
(`genDivExp`: which `u`-vars divide which generator) — NOT `T`. The "T balloons like support" fear is
misdirected: `T` is stable-index; support is what balloons. Prices R1's full-`T` carrier as cheap →
unblocks task #8; confirms compass fork-10/R1 (full-`T` in the State, `t̃` derived) carries no
`μ`-descent-retrofit risk on the `T` side.**

---

## Codex decorrelation summary

`[OBS]` Codex (hypothesis withheld; given only the page-pinned rules + `minAdm` values) independently:
(i) replayed the chart tree and produced **the same terminal atlas** as my nested-profile enumeration
at *both* L=2 instances (min `3` / `8` = minAdm; identical profiles) — strong decorrelated agreement;
(ii) found **no undershoot** among `t̃=0` divisors, and independently flagged the positive-`t̃`
small-`M` red herrings + the `t̃=0`-only contribution rule; (iii) found **no genuine tie** at
`(2,2,2)`/`(3,3,4)` (sole candidates) and produced the `(2,2,2,2)` forcing witness with the
`(1,1,1)`-vs-`(2,1,1)` collision; (iv) classified the `T`-update as **clean / fixed-length / cheap**;
(v) flagged a coverage caveat (full pivot-chart cover, not the corner chart).

`[OBS]` **Codex's own "most likely wrong"** (inference flags preserved, NOT promoted to fact): the
`S=0→1` boot convention and all-pivot chart-multiplicity expansion are **inferred** (the transcription
does not fix them); the "smallest tie" uses a width-1 tuple `(2,2,2,1)` — under a reduced-width
convention use `(2,2,2,2)` (which I verified); divisor **persistence** after Case-1(2) is inferred
from the `b`-chain structure. My verdicts do not rest on the boot/multiplicity (Q1 value + no-undershoot
are established independently of the tree; the tie witness is verified at rule level for the two
`T`-vectors, tree-level only for their live coexistence).

---

## Close (firmest result / most likely to break / next step)

- **Firmest:** at `(2,2,2)`/`(3,3,4)` there is **no undershoot** by five independent legs, and the
  binding divisor is provably **non-toric** (coordinate weights are loose: `4>3`, `9>8`); the full-`T`
  update is a **clean cheap** fixed-index rule (verdict 3, high confidence — page-pinned + arithmetic).
- **Most likely to break the closure:** the **proper coverage/cover-image theorem** (R2) — un-proved by
  Aoyagi, non-toric, and it must instantiate the **full pivot-chart cover** (the corner-only reading has
  an explicit gap). The no-undershoot legs do not substitute for it.
- **Next construction/consult that would settle the open part:** the full-`T` tie-break is only
  exercised at `L≥3` — the cheapest probe that would *both* stress the tie-break selection *and*
  hit the SchurCore depth-≥3 wall is an explicit `(2,2,2,2)` chart-atlas closure check (enumerate the
  layer-3 charts, confirm the tie-break at `(3,0,1)` picks `(1,1,1)`, and that the emitted `t̃=0`
  min stays `3`). That single instance converges the two open surfaces (tie-break faithfulness + depth-≥3
  coverage).
