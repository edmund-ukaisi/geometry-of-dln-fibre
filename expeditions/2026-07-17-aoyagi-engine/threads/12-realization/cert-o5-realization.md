# Cert — o5-IN REALIZATION: full ⊇ Adm is FALSE (stranding); the strict need minAdm ∈ P is SAFE

*Seat: `pen-and-paper` (pnp-o5), fork-13 o5-IN — the REALIZATION / stratum-completeness half ("the
t̃=0 profile-set contains Adm", elder-gate5). Direction: `witness` (exhibit the realizing path for each
a ∈ Adm). Instrument: the ORIGINAL VALIDATED simulator `threads/08-atlas-probe/battery/nonmono-2232-sim.py`
(runmin/FIX-A, integer-only, validated on the four known atlases), reused as ground truth; plus my own
branching tracer/steerer (`threads/12-realization/*.py`) and a consolidated exit-0 battery
(`threads/12-realization/battery/realization-battery.py`, 847 instances). One decorrelated Codex consult
(`threads/12-realization/codex/realization-{prompt,answer}.md`, gpt-5.x xhigh, hypothesis withheld).
Exact recursion only; NO Monte-Carlo. Register key as in the earlier certs.*

## Headline (the truth-value, sharp)

**The full ⊇ Adm is FALSE.** `P(M)` (the set of t̃=0 leaf-divisor profiles of the built tree) is a
PROPER subset of `Adm(M)` at every interior-bottleneck width vector — 84/351 instances at widths {1,2,3},
L≤4 (~24%). The elder-gate5 o5-IN target *"t̃=0 profile-set == Adm"* is **false** at deeper non-monotone
instances (the four pre-committed instances are all bottleneck-free, which is why it passed there).

**The strict need is SAFE.** `minAdm(M) ∈ terminalExponents` holds at EVERY scanned instance — `min` over
`P(M)` equals `minAdm(M)` (0 failures / 847), and every `Mval`-minimizer is realized (PROVED, §3). So the
Lean assembly (o5-∈, the value the payoff needs) is intact; only the stronger *stratum-completeness* claim
is false.

**Exact characterization (two-way):** `P(M) = { a ∈ Adm(M) : Clearable(a) }`, with `Clearable` defined in
§1. Verified EXACT at all 847 scanned instances AND independently derived+proved by Codex.

Fallback disposition (brief item 6): full ⊇ Adm **resists** (it is false); I certify the
**minimizer-only** statement `minAdm ∈ P(M)`, which is what o5-∈ strictly needs — PROVED in §3.

---

## 0. Objects (from the recursion, FIX-A runmin)

`M = (M¹,…,M^{L+1})`, `L` layers. Running-min corank `M(S) = min(M¹,…,M^S)`; write `r_S := M(S)`.
A divisor is `T = (T¹,…,T^L)`, level `t̃(T) = min T`. States `(S,J,divs)`; start `(1,0,∅)`. At `(S,J)`
with `MSp1 = min(r_S, M^{S+1})`:
- `S = L+1`: **leaf**. · `J ≥ MSp1`: **rollover** → `(S+1,0,divs)` (forced).
- else `occ_above = { levels m in divs : J+1 ≤ m ≤ r_S − 1 }`.
  - nonempty → **Case 1**: `target = min(occ_above)`, `f =` Def-4-least divisor at level `target`.
    Branch: **1(1)** replace `f` by `setTail(f,S,J)`, STAY at `(S,J)`; **1(2)** add a copy
    `setTail(f,S,J)`, keep `f`, go to `(S,J+1)`.
  - empty → **Case 2**: add `c` with head `cⁱ = M(i+1) = r_{i+1}` (`i<S`, running-min envelope) and
    tail `cⁱ = J` (`i≥S`); go to `(S,J+1)`.

`P(M) := { T : T ∈ divs at some leaf, t̃(T) = 0 }`. `Adm(M) :=` weakly-decreasing `a=(a¹≥…≥a^L=0)` with
`aⁱ ≤ M(i+1)` for all `i` (equivalently `aⁱ ≤ r_{i+1}`). The ⊆ half `P ⊆ Adm` is the Lean `leaf_mem_Adm`
(and holds at all 847 instances: 0 EXTRA profiles). This cert adjudicates the ⊇ half.

**Load-bearing structural facts** (FlatTail + WeakDec, from cert-compchain-o4, re-confirmed here):
at `(S,0)` every divisor has coords `S..L` equal to its level `t̃`; coords `1..S-1` are frozen. A t̃=0
leaf divisor with profile `a` has coord `i` frozen at `aⁱ` at the end of layer `i`; the tail reaches `0`
by the clearing layer `clear(a) = 1 + max{i : aⁱ > 0}`.

---

## 1. The characterization: `P(M) = Clearable-Adm(M)` `[CERT, two-way]`

Define the **birth layer** `b(a) = 1 + (`length of the maximal prefix of `a` equal to the running-min
envelope `(r_2, r_3, …)`; i.e. the largest `k` with `aⁱ = r_{i+1}` for all `i ≤ k`, plus 1`)`. Coords
`1..b−1` of `a` are the envelope; coord `b` is the first strictly below (`a^b < r_{b+1}`), or `a` is the
all-envelope profile (`b = clear`).

> **`Clearable(a)`** := for every layer `S` with `b(a) < S ≤ clear(a)`:
> `a^S < a^{S-1}  ⟹  a^{S-1} < r_S`.
> (Every strict descent of `a` AFTER the birth layer must start from a level strictly below the running
> min at that layer.)

`[CERT]` **`P(M) = { a ∈ Adm : Clearable(a) }` EXACTLY**, verified 0 counterexamples across 847
instances (widths up to 4, L up to 5): `battery/realization-battery.py` B2. Independently, Codex derived
the equivalent boxed predicate *"every strict descent from a coordinate saturating its running-minimum
(`a^{s-1} = r_s > a^s`) must have the complete running-min envelope as its prefix"* and named the
mechanism **running-min saturation freezing** — the two forms coincide (Codex's "prefix = full envelope
up to `s`" ⟺ `s ≤ b(a)`; his "saturation `a^{s-1}=r_s`" is forced because `Adm` gives `a^{s-1} ≤ r_s`,
so `a^{s-1} ≥ r_s ⟺ a^{s-1} = r_s`).

**Status of the two directions** (brief item 2, controller pin):
- **`⊆ Clearable` (unclearable ⟹ stranded): `[PROVED]`** at rule level — the `occ_above ⊆ [·, r_S−1]`
  argument (§2), chooser/branch-independent. The Lean assembly needs only the ⊇-at-minimizer direction,
  so a formaliser may carry ⊆ as battery-status without blocking D — but it IS a clean proof.
- **`⊇ Clearable` (clearable ⟹ realized): `[PROVED modulo one battery-verified brick]`** — the steering
  rule + descent invariant (§4); the sole brick is the intra-layer pull-ordering, reusing banked o4.
- Only the **minimizer instance of ⊇** is load-bearing for the Lean o5-∈, and it is `[PROVED]` (§3).

---

## 2. The obstruction: why non-clearable profiles are STRANDED (chooser/branch-independent) `[CERT]`

**Mechanism (the one uniform idea).** `occ_above` at layer `S` is `[J+1, r_S − 1]`. **A divisor at level
`≥ r_S` is never in `occ_above` at layer `S`, for any `J` and any Case-1 chooser pick.** So it is never
targeted by Case 1 at layer `S`; rollover and Case 2 do not lower existing divisors. Hence it survives
layer `S` at level `≥ r_S`. Since `r_S` is non-increasing in `S`, it stays `≥ r_{S'}` for all later `S'` —
it can **never** be pulled to `t̃ = 0`.

**Consequence.** A t̃=0 divisor with profile `a` needs coord `S−1` frozen at `a^{S-1}` and then, if
`a^S < a^{S-1}`, its level lowered from `a^{S-1}` to `a^S` DURING layer `S` — which requires
`a^{S-1} ≤ r_S − 1`. The only descent that escapes this is the running-min envelope itself, which is
**born already at its head value by Case 2** (Case-2 sets head coord `i` to `r_{i+1}` directly, no pull) —
this is why the `S ≤ b(a)` transitions are exempt. Therefore a non-clearable `a` (a strict descent at
`S > b(a)` from `a^{S-1} = r_S`) is **unrealizable at t̃=0**.

`[CERT]` **Chooser- and branch-independent.** The argument uses only `occ_above ⊆ [·, r_S−1]`, so no
Case-1 pick and no 1(1)/1(2) choice can clear a level-`r_S` divisor. Confirmed by exhaustive search over
ALL chooser picks × ALL branches on the witness `M=(3,3,4,2,3)`: both non-clearable admissible profiles
`(2,2,2,0)`, `(3,2,2,0)` are unreachable at t̃=0 under any pick/branch (`battery` B5). So the
**nondeterministic** tree also fails ⊇ — this is a hard structural obstruction, not an artifact of the
Def-4-minimal chooser.

**The witness in full.** `M=(3,3,4,2,3)`, running mins `(r_1..r_5)=(3,3,3,2,2)`. `(2,2,2,0) ∈ Adm`
(`a³ = 2 = r_4` is the tight running-min bound). Its would-be carrier `(2,2,2,2)` sits at level `2 = r_4`;
layer 4 clears only levels `≤ r_4 − 1 = 1`, so it strands at t̃=2. Cross-validated on the original sim:
`(2,2,2,·)`, `(3,2,2,·)` appear ONLY at t̃=2 (`Mval` 7 and 8 — both above `minAdm=5`, value-safe). This
is the **K3 stranding** (fork 12(b)(ii)): the missing strata live at t̃>0, fenced by the paper's t̃=0
read-off. A 4th verified read-off-shape defect alongside Def-3, FIX-A, and the p.15 full-chain.

**Scope = cert-compchain-o4's interior bottleneck.** `[CERT]` `{M : P(M) ⊊ Adm(M)}` equals
`{M : ∃ 3 ≤ S ≤ L, r_S < r_2}` (the interior width-drop below the layer-2 min) — 0 mismatches / 791
instances. The realization gap and the p.15 full-comparability failure (cert-compchain-o4 Part 1) are
**two faces of one width-drop stranding mechanism**: a divisor whose level equals the dropped running
min is stranded above the shrunken chain.

---

## 3. The strict need: `minAdm ∈ terminalExponents` — the load-bearing PAPER PROOF `[PROVED, two-way]`

**This is the piece the Lean D-task formalises** (controller pin). Claim: **every `Mval`-minimizer of
`Adm(M)` is Clearable** — hence realized (§4), hence `minAdm ∈ terminalExponents`. Small exact steps
(Codex's envelope-splice; I verified each step, 0 counterexamples). Write
`Mval(M,a) = (M¹−a¹)(M²−a¹) + Σ_{j=2}^{L} (a^{j-1}−a^j)(M^{j+1}−a^j)`, and `r_S = min(M¹,…,M^S)`.

**Step 1 `[PROVED]` — each running-min-envelope term is 0.** The envelope value at coord `i` is `r_{i+1}`.
- head term: `(M¹−r_2)(M²−r_2) = 0`, since `r_2 = min(M¹,M²)` kills one factor.
- for `2 ≤ j ≤ L`, the envelope term is `(r_j − r_{j+1})(M^{j+1} − r_{j+1})`, and `r_{j+1} = min(r_j, M^{j+1})`
  kills one factor: if `M^{j+1} ≥ r_j` then `r_{j+1}=r_j` and `r_j−r_{j+1}=0`; else `r_{j+1}=M^{j+1}` and
  `M^{j+1}−r_{j+1}=0`.
So the running-min envelope contributes **exactly 0** to `Mval`. (Battery: 0 counterexamples.)

**Step 2 `[PROVED]` — a non-envelope prefix contributes `> 0`.** Each `Mval` term is a product of two
NON-negative integers (`Adm` gives `aⁱ ≤ r_{i+1} ≤ M^{i+1}` and `a` weakly decreasing, so both factors
`≥ 0`). Term `j` is `0` iff `a^{j-1}=a^j` or `a^j = M^{j+1}` — and the componentwise-maximal all-zero
choice is exactly the envelope (Step 1). Any prefix differing from the envelope has some strictly positive
term, so its contribution is `> 0`. (Battery: strict for all 356 non-clearable profiles.)

**Step 3 `[PROVED]` — the envelope-splice.** Let `a ∈ Adm` be non-clearable, `s` its first bad descent
(`a^{s-1} = r_s > a^s`, prefix `1..s−1` not the full envelope — §1). Define `b` by `bⁱ = r_{i+1}` for
`i < s` and `bⁱ = aⁱ` for `i ≥ s`. Then:
- (a) `b ∈ Adm`: `bⁱ = r_{i+1} ≤ r_{i+1}` and weak-decrease holds at the seam because
  `b^{s-1} = r_s = a^{s-1} > a^s = b^s`.
- (b) `Mval` splits as (prefix terms `j < s`) + (boundary term `j=s`) + (suffix terms `j > s`). The
  boundary term uses `a^{s-1}=r_s=b^{s-1}` and `a^s=b^s`, so it is UNCHANGED; the suffix terms use only
  `aⁱ (i≥s)=bⁱ`, UNCHANGED.
- (c) by Steps 1–2 the prefix contribution drops from `> 0` (non-envelope `a`) to `0` (envelope `b`).
Hence `Mval(b) < Mval(a)`. (Battery: strict decrease + `b ∈ Adm`, all 356.)

**Step 4 `[PROVED]` — corollary.** By Step 3 a non-clearable profile is never a minimizer ⟹ **every
`Mval`-minimizer is Clearable** ⟹ realized by §4 ⟹
`minAdm(M) = min_{Clearable-Adm} Mval = min_{P(M)} Mval ∈ terminalExponents`. Directly cross-checked:
`min over P(M) == minAdm(M)` at all 847 instances (`battery` B3); every minimizer Clearable (`battery`
B4). Witness: `minAdm(3,3,4,2,3)=5`, attained by `(3,3,1,0),(2,2,1,0),(2,2,0,0)`, all in `P`.

*(This is the STRONG form — every minimizer clearable. The weaker "∃ a clearable minimizer" also
follows and equally suffices for `minAdm ∈ terminalExponents`; I certify the strong form.)*

This is the o5-∈ IN-half in its **provable, sufficient** form: NOT "profile-set ⊇ Adm" (false) but
"`minAdm` is attained by a realized (clearable) profile." It needs §4 only at the ONE minimizer, not the
whole clearable set.

---

## 4. The positive witness: the steering rule + descent invariant (⊇ Clearable-Adm) `[CERT + one flagged brick]`

For every `a ∈ Clearable-Adm` I exhibit a deterministic root-to-leaf path realizing `a` at t̃=0, under
the FIXED Def-4-minimal chooser (so it is a path in the BUILT tree; item-1 finding: no non-minimal pick
is ever needed — the minimal chooser realizes the entire clearable set, `battery` B6).

**The steering rule `R(a)` (state-free in the decision).** At a Case-1 node in layer `S` with target
level `ℓ`: take **1(1) iff `ℓ > a^S`**, else **1(2)**. Case-2/rollover forced. *("Descend every divisor
sitting above `a`'s layer-`S` value; preserve a plateau at level `a^S`.")* `R(a)` realizes EXACTLY the
clearable profiles — 0 counterexamples / 847 instances (`battery` B6).

**The descent invariant (anchor form, Lean-ready shape).** Track one divisor `A` ("the anchor").
- **Base (birth, layer `b=b(a)`):** the steered layer-`b` sweep reaches pivot `a^b` with all levels
  `> a^b` pulled down (rule 1(1) on `ℓ > a^b`), so `occ_above` empties and Case 2 births `A` with head
  `(r_2,…,r_b) = (a¹,…,a^{b-1})` and tail `a^b`. Invariant at end of layer `b`: `A` has coords
  `1..b = (a¹,…,a^b)`, level `a^b`.
- **Maintenance (layer `S`, `b < S ≤ clear`):** given `A` at start of layer `S` with coords
  `1..S-1 = (a¹,…,a^{S-1})` and level `a^{S-1}`:
  - **plateau `a^S = a^{S-1}`**: `ℓ = a^{S-1} = a^S` is not `> a^S`, so the rule 1(2)'s `A` — it stays at
    its level; coord `S` freezes at `a^S`.
  - **descent `a^S < a^{S-1}`** (needs `a^{S-1} < r_S`, i.e. `Clearable`): `A` is at level `a^{S-1} ≤ r_S−1`
    (in the clearable range), the rule 1(1)'s levels `> a^S` down to the current `J`; when `J = a^S`, `A`
    (the highest live level) is pulled to level `a^S`; coord `S` freezes at `a^S`.
  In both cases the invariant re-establishes at end of layer `S` with coords `1..S`, level `a^S`.
- **Termination (layer `clear`):** `a^{clear} = 0`; the rule 1(1)'s `A` down to level `0` (all levels
  `> 0` pulled at `J=0`). `A` becomes t̃=0 with coords `1..clear-1 = a`'s prefix and coords `clear..L = 0`,
  i.e. `A = a`. `a ∈ P(M)`. ∎

`Clearable` is load-bearing EXACTLY at the descent case: `a^{S-1} < r_S` is what puts `A` inside
`occ_above`'s range so it can be pulled. Non-clearable ⟹ `A` at level `r_S` invisible to Case 1 (§2).

`[FLAGGED — one brick, battery-verified]` The descent case asserts `A` lands at **exactly** `a^S` (not
lower) and is the Def-4-least at its level when pulled. This is the intra-layer pull-ordering: lower
levels clear first (Case 2 refills level `J` as `J` advances), the anchor at the top level is pulled last
at `J = a^S`, and Def-4-minimality keeps the anchor's head below competing same-level divisors (this is
the o4 `LiveHeadDom` / chooser-minimality already certified in cert-compchain-o4 §6–7). Battery-verified
that `R(a)` realizes every clearable `a` (B6, 847 instances); the pull-ordering is the single sub-lemma
the formaliser transcribes, and it reuses the banked o4 machinery.

---

## 5. Boundary cases `[CERT]`

- **Root / layer 0:** start `(1,0,∅)`; layer 1 is pure Case 2 (no divisor above), creating the diagonal
  `(k,…,k)` at levels `k = 0..min(M¹,M²)−1`. The anchor for `b(a)=1` (i.e. `a¹ < r_2`) is the diagonal at
  level `a¹`; for `b(a)≥2` (`a¹ = r_2`) the anchor is born by later Case 2. Both handled by the base case.
- **At-exhaustion / rollover guard:** rollover `J ≥ MSp1` is forced and carries `divs` unchanged; it is a
  chartless edge (fork 13(Q3)). No divisor is cleared at rollover, consistent with the invariant (coords
  freeze at the last in-layer level).
- **`L = 1`:** `Adm = {(0)}`, `minAdm = 0`; the sole profile is realized (Case 2 at `(1,0)`). Trivially ⊇.
- **Minimal profile `a = (0,…,0)`:** `clear = 1`, `b = 1`; born Case 2 at `(1,0)` with tail 0. Always in
  `P`. Clearable (no descent layers).
- **Envelope-touching `a` (`aⁱ = r_{i+1}` up to some point):** the all-envelope profile
  `(r_2,…,r_{clear-1},0,…)` has `b = clear`, no post-birth descent — always Clearable/realized (pure
  Case-2 births). A profile that touches the envelope then drops (`a^{S-1}=r_S > a^S`, `S>b`) is exactly
  the **stranded** class (§2).

---

## 6. Battery manifest + extension (brief item 4)

`threads/12-realization/`:
- `battery/realization-battery.py` — **consolidated, exit-0**, 847 instances (widths up to 4, L up to 5):
  B1 `P ⊆ Adm` (0 extra), B2 `P = Clearable-Adm` exact, B3 `min P = minAdm`, B4 minimizer clearable,
  B5 chooser/branch-independent strand on `(3,3,4,2,3)`, B6 steering rule realizes exactly clearable.
- `trace-realization.py`, `realize-check.py`, `extract-rule.py`, `steer-v2.py`,
  `scope-scan.py`, `clearable-characterization.py` — the discovery/derivation scripts (per-leaf branch
  paths, birth histories, winning-path extraction, scope scan, exact-char verification).
- Fresh non-monotone L≥4 instances checked (beyond the 6 pre-committed): `(3,3,4,2,3)` [GAP found],
  `(2,3,2,4,2)`, `(3,3,4,2)`… — realization checker + steering verified. The 6 known instances
  `(2,2,2),(3,3,4),(2,2,2,2),(2,2,3,2),(2,2,3,3,2),(3,2,4,2)` all have `P == Adm` (bottleneck-free) —
  consistent, and explains why the gate never fired before.
- Exact scope counts committed alongside: `threads/12-realization/scope-counts.md`.

**Confound lesson `[STANDING COUNSEL]` (brief item 4 / controller pin).** The elder-gate5 o5-IN kill was
pre-committed against `(2,2,3,3,2)` and `(3,2,4,2)` (plus `(2,2,2,2),(2,2,3,2)`) — **all four are
bottleneck-free** (`min(M¹..M^S) ≥ min(M¹,M²)` for every interior `S`), so `P == Adm` there, and the gate
passed vacuously. The gap ONLY appears once an interior width-drop strands a level-`r_S` divisor. Going
forward, any pre-committed battery set for a read-off / completeness claim MUST include the KNOWN failure
mechanism — here an interior bottleneck `∃ 3≤S≤L, min(M¹..M^S) < min(M¹,M²)`, e.g. `(3,3,4,2,3)`,
`(2,2,1,1)`, `(3,3,2,2)`. This is the same lesson as the FIX-A defect (invisible at monotone widths /
L≤2): a nice-instance battery is necessary, never sufficient; the adversarial mechanism-aware instance is
the gate (cf. compass standing counsel "decorrelated from the atlas builder").

---

## 7. Kill-conditions status (brief item 5)

- **K1 (`a ∈ Adm` unreachable in the built tree):** **FIRED.** `(2,2,2,0)`, `(3,2,2,0)` at `M=(3,3,4,2,3)`
  (and 82 other instances at widths {1,2,3}, L≤4). The **nondeterministic** tree does NOT reach them
  either (§2, B5) — a hard obstruction, not a chooser artifact. Scoped exactly by the interior bottleneck.
- **K2 (even `minAdm` minimizer unreachable — MAJOR, stop-and-surface):** **DOES NOT FIRE.** `min P =
  minAdm` at all 847 instances; every minimizer is Clearable (PROVED §3). The paper's read-off MINIMUM
  (the value the payoff needs) is intact.
- **K3 (realizable only at t̃>0 — stranded):** **FIRED and is the mechanism.** The missing strata sit at
  t̃>0 (`(2,2,2,2)` at t̃=2 etc.), fenced by the t̃=0 read-off (fork 12(b)(ii)). `Mval` of the stranded
  strata exceeds `minAdm` (value-safe).

---

## 8. Codex decorrelation (hypothesis withheld)

`[OBS]` Codex (xhigh, given only the recursion rules + the 6 passing instances, NOT my conclusion)
independently: (i) VERDICT **No**, ⊇ Adm not universal, decisive instance `(3,3,4,2,3)` — computed the
same missing set `{(2,2,2,0),(3,2,2,0)}`, same `P\Adm = ∅`; (ii) derived the equivalent characterization
+ named **running-min saturation freezing**; (iii) PROVED both directions of the characterization
(Case-1 sees only `≤ r_s−1`; unsaturated descents produced by 1(1)-then-1(2)); (iv) PROVED every
minimizer is realized via the envelope-splice (the argument in §3, which corrected my own wrong-direction
transformation). `[OBS, inference flag preserved]` Codex marks the characterization `[PROVED]` at rule
level and the enumeration `[COMPUTED]`; my battery confirms the enumeration on the original validated sim
and the strict-decrease/Adm-closure of the splice (0 counterexamples / 356). Two independent derivations,
agreeing to the component.

---

## 9. Consequence for the Lean assembly (o5-IN)

- **DROP** the o5-IN target *"t̃=0 profile-set == Adm"* / `IsFullMonomialization`-as-⊇-Adm. It is FALSE
  at interior-bottleneck widths. The elder-gate5 kill "an instance where the t̃=0 profile-set differs
  from Adm" has FIRED at `(3,3,4,2,3)`.
- **KEEP** the provable + sufficient IN-half: **`minAdm ∈ terminalExponents`**, via §3 — `minAdm` is
  attained by a realized (clearable) profile (envelope-splice ⟹ the argmin is clearable ⟹ realized by
  the steering rule §4). This is exactly what `aoyagi_learning_coefficient` needs (the value, not the
  full stratum set).
- If the formaliser wants the strongest true completeness statement: **`P(M) = Clearable-Adm(M)`** (§1),
  with `Clearable` the boxed predicate. ⊇ Clearable-Adm is the descent invariant §4; ⊆ is
  `leaf_mem_Adm` + the strand obstruction §2.
- The `terminalExponents` READ-OFF must stay **t̃=0-restricted** (fork 12(b)(ii)): the stranded strata at
  t̃>0 are real and would corrupt an unrestricted `∀k`.
- Alignment with cert-compchain-o4: the `Clearable`/strand predicate rides on the SAME `LiveHeadDom` /
  running-min structure; the descent invariant's one flagged brick (§4) reuses that banked o4 machinery.

---

## Close

- **Firmest:** ⊇ Adm is FALSE (two-way; exact missing set at the witness); `P(M) = Clearable-Adm(M)`
  EXACT (847 instances + Codex proof); the strict need `minAdm ∈ terminalExponents` is SAFE and PROVED
  (envelope-splice, both derivations). Strand = running-min saturation freezing = cert-compchain-o4's
  interior bottleneck (0 mismatches / 791). Value never at risk (`min P = minAdm` everywhere).
- **Most likely to break the build:** committing o5-IN as ⊇ Adm (unprovable — false); or dropping the
  t̃=0 restriction on `terminalExponents` (the stranded t̃>0 strata re-enter). The steering-rule §4
  descent case rests on the intra-layer pull-ordering brick — battery-verified, formalize via banked o4.
- **Next (open part):** formalize `minAdm ∈ terminalExponents` via the envelope-splice minimizer +
  steering-rule realization (§3+§4); the one sub-lemma to transcribe is the pull-ordering (reuse o4
  `LiveHeadDom`). If ⊇ Clearable-Adm is wanted in Lean, the descent invariant §4 is the route; otherwise
  the minimizer-only path is shorter and sufficient.
