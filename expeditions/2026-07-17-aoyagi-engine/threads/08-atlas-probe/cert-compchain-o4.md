# Cert — o4 CompChainInv preservation: the paper's full-chain invariant is FALSE; reshape to SameLevelChainInv

*Seat: `pen-and-paper` (pnp08), fork-13 o4 — the "unattempted brick", a PROOF WE OWE (the paper does not
cleanly prove the chain invariant; §5 defect record). Decorrelated: my VALIDATED profile simulator
(`battery/nonmono-2232-sim.py`, checks a leaf atlas matching the minAdm recursion at 4 instances) +
an independent Codex proof-attempt (`codex/compchain-preservation-{prompt,answer}.md`, hypothesis
withheld). Scope battery: `battery/compchain-scope.py` (exit-0, integer-only, 18 instances). Register
key as before.*

## The contract under test (fork 13)

The oracle's mutual induction: `CompChainInv(s)` ⟹ the eligible set is a **chain** ⟹ the Def-4
componentwise **minimum exists** (o2) ⟹ the chooser picks it ⟹ (consuming minimality) comparability is
**preserved** at every child (o4). The question: is total comparability preserved, uniformly in `L`,
for the tail-write (case-1(1)) and the appends (case-1(2)/case-2)?

**Headline: as the paper states it (Def 4 / p.15: `T_{s,k} ≤ T_{s',k'} or ≥` for ALL pairs), the
invariant is FALSE. It must be reshaped to `SameLevelChainInv` — which holds everywhere, is what o2
actually needs, and leaves the value untouched.**

---

## Part 1 — REFUTATION of full total-comparability (two-way confirmed)

`[CERT]` **Minimal counterexample** (Codex found it from a fresh angle; my simulator reproduces it
exactly): `M=(2,2,1,1)` (`L=3`; `M(2)=2`, `M(3)=M(4)=1`). Layer 1 creates `{(0,0,0),(1,1,1)}`. At
`(S,J)=(2,0)`, level `ℓ=1`, apply case-1(2) to `f=(1,1,1)`: append `setTail(f,2,0)=(1,0,0)`, `f` stays;
`M(3)=1` advances to `(3,0)` with chain `(0,0,0)<(1,0,0)<(1,1,1)`. At `(3,0)` the case-1 interval
`[J+1, M(3)-1]=[1,0]` is empty ⟹ **Case 2**, appending the running-min-head divisor `c=(M(2),M(3),0)=
(2,1,0)`. Then
> `(2,1,0)` vs `(1,1,1)`: `(1,1,1) ≰ (2,1,0)` (coord 3: `1>0`) and `(2,1,0) ≰ (1,1,1)` (coord 1:
> `2>1`) ⟹ **INCOMPARABLE**. Total comparability VIOLATED.

`[CERT]` **Mechanism.** A **width drop** shrinks the `b`-chain; a divisor created earlier at level
`ℓ` (here `(1,1,1)`, `ℓ=1`) is **stranded above** the shrunken chain (`ℓ ≥ M(S)`); the Case-2 append,
whose head is the (large) running-min widths and whose tail is `J`, is incomparable with the stranded
divisor (larger head, smaller tail). Holds under BOTH head-reset modes — orthogonal to the fork-12
raw-vs-runmin fix.

`[CERT]` **Exact scope** (`compchain-scope.py`, 18 instances, prediction matched 18/18): full
total-comparability fails **iff there is an interior bottleneck** —
> `∃ 3 ≤ S ≤ L` with `min(M^{(1)},…,M^{(S)}) < min(M^{(1)},M^{(2)})`

(the running-min drops below the layer-2 min at a non-final layer). Witnesses: `(2,2,1,1)`, `(3,3,1,1)`,
`(3,3,2,2)`, `(4,4,2,2)`, `(4,4,3,2)`, `(3,3,2,1)`, `(2,2,1,2)`, `(2,2,2,1,1)`. NOT failing (drop only
at the last layer, or no interior stranding): `(3,2,4,2)`, `(2,2,2,1)`, `(3,2,2,2)`, `(3,3,4,2)`,
`(3,3,3,1)`. **Interior bottlenecks are a common DLN configuration — this is in scope, not a corner
case.** This is the §5 "defect record": the paper's p.15 invariant is over-strong.

---

## Part 2 — the RESHAPE: `SameLevelChainInv` (holds everywhere, suffices for o2)

`[CERT]` Define `SameLevelChainInv(C) := ∀ a,b ∈ C, tilde a = tilde b → Comparable a b` (divisors at a
COMMON `t̃` level are pairwise comparable). It holds at **every reachable state on all 18 instances
(0 violations)**, including every interior-bottleneck instance where full comparability fails. It is
**exactly what o2 needs**: the chooser's eligible set `E = {T ∈ C : t̃ T = ℓ}` is same-level, so
`SameLevelChainInv ⟹ E` is a chain `⟹` a Def-4 minimum exists (and is unique). The `comp_violations`
(eligible-set incomparability) counter is `0` everywhere — o2 min-existence is robust.

`[CERT]` **`HeadChainInv` (the head-projection `T_{1..S-1}` forming a chain) is ALSO too strong** — it
fails at `(3,3,1,1)`,`(4,4,2,2)` where `SameLevelChainInv` holds. So the invariant is specifically
same-level, NOT a global head-chain. (Recorded to save the architect a dead route.)

---

## Part 3 — the lemmas, PROVED uniformly (Lean-ready)

The one auxiliary invariant the proofs consume (Codex's "active-tail constancy" = my flat-tail),
verified `0` violations at every state on all instances:
> **`FlatTail(S,T) := ∀ i ≥ S, T i = T S`** (the tail from the current layer is constant), and with
> **`WeakDec(T) := Monotone-decreasing`**, `tilde T = T S = the tail value`.
> Maintenance: initial `(r,…,r)` is flat; case-1/2 write the tail to a constant `J`; a layer advance
> `S→S+1` shrinks a constant suffix to a constant suffix. WeakDec: new tail `J < ℓ ≤ head`. (both landed/one-line.)

**Lemma A — case-1(1) tail-write / case-1(2) append of the eligible MINIMUM (PROVED, uniform in L;
me + Codex identical).** Let `f` be the eligible minimum at level `ℓ`, `J < ℓ`, with the run-gap
`{t̃ = i} = ∅` for `J < i < ℓ`. Put `h = setTail(f,S,J)`. Since `WeakDec+FlatTail ⟹` every coord of
`f ≥ ℓ > J`, `h ≤ f`. For any `g` **comparable to `f`**:
- `f ≤ g`: `h ≤ f ≤ g`. ✓
- `g ≤ f` (`g ≠ f`): `g ∉ E` (else minimality `f ≤ g` + `g ≤ f ⟹ g = f`), so `t̃ g ≠ ℓ`; `g ≤ f ⟹
  t̃ g ≤ ℓ`; the run-gap ⟹ `t̃ g ≤ J`. By `FlatTail+WeakDec`, `g i = t̃ g ≤ J = h i` for `i ≥ S`, and
  `g i ≤ f i = h i` for `i < S`. So `g ≤ h`. ✓

This is **the one uniform idea** (not a case grind): *minimality forces every `g` below `f` to sit at a
level `≤ J`, so its constant tail is already `≤ J`; lowering `f`'s tail to `J` keeps `h` above it.*

**Lemma B — case-2 append (PROVED for same-level; REFUTED for cross-level = Part 1).** `c =
(M(2),…,M(S), J,…,J)`. For a **same-level** `g` (`t̃ g = J`, so `g`'s tail `= J = c`'s tail): head
`c_i = M(i+1) ≥ g_i` by the width-bound `g_i ≤ M(i+1)` (`i<S`); tail equal. So `g ≤ c`. ✓  For a
**cross-level** stranded `g` (`t̃ g > J`), `c` is incomparable (Part 1) — but such `g` is a DIFFERENT
level, so this does NOT violate `SameLevelChainInv`.

`[CERT, scoped]` **`SameLevelChainInv` preservation in full** is verified `0/18` empirically. The proved
pieces above cover: case-2 (same-level, width-bound+equal-tail) and case-1 **in the no-bottleneck regime**
(where the full chain holds and Lemma A applies to all `g`). The **residual proof obligation** at interior
bottlenecks is a single sub-lemma — *when case-1 places `f' = setTail(f,S,J)` at level `J`, it is
comparable to every pre-existing level-`J` divisor* — which reduces (both share tail `= J`) to
**head-comparability at a common level**. This is NOT the global head-chain (that fails); it is the
same-level restriction, empirically `0/18`. Flagged as the one brick to formalise beyond Lemma A/B.

**o2 (min-existence), Lean-ready:** `E ⊆ C` same-level; `SameLevelChainInv ⟹ E` totally ordered by `≤`;
a nonempty finite totally-ordered set has a least element ⟹ the chooser's `f` exists and is unique.

---

## Part 4 — value safety + the fidelity caveat

`[CERT]` `min` over `t̃=0` leaf divisors `= minAdm` at **every one of the 18 instances**, including all
interior bottlenecks. The finiteness / no-undershoot VALUE is untouched by the full-chain failure — only
the paper's over-strong invariant is false.

`[SPEC] Caveat (preserved, both mine and Codex's flag).` The profile simulator's case-1(2) **keeps** the
parent `f` (it is the symmetric-quotient PROFILE projection, blind to geometric fan-out; p.17 actually
reparametrizes `u_{s,k}=u_{S,J+1}u'_{s,k}`). IF the faithful `ConDecision` instead **consumes/
reparametrizes** `f` in case-1(2), the stranded divisor might not persist and full comparability could
survive. But `SameLevelChainInv` (and the eligible-set chain `comp_violations=0`) hold in EITHER reading,
and o2 needs only that — so building o1/o4 on `SameLevelChainInv` is **robust to this open question**,
whereas building on full total-comparability is not.

---

## Codex decorrelation summary + inference flags

`[OBS]` Codex independently: PROVED Lemma A (1a) and (1b) with the SAME mechanism ("active-tail
constancy" = flat-tail) and the same case split; and **REFUTED case-2** with the `(2,2,1,1)` state
`(3,0)`, `c=(2,1,0)` incomparable to `(1,1,1)` — reproduced exactly by my simulator. `[OBS] Codex "most
likely wrong":` the counterexample uses the inferred "case-1(2) advances immediately to the next layer"
and the "case-1(2) keeps `f`" readings (the same fan-out caveat above); the min is read as a least
member of `E`. My simulator confirms the counterexample under the profile model, and the scope
prediction (interior bottleneck) matches 18/18.

---

## KILL-CONDITION status + recommendation

- Task-1 clarifier: `comp_violations = 0` (eligible chain) at `(2,2,3,3,2)`,`(3,2,4,2)` and all
  instances (o2 robust); `profile-set == Adm` under runmin (o5-IN); value safe.
- **o4 kill FIRED for the paper's FULL invariant** (interior bottlenecks) — but the reshaped
  `SameLevelChainInv` passes `0/18`. **Recommendation:** build `o1`/`o4` on `SameLevelChainInv`
  (same-`t̃` comparability), NOT the paper's full total-comparability; state the refutation as a
  `¬(full-comparability)` regression witness at `(2,2,1,1)`; and either (i) confirm the `ConDecision`'s
  case-1(2) keeps `f` (then the reshape is mandatory) or (ii) if it consumes `f`, full-comparability may
  be recoverable — but `SameLevelChainInv` suffices regardless, so the safe build does not wait on (i)/(ii).

## Close

- **Firmest:** the paper's p.15 total-comparability is FALSE at interior bottlenecks (two-way, exact
  scope 18/18); `SameLevelChainInv` is the correct, sufficient, everywhere-holding replacement; value safe.
- **Most likely to break the build:** committing o4 as full total-comparability — unprovable. The gate
  correctly reshapes it.
- **Next:** the single residual sub-lemma (case-1 same-level head-comparability at bottlenecks) — the
  one brick beyond Lemma A/B; and the `ConDecision` case-1(2) keep-vs-consume `f` confirmation.
