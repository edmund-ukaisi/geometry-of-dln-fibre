# Claim card — PIN2 option-2 comparability (`Sreg ≍ ∑deepestEPivot²`)

**Statement (the candidate, brief's option 2).** For `L=2, H=[2,2,2], r=1` (and `r=1` corank-≥2,
e.g. `H=[3,3,3]`), near the deepest point: ∃ `γ₁,γ₂>0` and a neighborhood `U` with, ∀ `w∈U`,
`γ₁·∑deepestEPivot²(split w) ≤ Sreg(w) ≤ γ₂·∑deepestEPivot²(split w)`, where `Sreg` = the FULL-product
regular block energy `(P00−1)²+P01²+P10²` (from `hconj`) and `∑deepestEPivot²` = the T=0
(`framedParamsRegPivot`) product regular block energy. (The proposed weakening of the exact `h00/h01/h10`.)

**Kill-condition (stated before hunting):** a point arbitrarily close to the deepest point where one of
`Sreg`, `∑deepestEPivot²` is 0 and the other is bounded away from 0 — refuting one direction of the
two-sided bound for any constant.

**Status: REFUTED (new tier).** Both directions killed by exact witnesses:
- Lower (`γ₁·Ereg ≤ Sreg`): **line A** `X0=X1=Z0=Z1=T0=0, Y1=−T1·Y0` → `Sreg=0`, `Ereg=(T1Y0)²>0`.
- Upper (`Sreg ≤ γ₂·Ereg`): **line B** `X0=X1=Y1=Z0=Z1=0` → `Sreg=(T1Y0)²>0`, `Ereg=0`.

**Tier:** new (our framing). **Evidence:** thread 31 (`thread.md`), sympy certificates
(`/tmp/option2_test.py`, `exact_lineA.py`, `comparability.py`), decorrelated Codex (`codex/`).

**Mechanism:** the inter-layer leak `(C0C1)₁₂ − (T=0)₁₂ = Y0·T1` (degree-2, same order as the signal,
produces exact cancellation). `Y0` is a GAUGE direction (verified: `δC0=corM·A` ⇒ `Y0` free; `G=[[1,−Y0],
[0,1]]` gauges line A to `(corM, diag(1,T1))`), so the T=0 product reads spurious gauge energy the true
loss does not see.

---

# Claim card — the correct comparable quantity (the repair)

**Statement.** `dlnLoss ≍ Sreg + Score` near the deepest point, where BOTH `Sreg = (P00−1)²+P01²+P10²`
and `Score = ‖P11 − P10⅟P00 P01‖²` are read off the FULL product `reindex(P0·N·QL) = fromBlocks
(P00−1) P01 P10 P11`. (= the banked leaf lemma `dlnLoss_two_sided_of_frame`.)

**Kill-condition:** a near-deepest point with `dlnLoss=0` but `Sreg+Score>0`, or vice-versa.

**Status: SURVIVED (new tier).** No witness found; `inf(dlnLoss/(Sreg+Score)) → 1` as scale→0 on
line-A-biased neighborhoods (`H=[2,2,2]` and `H=[3,3,3]`, `/tmp/inf_correct.py`, `corank2.py`); on
line A both = `det(P)/A`-equivalent and agree to machine epsilon. `Score = D − C A⁻¹B = det(C0)det(C1)/A`
(invariant core; Codex-confirmed). MC is a guide; the leaf lemma is the exact proof.

**Tier:** new framing of an already-banked sound lemma. **Evidence:** `dlnLoss_two_sided_of_frame`
(`DeepestGaugeBlocks.lean:558`, banked sorry-free); thread 31.

---

# Open risk (NOT a claim — flagged for controller)

`rlctAtOn(Φ_struct) = rlctAtOn(dlnLoss)` where `Φ_struct = ∑deepestEPivot² + ‖∏T‖²` (the structure's
hard-coded target). **Unresolved.** `V(Φ_struct) ⊊ V(dlnLoss)` (line A). On the minimal slice the two
RLCTs coincide (`= ½`) via the diffeo `Y1↦Y1+Y0T1` — but this is slice-local; the global statement is
NOT certified. The SAFE repair (repoint `regStraighten` to the FULL reg blocks) sidesteps this gamble.
