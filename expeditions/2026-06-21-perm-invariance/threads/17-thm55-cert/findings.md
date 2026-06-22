# Thread 17 — Thm 5.5 (M4) → Cor 5.10 (M6): a Lean-ready certificate

> Seat: pen-and-paper (no Lean). De-risk the M4→M6 chain into a Lean-targetable certificate, against
> the LANDED encoding (`Qseries`/`Pmult`/`P`/`Pm`, the M5 bridge, M6-prep, fivegon S0). Every
> load-bearing identity exact-rational verified (sympy, 0 float, all PASS); a decorrelated Codex
> (hypothesis withheld) reproduced the mechanism and gave the cleanest orthogonality induction.
> Homed by the controller from penpaper-s3's report (subagent `Write` harness-blocked); data
> artefacts committed `1069c96` (scratch/ + codex/, no .lean touched, verified no leak).

**VERDICT.** M4 (Thm 5.5) is a clean elementary chain on the LANDED fivegon. **S3 is NOT a
linear-system inversion and needs NO q-binomial / q-Vandermonde / Gaussian-binomial library** — it is a
direct algebraic substitution (S2 into the RHS) + reindex + ONE classical q-fact (orthogonality
`∑ₖ altP(k)·P(u−k)=[u=0]`), and that q-fact has a self-contained single-variable induction on the
LANDED `P_mul_one_sub_succ`. **M6 (Cor 5.10) closes per-`r` for all `r`** via the LANDED M5 bridge +
`Pmult_sub_comp_perm`. Size: **~3 files + M6 capstone, ~16 lemmas, ~540–890 lines**.

## 0. The LANDED floor (read-only, confirmed in-tree)
| object / lemma | file:line | role |
|---|---|---|
| `Qseries d r = ∑_{m∈kostantPartitions d r} X^{(codimForm N (extendℤ m)).toNat}·Pm N m` | `QSeries.lean:208` | LHS |
| `Pmult h=∏ᵢ P(h i)`, `P s=∏_{k=1}^s geomFactor k`, `Pm` | `QSeries.lean:127/159/178` | primitives |
| `P_succ : P(s+1)=P s·geomFactor(s+1)` | `QSeries.lean:145` | recurrence |
| `geomFactor_mul_one_sub : k≥1→geomFactor k·(1−X^k)=1` | `QSeries.lean:97` | inverse |
| `P_mul_one_sub_succ : P(s+1)·(1−X^{s+1})=P s` | `QSeriesDurfee.lean:33` | **(PA)** — drives ORTH |
| `one_sub_X_pow_ne_zero : 1≤n→(1−X^n)≠0` | `QSeriesDurfee.lean:153` | non-zero-divisor cancel |
| `sum_Qseries_eq_Pmult : ∑_{r∈range(d 0+1)} Qseries d r = Pmult d` | `QSeriesFivegon.lean:1331` | **S0/fivegon** |
| `fivegonSum_eq_sum_Qseries`; `fivegon` | `QSeriesFivegon.lean:1319/1293` | S0 internals |
| `dropCorner`,`dropCorner_mem`,`addCorner_mem`,`kostantPartitions_dminus_eq_image`,`dropCorner_injOn` | `CTheta.lean:227/278/298/341/360` | **corner bijection** (S1') |
| `codimForm_update_corner` | `CTheta.lean:215` | codim-blind to corner (S1') |
| `cCodim_eq_of_Qseries_eq`/`numTop_eq_of_Qseries_eq` | `QSeriesExtraction.lean:107/116` | **M5 bridge** |
| `Pmult_sub_comp_perm : Pmult(fun i↦(d∘σ) i−c)=Pmult(fun k↦ d k−c)` | `CThetaPermInvariance.lean:35` | **M6-prep** |

One **range mismatch** the chain bridges: LANDED fivegon sums `r∈range(d 0+1)` (`r=0..d₀`); paper sums
`s=0..min d`. They agree (gap terms vanish — see S2).

## 1. S1–S4 chain → Thm 5.5 (PowerSeries identities over ℤ⟦X⟧)
Target (`r=0`): `Qseries d 0 = ∑_{s=0}^{min d} altP s · Pmult(fun i↦ d i − s)`,
`altP s := (−1)^s·X^{s(s−1)/2}·P s`. Set `n:=min d`.

**S1' (clean corner-shift, paper Lemma 5.7 "add-longest"):** `Qseries d s = P s · Qseries(fun i↦ d i − s) 0`
(`0≤s≤min d`). q-series LIFT of the LANDED `dropCorner` bijection. **Avoids the paper's `(q)_s=∏(1−X^k)`
object AND `(q)_s·P_s=1` entirely** (presentation artefacts; S2 only needs `P_s·Qseries(d−s) 0`). Verified
PASS (`verify_s1_bijection.py`). Lean lemma `Qseries_corner_shift`: `Finset.sum_bij` over the bijection;
under `m↦dropCorner m`, exponent unchanged (`codimForm_update_corner`), `Pm N m = P_s·Pm N(dropCorner m)`
(one `(0,N)` factor `P_s` vs `P_0=1`) — verified. Hooks: `Finset.sum_bij`, `Finset.mul_sum`, the bijection
lemmas, a helper `Pm_dropCorner`.

**S2 (eqn:key):** `Pmult d = ∑_{s=0}^{min d} P s · Qseries(d−s) 0`. From LANDED S0 rewriting each term by
S1'. Verified PASS. **Range-gap step (load-bearing):** `Qseries d r = 0` for `min d < r ≤ d₀` (corner
`m(0,N)=r` forces `d_k≥r` at every vertex ⟹ `kostantPartitions d r = ∅`). Verified PASS
(`verify_range_gap.py`). Lean: `Qseries_eq_zero_of_min_lt` + `Finset.sum_subset` (range `min d+1 ⊆ range
d₀+1`, extra terms zero). Hooks: `mem_kostantPartitions`, `Finset.sum_subset`. (`min d` =
`Finset.inf'`/`min'` over univ.)

**S3 (inversion — the flagged-risky step, DE-RISKED):** four-line algebraic substitution, exact-verified
end to end (`verify_s3_clean.py` (i)-(iv) PASS):
```
∑_{s=0}^n altP(s)·Pmult(d−s)
  = ∑_s altP(s) · ∑_{t=0}^{n−s} P_t·Qseries(d−s−t) 0      [substitute S2 at e=d−s]
  = ∑_{(s,t): s,t≥0, s+t≤n} altP(s)·P_t·Qseries(d−s−t) 0   [triangle double-sum]
  = ∑_{u=0}^n (∑_{k=0}^u altP(k)·P(u−k))·Qseries(d−u) 0    [reindex u=s+t, k=s]
  = ∑_u [u=0]·Qseries(d−u) 0 = Qseries(d−0) 0 = Qseries d 0.[ORTHOGONALITY, §2]
```
Side-facts (verified): `min(fun i↦ d i − s)=min d−s` for `s≤min d` (inner limit `n−s`, double-sum =
triangle `{s+t≤n}`); `(d i − s)−t = d i −(s+t)` (`Nat.sub_sub`; no negative coord since `s+t≤n≤dᵢ`). Lean
lemma `thm55_zero`. Hooks: a reusable finite-triangular-convolution helper
(`Finset.Nat.antidiagonal`/`Finset.sum_bij'`), `Finset.mul_sum`, `Finset.sum_mul`, `Nat.sub_sub`.

**S4 (general `r`):** S1' applied to S3 at `d−r`: `Qseries d r = P_r·∑_{s=0}^{min d−r} altP s·Pmult(d−(r+s))`,
`(d−r)−s = d−(r+s)`. Paper's full `eq:Fd_formula`. Verified for **all** `r∈[0,min d]` (`verify_s3.py`
CHECK 2+3 ALL PASS). Lean `thm55`.

## 2. ORTHOGONALITY — the headline de-risk (no library)
`ORTH: ∑_{k=0}^u altP(k)·P(u−k) = (if u=0 then 1 else 0)` over ℤ⟦X⟧,
`altP(k)=(−1)^k·X^{k(k−1)/2}·P k`. **`altP` is a NEW def** (not in QSeries.lean):
`noncomputable def altP (k:ℕ) : ℤ⟦X⟧ := (−1)^k · X^(k*(k−1)/2) · P k`. Coefficient form of
`(x;q)_∞·(x;q)_∞^{−1}=1`. Mathlib v4.29 has none of the q-library — **and ORTH needs none.**

Clean Lean route — **single induction on `u`, no second variable, no Gaussian binomial** (Codex-proposed;
I independently found the equivalent truncated-`Y` route, this is cleaner). With
`O u := ∑_{k=0}^u altP(k)·P(u−k)`, prove `u≥1 ⟹ O u·(1−X^u) = (1−X^{u−1})·O(u−1)`.
Rests on the **pure split** `1−X^u = (1−X^{u−k}) + X^{u−k}·(1−X^k)` (exact, all `0≤k≤u`, verified)
distributed inside the sum, plus:
- `(PA) P m·(1−X^m)=P(m−1)` — **LANDED** `P_mul_one_sub_succ`.
- `(AA) altP k·(1−X^k) = −X^{k−1}·altP(k−1)` — pure `ring` from `(PA)` + `C(k,2)−C(k−1,2)=k−1` (verified).
First split-part telescopes to `O(u−1)` (`k=u` term vanishes, `1−X^0=0`); second, after dropping `k=0` and
reindexing `j=k−1`, gives `−X^{u−1}·O(u−1)`. Induct: `O 0=1`; `u=1`⟹`O 1·(1−X)=0`; `u≥2` IH `O(u−1)=0`
⟹`O u·(1−X^u)=0`. Cancel `(1−X^u)` via `geomFactor_mul_one_sub` (multiply by `geomFactor u`) or
`one_sub_X_pow_ne_zero`. Recurrence+conclusion verified to 13 orders (`verify_codex_orth.py` PASS). Lean
lemmas: `altP` (def), `altP_mul_one_sub` (=(AA)), `orth_recurrence` (the work), `orth`. Hooks:
`Finset.sum_range_succ`/`_succ'`, `Finset.mul_sum`, `Finset.sum_mul`, `pow_add`, `Nat.sub_add_cancel`,
`ring`, `P_mul_one_sub_succ`, `geomFactor_mul_one_sub`.

## 3. The triangular reindex (S3, Codex Q1)
`{(s,t): s≤μ, t≤μ−s} ↔ {(u,k): u≤μ, k≤u}`, `u=s+t, k=s` (inverse `s=k, t=u−k`), `μ=min d`. Side
conditions: `min(fun i↦ d i − s)=μ−s` (every `dᵢ≥μ`, some `dᵢ=μ`, `Fin(n+1)` nonempty) ⟹ inner S2 limit is
`μ−s` so the double-sum is exactly the triangle; `(fun i↦(d i−s)−t)=(fun i↦ d i−(s+t))` by `funext`/`Nat.sub_sub`.
`Qseries(d−s−t) 0 → Qseries(d−u) 0` is `k`-independent ⟹ factor by distributivity. Map to
`Finset.sum_sigma'`/`Finset.Nat.antidiagonal` or explicit `Finset.sum_bij'`; recommend a reusable
finite-convolution helper so S3 is a clean ORTH application.

## 4. M6 (Cor 5.10) — closing, per-`r`, for all `r`
`Qseries(d∘σ) r = Qseries d r` per `r`: in the Thm 5.5 RHS, `P r`/`altP s` carry no `d`; range
`s=0..min d−r` is a multiset invariant (`min(d∘σ)=min d`); the only `d`-dependent factor
`Pmult(fun i↦ d i − r − s)` is the **LANDED `Pmult_sub_comp_perm`** with `c=r+s` (after
`Nat.sub_sub: d i−r−s=d i−(r+s)` on both sides). **`Pmult_sub_comp_perm` supplies exactly the needed
symmetry for every `s` in range** — confirmed. Then the LANDED M5 bridge
`cCodim_eq_of_Qseries_eq`/`numTop_eq_of_Qseries_eq` (with `d'=d∘σ`, `r'=r`) gives `cCodim(d∘σ) r=cCodim d r`,
`numTop(d∘σ) r=numTop d r`. Verified PASS incl. ground-truth on the Kostant definition (`verify_m6.py`
(A)-(D)). **`r`-range subtlety:** the per-`r` identity holds for ALL `r` — by Thm 5.5 for `r≤min d`,
vacuously for `r>min d` (both sides 0, empty kostant). M5 bridge invoked only where `(C,θ)` defined
(`r≤min d`), where nonemptiness holds on both sides. **No `rankShift` needed for M6** (that's the
orthogonal `cCodim d r=cCodim(d−r) 0` reduction); M6 works per-`r` directly off Thm 5.5. Lean:
`Qseries_comp_perm`, `cCodim_comp_perm`, `numTop_comp_perm` into existing `CThetaPermInvariance.lean`.

## 5. Most-likely-to-break + size
**`orth_recurrence`** (§2): the `Finset.sum_range_succ'` peel-`k=0`/reindex-`j=k−1` bookkeeping inside the
split-distribution. De-risk: algebra fully pinned + verified to 13 orders; the M2 `durfee` proof already
executed the analogous peel-and-shift in `B_sum_desc` (`QSeriesDurfee.lean:114`) — in-tree, reusable.
**Fallback:** truncated-`Y` convolution-inverse `A_M·B_M≡1 mod Y^{M+1}` in `(ℤ⟦X⟧)⟦Y⟧` via
`PowerSeries.inv` (verified), but adds a 2nd formal variable — prefer single-variable unless it stalls.
Secondary risk: S3 triangle reindex — make it a reusable finite-convolution helper.

| file | content | lemmas | lines |
|---|---|---|---|
| `Core.QSeriesShift` | S1' + S2 + range-gap | ~5 | ~180–280 |
| `Core.QSeriesOrth` | `altP`, `altP_mul_one_sub`, `orth_recurrence`, `orth` | ~4 | ~150–250 |
| `Core.QSeriesThm55` | triangle-convolution helper, `thm55_zero`(S3), `thm55`(S4) | ~4 | ~150–250 |
| (into `CThetaPermInvariance`) | `Qseries_comp_perm`, `cCodim/numTop_comp_perm` | ~3 | ~60–110 |

**Total ~16 lemmas, ~540–890 lines.** Heavy reuse of LANDED `P_mul_one_sub_succ`,
`geomFactor_mul_one_sub`, `dropCorner` bijection, `codimForm_update_corner`, M5 bridge,
`Pmult_sub_comp_perm`. Build inline (serial, warm `.lake`). Order: `QSeriesShift` → `QSeriesOrth` →
`QSeriesThm55` → M6 capstone.

## 6. Close
- Firmest: Thm 5.5 reduces to an elementary substitution chain (S1'→S2→S3→S4), only classical q-input is
  ORTH (self-contained single-var induction on LANDED `P_mul_one_sub_succ`). Cor 5.10 closes per-`r` for
  all `r` via the LANDED M5 bridge + `Pmult_sub_comp_perm`. All exact-verified (monotone/non-monotone/
  zeros/all `r`/all perms).
- S3 verdict: Lean-tractable, NO mini-library.
- Most likely to break: `orth_recurrence`'s `sum_range_succ'` bookkeeping (de-risked: M2 `B_sum_desc`
  precedent + truncated-`Y` fallback). S3 triangle reindex (de-risk: reusable helper).
- Next: write `Core.QSeriesShift` first (lowest risk, unlocks S2), then `QSeriesOrth`, `QSeriesThm55`, M6
  capstone. If `orth_recurrence` stalls >1 session → truncated-`Y` `PowerSeries.inv` route.

**Precision note (controller-flagged):** this cert produces a `cCodim`/`numTop` (combinatorial
codimension / component-count) permutation-invariance result, NOT an `rlct` result — the `rlct=½·codim`
reading stays Cited (Aoyagi/Watanabe). Name the M6 capstone `cCodim_comp_perm`/`numTop_comp_perm`, never
`rlct_…`.

### Artifacts (committed 1069c96, `scratch/`, exact-rational, 0 float)
verify_s3.py · verify_chain_s1s4.py · verify_s3_clean.py · verify_codex_orth.py · verify_s1_bijection.py ·
verify_range_gap.py · verify_m6.py · (orthogonality exploration: verify_orthogonality_route.py,
verify_orth_induction.py, verify_orth_shift.py, verify_qbinom_funceqn.py, verify_orth_direct.py) ·
codex/s3-{prompt,answer}.md.
