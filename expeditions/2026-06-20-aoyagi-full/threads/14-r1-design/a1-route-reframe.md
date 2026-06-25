# A1 #19 route reframe + perm-invariance validation

- **Seat:** `pp` (design). **Read-only; /tmp scratch; no Lean.** Task #11/#19.
- **Trigger:** the A1 statement-card's route **step 3 ("per-c lower bound") was the FALSE `min_c`
  reading** (fm + agent surfaced it). The STATEMENT (candidate d, `∃ℓ, lambdaCore M = cleanCore ℓ
  (sortedSmallest M ℓ)`) is correct + total (1360/1360); only the ROUTE's step 3 was wrong. This
  reframes the route and VALIDATES the perm-invariance keystone before fm invests ~250-350 lines.
- **Note:** the decorrelated Codex consult on this (perm-inv provability) FAILED (exit 144, no
  answer). My findings below are independent exact-algebra (validated, not Codex-dependent); a Codex
  cross-check is still desirable and can be re-fired.

## 1. Why step 3 was false (the `min_c` / monotonicity trap)

`cleanCore` is **NOT monotone in the widths** (confirmed: `s=[1,2,4]`→`clean2`=2 vs `[1,2,7]`→−2; and
my earlier `[1,1,4]`: `cleanCore(2,[1,1,4])=0 < lambdaCore=1/2`). So **both** `min_ℓ` and `max_ℓ` of
`cleanCore ℓ (ℓ+1 smallest)` are FALSE readings of `lambdaCore`. The route must NOT route the lower
bound through any monotonicity/extremum of `cleanCore` over widths.

## 2. Perm-invariance keystone — VALIDATED (true) + provable, but as a COROLLARY

**`lambdaCore M = lambdaCore (M∘σ)` for every permutation σ — VALIDATED** exactly
(`/tmp/a1_perminv.py`): 0 perm-variant classes over all width-multisets (Lp1=2..4, entries 0..4).
True despite `Adm` and `Mval` being POSITIONAL in `M`.

**Provability + the right dependency direction (the key finding — reverses the proposed route):**
- The natural "prove perm-inv first via an `Adm(M) ≃ Adm(M∘σ)` Mval-preserving cone bijection" is the
  HARD ~250-350-line beast (the cone reshapes under σ; the bijection is intricate). **Do NOT do this
  first.**
- Instead: `min_T Mval(M,T)` depends only on the **MULTISET** of widths, because it equals
  `2·cleanCore(ℓ*, ℓ*+1 SMALLEST widths)` for the achiever ℓ* (verified: 0 fails / 3900 cases with the
  EXACT Lean defs `cleanCore=¼(Σq²−Σm²)`, `lambdaCore=½ min Mval`) — and "ℓ+1 smallest" + the balanced
  split are **order-free / symmetric** in `M`. So `lambdaCore M = F(multiset{M^s})`.
- ⟹ **perm-invariance is a COROLLARY of the sorted-form characterization (#19)**, not its prerequisite.
  Prove `#19-on-sorted-M` (lambdaCore = cleanCore at the smallest widths); perm-inv falls out
  (`F` depends only on the multiset). **This is the cheaper dependency order** — it avoids the cone
  bijection entirely.

(If a standalone `lambdaCore_perm_invariant` is wanted as a lemma, derive it FROM the sorted
characterization: `lambdaCore M = lambdaCore (sort M)` for both `M` and `M∘σ` since `sort(M)=sort(M∘σ)`.
That is a one-liner once the sorted characterization is in hand — NOT a separate 250-line proof.)

## 3. The reframed route (replaces card step 3) — does it CLOSE #19?

Target: `∃ ℓ ∈ {1..L}, lambdaCore M = cleanCore ℓ (sortedSmallest M ℓ)`.

**Reduce to sorted M** (perm-inv, now a corollary — or just `lambdaCore M = lambdaCore (sort M)` and
`sortedSmallest` is already sorted-based). WLOG `M` ascending.

**UPPER bound** `lambdaCore M ≤ cleanCore(ℓ*, smallest)` (the achiever, easy): construct
`T* ∈ Adm(M)` from the balanced split on the `ℓ*+1` smallest widths; `Mval(M,T*)/2 =
cleanCore(ℓ*, smallest)`. [`balancedSplit_min` gives the value; admissibility of `T*` is the
construction.]

**LOWER bound** `lambdaCore M ≥ cleanCore(ℓ*, smallest)` (the crux, the corrected step 3): EVERY
admissible `T` satisfies `Mval(M,T)/2 ≥ cleanCore(ℓ*, smallest)`. The route (NOT via cleanCore
monotonicity):
1. **per-T balanced-split bound:** for `T` with `ℓ_T` levels at breakpoint widths `W_T` (a
   submultiset of `M`), `Mval(M,T) ≥ 2·cleanCore(ℓ_T, W_T)` — the completed-square form (design-spec
   §4.3) + `balancedSplit_min` (PROVEN): T's heights deviate from the balanced split, raising `Mval`.
2. **smallest-widths reduction (sorted M):** `cleanCore(ℓ_T, W_T) ≥ cleanCore(ℓ*, smallest)` =
   `lambdaCore` — because on SORTED M the minimum over (ℓ, achievable breakpoint widths) is attained
   at the front (smallest widths): the `Mval` factors `(M^{S}−H)` REWARD small `M^S` (smaller widths
   ⇒ smaller product terms), so a minimizer's breakpoint widths are pushed to the smallest. This is
   NOT cleanCore-monotonicity (false); it is the minimisation over the ACTUAL `Adm` cone reduced to
   the smallest-widths achiever.

**Does it close #19?** YES in principle (UPPER + LOWER ⟹ equality at ℓ*), with one **load-bearing
sub-lemma to nail in the formalisation:** step 2's "minimizer's breakpoint widths = the ℓ*+1 smallest
on sorted M". This is *forced* (not just achievable) — the lower bound needs it for EVERY T. I verified
the END claim (0 fails / 3900) but the per-T forcing is the genuine content fm must prove. Flag:
**this is the residual hard step**, and it is where the prior false `min_c` lived — it must be the
per-T-over-the-Adm-cone argument, not a widths-extremum.

## 4. Gaps / honest flags (validate-before-investing)

1. **The per-T lower bound (step 2 above) is the crux and the residual hardness.** It does NOT follow
   from cleanCore monotonicity (false). It needs: completed-square + balancedSplit_min (per-T) + the
   "smallest widths win on sorted M" forcing. The last is the ~real work; estimate it dominates the
   line count, not perm-inv.
2. **Perm-inv is CHEAP if done as a corollary of the sorted characterization** (not the cone
   bijection). So the ~250-350-line worry should be re-budgeted: most of it is the per-T lower bound
   (step 2), NOT perm-inv. If fm was about to prove perm-inv via the cone bijection FIRST, redirect:
   prove sorted-M #19, get perm-inv free.
3. **L=1 edge:** `lambdaCore([M⁰,M¹]) = ½ M⁰M¹ = cleanCore(1,[M⁰,M¹])` (`= ¼·2M⁰M¹`) ✓ — the ℓ=1
   case fits (factor checked; my earlier scratch had a ×2 `clean2` slip, corrected — the EXACT Lean
   defs match, 0 fails).
4. **Does the achiever ℓ* need a definable formula?** NO — the statement is `∃ℓ` (the achiever exists;
   non-unique is fine). The construction (UPPER) exhibits one; the LOWER shows none beats it. No
   `ℓ*(M)` function needed.

## 5. Recommendation

- **Reframe card step 3** to: per-T balanced-split bound (`Mval(M,T) ≥ 2 cleanCore(ℓ_T, W_T)`) +
  smallest-widths-win-on-sorted-M (the forcing) — NOT the `min_c` reading. [Patch applied to this
  card; the a1-statement-card.md step 3 should point here.]
- **Perm-invariance:** prove it as a COROLLARY of the sorted characterization (one-liner via
  `sort M = sort (M∘σ)`), NOT a standalone cone bijection. Re-budget the ~250-350 lines: the bulk is
  the per-T lower bound, perm-inv is cheap.
- **The route CLOSES #19** modulo the one residual sub-lemma (smallest-widths forcing at the
  minimizer) — sound, verified end-to-end (0 fails), no monotonicity smuggled. Fm proves against this.
- Re-fire the Codex cross-check on the per-T forcing if desired (the consult failed exit-144; my
  analysis is independent).
