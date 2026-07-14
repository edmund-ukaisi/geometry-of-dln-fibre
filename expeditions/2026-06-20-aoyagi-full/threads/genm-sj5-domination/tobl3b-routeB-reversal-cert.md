# T-Obl3b Route-B "peel the better end" — REFUTED + reversal-CoV soundness cert

**Seat:** pen-and-paper (design-space math, one truth-value, decorrelated), aoyagi-full Stage 2,
`genm-sj5-domination`. **Date:** 2026-07-13. **NO Lean edits, NO git, NO build.** Exact integer
arithmetic for the load-bearing classification (`minAdm` layer-peel recursion, pivot-block map rank,
co-minimizer ranks); exact-rational Gaussian elimination for the independent pivot-rank check; Monte-Carlo
/ float only as a guide. Decorrelated `local-codex-consult` (xhigh, conclusion WITHHELD, framed
"adjudicate either direction"): `codex/tobl3b-routeB-reversal-{prompt,answer}.md`. Scripts (this dispatch, banked at `scripts/routeB/`):
`routeB_sweep.py`, `routeB_refine.py`, `routeB_crux.py`, `routeB_recursion.py`,
`routeB_robust.py`, `waist_char.py`, `verify_codex.py`.

**The ONE truth-value.** Does every nondegenerate `≥3`-width DLN chain `M` have a front-OR-back END whose
head-split front-peel avoids the divergent off-sector — so that, via the exact reversal symmetry
`I(M)=I(reverse M)`, `(□)`-finiteness for ALL `M` reduces to the `M₂≤M₁`-scoped mountain we can already
build (route B, the cheapest complete cover)?

---

## ★ HEADLINE VERDICT — **REFUTED. Route B is DEAD; route A (finer `Z_deep`-stratification) is FORCED.**

- **The claim FAILS.** The minimal counterexample is **`M=(2,1,2)`** — a nondegenerate 3-width chain
  (all widths `≥1`, `≥3` widths) that is head-split divergent from **both** ends. It is a palindrome, so
  `reverse M = M`: reversal offers no second orientation, and there is no third symmetry (tobl3b Q2:
  reversal is the ONLY measure-preserving CoV).

- **The real divergence boundary is the PIVOT criterion**, `u·ρ ≥ minAdm(redChain u M)` with
  `ρ = min(M₁,…,M_L)` (the naive min-tail-width — the C_hle criterion), **NOT** the corank criterion.
  The pivot block genuinely diverges for the head-split ROUTE (C_hle §5, exact map rank `= u·ρ`, verified
  independently here over ℚ — not an under-certified floor). The corank criterion is a strictly weaker
  bound artifact. **This is the crux the brief flagged**, and it reverses the tobl3b cert's route-B hope:
  that "0/764 both-ends-divergent" was computed under the CORANK criterion; under the binding PIVOT
  criterion route B fails.

- **The co-minimizer does NOT rescue the pivot block** (0/35 rescued, exact): at every both-ends-bad
  chain's failing cut, either the binding cut is **degenerate** (`b★=M₁−t★=0`, so the co-minimizer's
  `a,b≥1` hypothesis fails — 8/35) or, at a nondegenerate cut, `u·ρ < minAdm(redChain u M)` **even with
  the optimistic co-minimizer deep rank** (27/35), because the pivot codim is `u·ρ` and the waist forces
  `u` small — no `ρ` compensates a small `u`.

- **Clean structural theorem (Codex's, exhaustively verified).** Two-ended head-split obstruction occurs
  **ONLY for 3-width chains**, exactly the **strict-waist triples `(x,y,z)` with `y < min(x,z)`**. For
  `≥4` widths, front-failure forces `M₁ < M_{L-1}` while back-failure forces `M_{L-1} < M₁` — impossible;
  so every `≥4`-width chain has a head-split-good top end. **But this does NOT save route B**: the
  recursion is FORCED to descend into 3-width waist chains (1506+ `≥4`-width chains are top-good from an
  end yet not transitively dischargeable — every peel path leads into an irreducible waist).

- **The reversal CoV `I(M)=I(reverse M)` is SOUND** (transposition + factor-reversal, `|det|=1`,
  frobSq/box invariant, zero target fixed) and **Lean-adjacent**: the combinatorial half
  `minAdm(reverse M)=minAdm(M)` is banked (`minAdm_comp_perm` at `σ=Fin.rev`, 0/55944 numeric violations);
  the integral half is a small new lemma with a KNOWN measure-diamond friction. It is sound **regardless**
  of the route-B verdict — route B needs strictly MORE than reversal (a good end, which `(2,1,2)` lacks).

---

## Part 1 — The precise claim + the real divergence boundary (which criterion)

### 1.1 Setup (banked semantics, matching Lean exactly)

A chain `M=(M₀,…,M_L)` (`L+1` widths, `L` matrices). `minAdm` is the layer-peel recursion
(`RouteMLayerSplit.minAdmRec`, banked sorry-free):
`minAdm(n,m)=nm`; `minAdm(M)=min_{0≤t≤min(M₀,M₁)}[(M₀−t)(M₁−t)+minAdm(redChain t M)]`,
`redChain t M = (t,M₂,…,M_L)`. A **binding cut** `t★` attains the min. `reverse M = M∘Fin.rev = (M_L,…,M₀)`.

At chain `M`, binding cut `t★`, front-rank shell `u=t★+j` (`a=M₀−u`, `b=M₁−u`), the head-split resolution
carries two sub-integrals:
- **PIVOT block** (C_hle cert §1–§4): finite up to the reduced comparator `½·minAdm(redChain u M)` **iff**
  `u·ρ ≥ minAdm(redChain u M)`, where `ρ = rank(Q) = min(M₁,M₂,…,M_L)` is the generic rank of the deep-tail
  product `Q` (shape `M₁×M_L`). C_hle verified this rank is EXACT (`chle_mc.py`, `match=True` all rows) —
  an actual rank, not a bound.
- **CORANK block** (tobl3b cert §3.1, S1 §B.2b): the cheap single-shell bound converges iff
  `floor ≥ a+b`, `floor = M₂` (`L=0`) else `min(M₁,M_L)−j`. This UNDER-counts — the co-minimizer
  `ρ_comin ≥ a★+b★−1` makes the TRUE corank integral finite even when it fails (bound artifact).

### 1.2 The real boundary: PIVOT, not CORANK (crux resolution)

**[FACT]** Over widths `1..6`, lengths `3..6` (55944 chains): the pivot wall is a **strict superset** of
the corank wall — `{corank-fails ∧ pivot-ok} = 0`, `{pivot-fails ∧ corank-ok} = 6844`
(`routeB_sweep.py`). So the two S1-mountain sub-integrals fail on a nested pair of sets, pivot the larger.

**[INFERENCE, C_hle §5-anchored]** The pivot-block divergence is a GENUINE obstruction of the head-split
ROUTE (the specific chart/comparator cannot deliver the reduced threshold `½·minAdm(redChain u M)`), not a
bound artifact — its threshold is the EXACT map rank `u·ρ`. The corank-block "divergence" is a bound
artifact (the true corank integral is finite). Therefore **what the S1-mountain-as-built can cover is
gated by the PIVOT criterion**; the corank criterion is a distraction here. The brief's own criterion form
`u·ρ_minwidth ≥ minAdm(redChain u M)` IS the pivot criterion — and it is the right one.

**[FACT, independent exact ℚ rank check — `routeB_crux.py` CRUX 2]** For the minimal counterexamples, the
pivot-map `(P,B₁₂) ↦ P·Q_p + B₁₂·Q_b` (a generic deep product `Q`, exact-rational Gaussian elimination
decorrelated from `chle_mc.py`) has rank exactly `u·ρ`:

    (2,1,2) @ u=1: rank 1 = u·ρ,  minAdm(redChain)=2  ⇒ codim 1 < 2  (diverges)
    (3,2,3) @ u=1: rank 2 = u·ρ,  minAdm(redChain)=3  ⇒ codim 2 < 3  (diverges)
    (3,2,4) @ u=1: rank 2 = u·ρ,  minAdm(redChain)=4  ⇒ codim 2 < 4  (diverges)
    (4,2,4) @ u=1: rank 2 = u·ρ,  minAdm(redChain)=4  ⇒ codim 2 < 4  (diverges)

### 1.3 "front-good", precisely

`M` is **front-good** iff at every binding cut `t★` and every front-rank shell `u≥t★` (`u≥1`) the pivot
criterion `u·ρ ≥ minAdm(redChain u M)` holds. Two defensible **shell readings** (Codex flagged the
ambiguity, adjudicated under each):
- **STRICT** (binding-cut main peel `j=0` + proper off-sectors `a,b≥1`): both-ends-bad = **35** chains.
- **ALL-SHELL** (every `u∈[t★,min(M₀,M₁)]`, `u≥1`, including `b=0` shells) = Codex's reading:
  both-ends-bad = **55** chains.

**The verdict, the minimal counterexample `(2,1,2)`, and "only 3-width" are INVARIANT across both readings**
(and a third `bind-only` reading: 29). `(2,1,2)` is both-ends-bad under all three (`routeB_robust.py`).

---

## Part 2 — REFUTED: the counterexamples + the clean structural theorem

### 2.1 Minimal counterexample `(2,1,2)` (hand-verified)

`minAdm(2,1,2)`: `t=0: 2·1+minAdm(0,2)=2`; `t=1: 1·0+minAdm(1,2)=0+2=2`. **Both `t=0` and `t=1` bind.**
`ρ = min(M₁,M₂) = min(1,2) = 1`. At the binding cut `t★=1`: `t★·ρ = 1·1 = 1 < minAdm(redChain 1 M) =
minAdm(1,2) = 2` ⇒ **pivot diverges at the MAIN peel.** Concretely the pivot integral is `∫_{[−T,T]}
|c·P|^{−2c''} dP` (`c=|Q|≠0`), finite iff `c''<½`, but the reduced chain `(1,2)` needs `c''` up to
`minAdm(1,2)/2 = 1`. Diverges on `c''∈[½,1)`. Palindrome ⇒ `reverse M = M` ⇒ back identical. Route B stuck.

The waist `M₁=1` forces `b★ = M₁−t★ = 0` (degenerate binding cut): the co-minimizer (`a,b≥1`) does not
even apply. The `M₁=1` bottleneck starves the deep rank AND the pivot rank `u`.

### 2.2 The co-minimizer non-rescue, exact (`routeB_crux.py` CRUX 1)

Over all 35 both-ends-bad chains, at the first failing cut: **8** are at a degenerate binding cut
(`a★|b★=0`, co-minimizer N/A); **27** are at a nondegenerate cut where `u·ρ_opt < minAdm(redChain u M)`
even with `ρ_opt = min(max(min-width, a★+b★−1), tailMin)` (the best deep rank the co-minimizer allows);
**0** rescued. For `(3,2,3)`: nondegenerate (`a★=2,b★=1`), co-minimizer gives `ρ≥a★+b★−1=2` which MATCHES
the actual `ρ=2`, and `u·ρ = 1·2 = 2 < 3` regardless — the pivot rank `u=t★=1` is the bottleneck.
(Codex independently reproduced both computations and flagged that "deep rank `≥ a+b+1`" cannot mean the
literal `M₂×M_L` matrix rank in these examples — it is a resolution-rank statistic; this does not touch the
pivot, whose `ρ` is by definition the actual generic matrix rank.)

### 2.3 The clean structural theorem (Codex, exhaustively verified — `verify_codex.py`)

Let `R_f(M) = min(M₂,…,M_L)`.

**[FACT] Upper-bound lemma:** `minAdm(M) ≤ M₀·min(M₁,…,M_L)` for every chain (0 violations, widths `1..7`,
lengths `2..6`). [The `t` split that kills each of the `M₀` leading columns through the bottleneck.]

**[FACT] front-good sufficient condition:** if `M₁ ≥ R_f` then `ρ = R_f` and, for every shell `u`,
`minAdm(redChain u M) ≤ u·R_f = u·ρ` (upper-bound lemma applied to `(u,M₂,…,M_L)`), so the pivot passes.
Contrapositive: **front-bad ⟹ `M₁ < R_f = min(M₂,…,M_L)`** (0 violations).

**[FACT] Only 3-width:** for `≥4` widths, front-bad ⟹ `M₁ < M_{L-1}` (since `M_{L-1}∈{M₂,…,M_L}`) and
back-bad ⟹ `M_{L-1} < M₁` — contradiction. So **both-ends-bad occurs only at 3 widths** (0 both-ends-bad
`≥4`-width chains; 35 at 3 widths — matches Part 1.3 exactly).

**[FACT] Exact 3-width family (all-shell reading):** `(x,y,z)` is both-ends-bad **iff `y < min(x,z)`**
(strict interior waist). Minimal `(2,1,2)`. Palindromic subfamily `(r,s,r)`, `s<r`. (Under the STRICT
reading, waist triples whose binding cut is `t★=0` with only a `b=0` shell — e.g. `(2,1,3)` — escape; the
both-ends-bad subset is the 35 of Part 1.3. `(2,1,2)` is in both.)

### 2.4 The transitive failure — the good top end does NOT save route B

**[FACT, `routeB_recursion.py` + `verify_codex.py`(d)]** A chain is **route-B dischargeable** iff some
orientation is top-good AND (recursively) every reduced chain over that orientation's binding cuts is
dischargeable (all binding cuts must be covered — different cuts = different top-dim components). Over
widths `1..6`, lengths `3..6`: **8653 chains are NOT route-B dischargeable**. Of these, **1506** are
`≥4`-width chains that ARE top-good from an end but are FORCED to descend into an irreducible 3-width waist
(e.g. `(2,1,2,2)`, `(2,1,2,3)`, `(2,1,3,2)` ⤳ `(2,1,2)`). Every stuck chain has a strict interior waist;
the waist counterexamples `(2,1,2)`, `(3,1,3)`, `(3,2,3)` also arise as `redChain` of wider chains
(`(2,2,1,2)⤳(2,1,2)`, etc.), so forbidding them as roots is not an option.

**Conclusion:** route B is dead both at the root (3-width waists) and transitively (forced waist descent).
Route A — the finer `Z_deep`-direct stratification of tobl3b §3 cover (A) — is FORCED.

---

## Part 3 — Reversal CoV soundness + Lean-adjacency (task item 3)

**[FACT] Sound.** For `M` with factors `A₀,…,A_{L-1}` (product `P = A_{L-1}···A₀`), set `B_i := A_{L-1-i}ᵀ`.
Then `B_{L-1}···B₀ = A₀ᵀ···A_{L-1}ᵀ = (A_{L-1}···A₀)ᵀ = Pᵀ`. The map `(A_i) ↦ (B_i)` is a linear
bijection of the parameter box for `M` onto the box for `reverse M`, and:
- transpose + factor-reindex merely PERMUTE scalar coordinates ⇒ the cube `[−T,T]^{·}` is preserved
  exactly (the box for a factor `M_{i}×M_{i+1}` maps to the box for the reversed factor `M_{i+1}×M_i`);
- `‖Pᵀ‖_F² = ‖P‖_F²` ⇒ the loss (frobSq of the product) is invariant;
- the zero target `B=0` is fixed (for a NONzero target one must transpose the target too — flag);
- the Jacobian is `±1`, `|det| = 1`.

Hence `I(M,c) = I(reverse M, c)` as an equality of extended-`ℝ≥0` integrals (even if either side is `⊤`).
Codex independently reconstructed this verbatim (Q4).

**[FACT] Lean-adjacency.**
- **Combinatorial half** `minAdm(reverse M) = minAdm(M)`: banked — `reverse M = M ∘ Fin.rev`, `Fin.rev` is
  an `Equiv.Perm`, so `minAdm_comp_perm Fin.rev M` closes it (one line). Numeric sanity 0/55944 violations.
- **Integral half** `I(M,c) = I(reverse M,c)`: a small NEW lemma, ingredients present. `Matrix.transpose_mul`
  (iterated / `transpose_list_prod`) for the product reversal; `frobSq` transpose-invariance (a
  `Finset.sum` reindex); the measure CoV via a `|det|=±1` linear equiv. **Known friction:** it hits the
  matrix-space measure instance DIAMOND (`Matrix.module` vs `NormedSpace.toModule`, per `lean/CLAUDE.md` /
  `RouteMSJDecoratedPeelMeas`) — the transpose CoV must be transcribed over the RAW pi type (the banked
  workaround). Small, not free; the pattern is banked.

**The reversal is sound but insufficient for route B.** Route B needs a good END; `(2,1,2)` (and the
whole waist family) has none, and reversal only ever offers the two orientations `{M, reverse M}`.

---

## Numeric ledger (exact classification; MC/float guides only)

- `routeB_sweep.py` — widths `1..6`, lengths `3..6` (55944 chains): pivot wall ⊋ corank wall
  (`corank-only=0`, `pivot-only=6844`); both-ends-bad: PIVOT 55, CORANK 0, BOTH(S1-as-built) 55.
- `routeB_refine.py` / `routeB_robust.py` — STRICT reading 35 both-ends-bad (25 up to reversal, all
  3-width); minimal `(2,1,2)`; `(2,1,2)` both-ends-bad under bind-only/strict/all-shell (29/35/55).
- `routeB_crux.py` — co-minimizer rescue 0/35 (8 degenerate cut, 27 `u`-starved); independent ℚ
  pivot-rank `= u·ρ` on `(2,1,2)/(3,2,3)/(3,2,4)/(4,2,4)`.
- `routeB_recursion.py` — 8653 not-transitively-dischargeable; all have a strict interior waist; waist
  chains arise as `redChain` of wider chains.
- `verify_codex.py` — upper-bound lemma 0 violations; front-bad ⟹ `M₁<R_f` 0 violations; both-ends-bad
  `≥4`-width = 0 / 3-width = 35; transitive `≥4`-width top-good-but-stuck = 1506.
- `waist_char.py` — the STRICT-vs-all-shell mismatch is exactly the `t★=0`/`b=0`-shell chains (`(2,1,3)`).
- `minAdm` reversal-invariance 0/55944 (`minAdm_comp_perm` at `Fin.rev`).

---

## Decorrelated Codex (conclusion WITHHELD; prompt framed "either direction")

`codex/tobl3b-routeB-reversal-{prompt,answer}.md` (xhigh). CONCURS on all four, decorrelated (the prompt
carried the two criteria + reversal facts, but WITHHELD my verdict, the minimal counterexample, and the
"only 3-width" claim):
- **Q1** PIVOT criterion is the route boundary; corank failure ≠ divergence. Matches Part 1.2.
- **Q2** co-minimizers do NOT rescue PIVOT; computed `(2,1,2)`/`(3,2,3)` matching mine; SHARPENED that
  "deep rank ≥ a+b+1" cannot be the literal `M₂×M_L` matrix rank (a resolution-rank statistic) — folded
  into §2.2.
- **Q3** NO; smallest counterexample `(2,1,2)`; PROVED the clean structure independently — front-bad ⟹
  `M₁<R_f` via the upper-bound lemma; two-ended only at 3 widths; exact family `y<min(x,z)`. This is a
  decorrelated PROOF, not just concurrence; I verified all its facts exhaustively (§2.3).
- **Q4** reversal sound; flagged the nonzero-target transpose caveat. Matches Part 3.

Codex's "most likely wrong" surface: the shell-coverage reading (which `u` the route must cover). I
adjudicated the verdict INVARIANT across all three readings (§1.3), so the ambiguity does not move the
refutation.

---

## Close

- **Firmest result.** Route B is **REFUTED**. Minimal counterexample **`(2,1,2)`** (palindromic 3-width
  waist, head-split divergent from both ends; hand-verified `t★=1` pivot codim `1 < minAdm(1,2)=2`). The
  real divergence boundary is the **PIVOT criterion** `u·min(M₁,…,M_L) ≥ minAdm(redChain u M)` (the genuine
  head-split ROUTE wall; corank is a strictly weaker bound artifact); the co-minimizer does NOT rescue it
  (0/35). Clean theorem (Codex-proved, exhaustively verified): two-ended obstruction occurs ONLY for
  3-width strict-waist triples `y<min(x,z)`; for `≥4` widths a good top END always exists but the recursion
  is FORCED into a waist (1506 stuck). **Route A (finer `Z_deep`-stratification) is forced.** The reversal
  CoV `I(M)=I(reverse M)` is SOUND and Lean-adjacent (combinatorial half banked via `minAdm_comp_perm`;
  integral half a small new lemma with the known measure-diamond friction) — but insufficient for route B.
- **Most likely to break it.** (i) A definition slip: if the head-split resolution does NOT in fact need
  to cover the `b=0` / degenerate-binding-cut shells (a narrower shell obligation than any of my three
  readings), the 3-width waist set could shrink — but `(2,1,2)`'s failure is at the MAIN peel `t★=1`
  (`b★=0` there is intrinsic to the waist, not an off-sector artifact), so it survives. (ii) If a route
  DISTINCT from head-split (not front-peel, not reversal) could discharge a waist chain within the banked
  method — but that is route A by another name, not route B.
- **Next construction / consult.** Route A step 4 (tobl3b §3.2): the codimension-retaining stratified
  additivity across `Z_deep`-rank shells for the 3-width waist family (and its forced appearances mid-
  recursion) — the one place the residual labour lives. The clean 3-width `y<min(x,z)` characterization
  gives route A a SMALL, sharply-scoped hard core to target (resolve the waist bottleneck directly), rather
  than an open-ended `M₂>M₁` regime. Recommend the controller retire route B and scope route A around the
  waist family.
