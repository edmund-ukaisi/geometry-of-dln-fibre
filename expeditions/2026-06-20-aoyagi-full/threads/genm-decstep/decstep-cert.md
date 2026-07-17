# decstep — is `DecoratedStepHyp` provable natively (the weighted-IH FaithfulSJAt peel), especially at the square u≥3 waist?

**Seat:** pen-and-paper, aoyagi-full `genm-decstep`. **Date:** 2026-07-16. **NO Lean edits, NO build.**
Exact-ℕ (`minAdm` recursion = Lean's `minAdmRec`; joint rank-`r'` codim `C_k`; Wishart/qbox convergence)
+ structural CoV reasoning. Decorrelated `local-codex-consult` (gpt-5.x xhigh, my conclusion WITHHELD):
`codex/crux-{prompt,answer}.md`, `crux-run.log`. Decorrelated from q2gate/satred/couplerad — I formed the
verdict independently and it CONVERGES with (and sharpens) theirs.

The single truth-value asked: **is `DecoratedStepHyp adm` (`RouteMSJDecoratedRec.lean:144`, `adm =
genuineCarrier ∧ FaithfulSJAt`, `RouteMSJAdm.lean:194`) provable natively — the weighted/decorated
FaithfulSJAt peel — ESPECIALLY at the square `u≥3` waist where the plain IH provably fails — or is it the
genuine `(□)` wall?**

---

## ★ ROUND-2 RESOLUTION (2026-07-17): the gap is SELF-SIMILAR-BOUNDED → BUILD NATIVE (option a)

The controller's deciding de-risk (is the `≥2×2` corank-block gap self-similar, or does the `C'·B₀`
coupling break it?) is **RESOLVED: option (a), SELF-SIMILAR-BOUNDED — build it natively, no cited-Aoyagi
step needed.** The `GAP-AT-CORANK-2` below is REAL but NATIVELY closable: it is a *detail-at-scale*
determinantal resolution (bounded, self-similar), not a monument. Full analysis + the flag-`γ'` design
sketch + preservation check in **§ ADDENDUM (round 2)** at the end. The round-1 verdict below stands as
the precise characterization of *what the current design lacks*; the addendum says *how to close it natively*.

## ★ VERDICT (round 1, sharp, two decorrelated lines converge)

**It is NOT a genuine `(□)` wall, and it is NOT plainly provable-as-designed. It is: `(□)` is TRUE
(Aoyagi — the integral IS finite, budget exactly tight), the DECORATED route ESCAPES the plain/coupled
Q2-obstruction at `n=3` — but the CURRENT `DecoratedStepHyp` design carries a GENUINE GAP that first bites
at a `≥ 2×2` corank block (smallest: the square `(4,4,4,4)`, corank `a=b=2`). The gap is the JOINT
rank/kernel incidence of the corank block `Γ` against the coupled tail `Q_b`; it needs an INTERNAL
determinantal / flag stratification (a nested blow-up of depth up to `⌈n/3⌉`) that (i) the single
radial-attach peel does NOT perform and (ii) the single-product `γ'` clause of `FaithfulSJAt` cannot
express. So: PROVABLE-IN-PRINCIPLE (Aoyagi guarantees the threshold; the budget is exactly tight and the
weight is the right object), but the honest status is `GAP-AT-CORANK-2` — a substantial multi-tide build
whose deepest content is the corank-block joint-incidence resolution, OR the cited-Aoyagi boundary.**

Both lines agree:

- **My exact-algebra line.** The decorated front-cover peels at the BINDING cut (dominant-minor cover),
  where the square corank block is `a=b=⌈n/3⌉`; for `n≥4` this is `≥2×2`, a genuine matrix corank whose
  `Γ·Q_b` singular locus is a determinantal variety; a single radial coordinate resolves only `Γ=0`, not
  the rank-1 cone `{rank Γ̂ ≤ 1, rank Q_b < b}`.
- **Codex xhigh (decorrelated, my verdict withheld).** `Verdict: GAP-AT-CORANK-2`. Q1 (budget) PROVEN
  exactly tight; Q2 the Wishart criterion holds for a FREE Gram but "`Q_b` is itself a product and shares
  deeper variables … does not prove joint integrability"; Q3 "PROVEN gap for a single radial blow-up …
  first occurrence `n=4, a=b=2`"; Q4 "Merely attaching the Gram determinant … is not a complete proof …
  one must … perform nested flag or determinantal blow-ups … or invoke Aoyagi directly."

Codex also corrected an arithmetic mis-statement of mine (checked, it is right): the square binding-cut
corank is **`⌈n/3⌉`**, not `⌊n/2⌋` (they coincide only at `n=4,5`; verified `n=2..15`). It still grows
unboundedly, so the internal-stratification depth is unbounded in `n`.

---

## 1. The decorated route peels at the BINDING cut, NOT the saturated waist (the key re-framing)

q2gate's `u≥3` obstruction is a property of the **coupled route's shell-cover** (`hbdryShell` at the
saturated shell `j=r`, `u=min(M₀,M₁)`, `a=b=0`, plain IH). The **decorated** driver
(`routeMBoxThresholdFinite_of_decoratedStep`) does NOT use that shell-cover. Its peel (per
`RouteMSJDecoratedPeelStep`) is the front cover `sjBoundaryPeel` — a sum over pivot cuts `t ∈ [1,
min(M₀,M₁)]` via the **dominant-minor** cover, each chart reducing to `redChain t M` at threshold
`½·minAdm M − ½·peelCharge M t`, closed by the (decorated) one-shorter IH.

- **The dominant-minor cover redistributes the density.** On the naive generic chart `{P invertible}`
  (`t = min = n`, `a=b=0`) the reduction `z̃₀ = P·z₀` carries the pushforward density `ρ(z̃₀)∉L⁴` — the
  q2gate obstruction. The dominant-minor cover moves each point to the chart of its LARGEST invertible
  minor, so on the `t=n` chart `|det P|^{−n}` is BOUNDED (away from rank drop) and the reduction is clean;
  the rank-drop singularity is redistributed to the `t<n` charts, where it re-appears as a corank-block
  GRAM at the binding cut `t★`.
- **The binding-cut chart is where the difficulty concentrates.** For square `(n,n,n,n)` the binding cut
  `t★` has corank `a=b=n−t★=⌈n/3⌉` (PROVED exact-ℕ). So the decorated route confronts, not the `a=b=0`
  saturated waist, but a `⌈n/3⌉×⌈n/3⌉` corank block.

**Consequence for `n=3`.** The recursion `(3,3,3,3) →_{t=2} (2,3,3) →_{t=1} (1,3)` has `min(a,b)=1` at
EVERY level (corank blocks `1×1` and `1×2`). A scalar/row corank block has NO internal rank strata (rank
`≤ 1` always), so the single radial-attach peel + the single-product `γ'` reduced decoration close it.
**⟹ the decorated route DOES escape the plain/coupled Q2-obstruction at `n=3`** (which is real only for
the un-decorated saturated shell). The FIRST decorated gap is `n=4`.

## 2. The budget is EXACTLY tight — no numerical deficit, so it is NOT a wall (Proved exact-ℕ)

At the binding cut, one peel spends `½·peelCharge = a·b/2` on the corank block and hands `½·minAdm(redChain
t★ M)` to the IH, and these SUM to `½·minAdm(M)` with NO slack (`carrierThreshold_shift` is EQUALITY at
`t★`). Worked, exact:

- `(3,3,3,3)`: `t★=2`, `½ + 5/2 = 3 = ½·minAdm`.
- `(4,4,4,4)`: `t★=2`, `a=b=2`, `2 + 7/2 = 11/2 = ½·minAdm`. (Codex's finer split `7/2 = 3/2 + 2`, so
  `2 + 3/2 + 2 = 11/2`.)
- `(5,5,5,5)`: `t★=3`, `2 + 13/2 = 17/2`. `(n,n,n,n)` in general telescopes exactly.

Independently, the JOINT rank-`r'` stratification of the middle product `Y=P·Z₀` (`n×n`, corank `k=n−r'`,
product-corank codim `C_k = k²−⌊k²/4⌋`) has per-chart threshold `(C_k + n·r')/2`, and
`min_{r'}(C_k+n·r')/2 = ½·minAdm(n,n,n,n)` EXACTLY (verified `n=2..8`; binding stratum `k*=2,2,3,4,…`).
The RLCT IS reached by the correct resolution — **so `(□)` is TRUE for square chains and there is no
threshold deficit for the decorated route to close.** (Cited: Aoyagi `rlct = ½·codim` — the integral is
finite for `c' < ½·minAdm`.)

## 3. Does the FaithfulSJAt weight EXACTLY compensate the corank-2 (`γ=1`, `ρ∉L⁴`) obstruction?

**Partly. It compensates the DENSITY POWER exactly (budget-tight) but NOT the JOINT INCIDENCE — a finer
obstruction the current carrier cannot express.**

- **The weight is the right object.** The plain-IH route Hölder-splits `ρ_ang ∈ L^p` (`p<4` at the
  corank-2 stratum ⟹ `q>4/3`), losing to `(3/8)minAdm(n,n,n) < ½minAdm(n,n,n,n)` (`n=3`: `21/8 < 3`).
  Keeping the corank Gram `det(Q_bQ_bᵀ)^{−a/2}` ATTACHED (rather than split off) removes exactly this
  artificial `p<4` loss — this is the FaithfulSJAt/decorated mechanism, and with it the budget is exactly
  tight (§2). In this sense the weight compensates.
- **But keeping it attached exposes a NEW obstruction (Argued, decorrelated ×2).** Integrating the corank
  block `∫dΓ (F+‖Γ·Q_b‖²)^{−c} ≍ det(Q_bQ_bᵀ)^{−a/2}·F^{−(c−ab/2)}` is valid ONLY where `Q_b` is full
  row rank. For a FREE `Q_b` the Wishart criterion `∫_{box}det(Q_bQ_bᵀ)^{−s} < ∞ ⟺ 2s < q−b+1` even
  covers its rank-deficient strata (Codex: `n=4`, `1 < 3/2`). **The failure is that `Q_b` is NOT free —
  it is itself a layer product coupling into `frobSq(B₀)` (the `C'·B₀+Γ·Q_b` weld term is a SUM, not a
  single product).** So the finiteness is a JOINT `(Γ,Q_b)` determinantal-incidence problem. For
  `min(a,b) ≥ 2`, the singular locus `{Γ·Q_b ≈ 0}` includes the rank-1 cone: `Γ↦Γ·Q_b` on `{rank Q_b =
  1}` has only `a·r = a` active directions (not `a·b`), so the angular quadratic on the radial exceptional
  divisor is NON-coercive — one radial coordinate does not resolve it (Codex Q3, PROVEN for a single
  radial blow-up; my structural argument concurs). This is the corank-2 `γ=1` obstruction in its true
  form: not a density-`L^p` failure (that is defeated by attaching the weight) but a JOINT incidence
  requiring a NESTED (flag) resolution.

## 4. The minimal gap (standing decision 7 — what is unprovable natively as-designed)

**`innerCorankDescent_lt_top` at `min(a,b) ≥ 2`: the finiteness of the freed-Γ triple integral where the
corank block `Γ` (`a×b`, `min(a,b)≥2`) couples to the tail `Q_b` (`b×q`, itself a layer product) below the
shifted threshold — i.e. the JOINT rank/kernel incidence of `Γ·Q_b`.** As designed the peel resolves this
by (i) a single radial attach on `Γ` and (ii) a single-product `γ'` reduced decoration (`residual = Γ·prod
(dropHead M)`, `gammaPrimeClause`); NEITHER expresses the determinantal flag `{rank Γ̂ ≤ 1} ∩ {rank Q_b <
b}`. Closing it natively requires ONE of:

- **(a) Strengthen `adm` + build the nested resolution.** Replace the single-product `γ'` with a FLAG /
  determinantal carrier (a nested `Γ·Q_b` incidence, resolvable across a per-peel INTERNAL determinantal
  stratification of the corank block — depth up to `⌈n/3⌉`, unbounded in `n`). This is a genuine
  determinantal-resolution theorem, the "genuinely-new heart". It is NOT the flat `cornerComparator`
  domination (which is L≥1-UNSOUND, `Z=t·Z₀` scaling — heeded; the sum-form weld `C'·B₀+Γ·Q_b` is exactly
  why a static single-product comparator cannot dominate), and it is NOT a single radial attach.
- **(b) Cite Aoyagi for the coupled corank-Gram step.** The corank-block joint-incidence finiteness IS an
  instance Aoyagi's determinantal RLCT computation resolves. Citing it here (rather than re-deriving via
  the decorated recursion) discharges the hole at the price of the `cited_aoyagi` interface — the
  cited-Aoyagi boundary sits EXACTLY at this step.

## 5. Scope of the gap — which chains hit it (Proved exact-ℕ)

The gap is `min(a,b) ≥ 2` at the binding cut — a **broad** set, not one square chain. Among arity-4 chains
with widths `≤ 6` (`M₀≤M₁`): **95** hit it, including square `(4,4,4,4),(5,5,5,5),(6,6,6,6)` AND many
rectangular ones (e.g. `(2,2,3,3)`, `(2,2,3,4)`, …). It also RECURS in reduced chains for larger `n`
(`(5,5,5,5)→(3,5,5)`: `min(a,b)=2` at BOTH levels; `(7,7,7,7)→(4,7,7)`: `3` then `2`). Only
`(4,4,4,4)→(2,4,4)` drops to `min(a,b)=1` after one peel.

**Non-square `u≥3` cases the controller flagged (likely NATIVE — no joint-incidence gap):**
- **Tall `b=0` (`M₀>M₁`):** the front `[P;C]` is FULL COLUMN RANK `M₁` (injective), so the Gram
  `det([P;C]ᵀ[P;C])^{−M₂/2}` is a NONDEGENERATE Wishart. It rarely one-shots (`M₂ ≤ a` needed; usually
  `M₂ > a`) so it RECURSES — but via a CLEAN per-level pivot-Gram fold (banked `qbox`, satred D-cert
  §3bis), NOT a joint pushforward-density incidence. **⟹ native (plain IH + qbox recursion); no weighted
  IH.**
- **Wide `a=0`, `b>0` (`M₀<M₁`):** the front `X=[P|B₁₂]` is FULL ROW RANK `M₀` (surjective). A
  full-row-rank front has a milder pushforward density (no square non-injective block). **⟹ likely native /
  milder; not the `≥2×2` joint incidence.** (Not fully adjudicated here — flagged.)

**So the weighted/decorated IH is needed EXACTLY for the genuine `≥2×2` (min(a,b)≥2) corank block** — the
square/near-square non-injective case. This sharpens q2gate's "square `u≥3`" to the precise trigger.

## 6. Levels kept apart

- **Quiver/orbit** — untouched; consumed via `minAdm`/`redChain`/`peelCharge`.
- **Codim `(C,θ)`** — `minAdm`, `C_k = k²−⌊k²/4⌋`, `a·b`, the budget sums are exact ℕ facts of the
  recursion; the joint rank-`r'` min `= ½minAdm` is exact-ℕ.
- **RLCT cap** — this works at `RouteMBoxThresholdFinite` (per-chart finiteness / box integral). The
  finiteness threshold `½minAdm` is Aoyagi-CONSISTENT; it is NOT a re-derivation of `rlct = ½·codim`. The
  cited-Aoyagi equality is invoked only in option (b) of §4 (to discharge the corank-Gram hole), never
  smuggled elsewhere.

## Close

- **Firmest result.** `DecoratedStepHyp adm` is NOT a `(□)` wall (Aoyagi; budget exactly tight, §2) and
  the decorated route genuinely ESCAPES the plain/coupled Q2-obstruction at `n=3` (scalar corank blocks
  throughout, §1). But as CURRENTLY designed it has a GENUINE GAP at `min(a,b) ≥ 2` (first `(4,4,4,4)`,
  `a=b=2`): the JOINT `Γ·Q_b` rank/kernel incidence, unresolved by one radial attach and inexpressible by
  the single-product `γ'` carrier (Argued, decorrelated ×2 — me + Codex xhigh `GAP-AT-CORANK-2`). It is
  PROVABLE-IN-PRINCIPLE via (a) a strengthened flag/determinantal carrier + a nested per-peel corank-block
  resolution (unbounded depth `⌈n/3⌉`, the genuinely-new heart, NOT the unsound `cornerComparator`
  flat-descent), OR (b) citing Aoyagi for the coupled corank-Gram step (the cited-Aoyagi boundary).
- **Most likely to break this call (both directions).** (i) If a formaliser builds the peel with a single
  radial attach + single-product `γ'` and claims it closes `(4,4,4,4)`, it will NOT (the rank-1 cone
  survives — do not ship it). (ii) The one INFERENCE (not a hard proof) is "the joint incidence needs a
  NESTED resolution the current design lacks" — corroborated by Codex's independent `GAP-AT-CORANK-2`
  + the exact `⌈n/3⌉` corank growth + the sum-form weld `C'·B₀+Γ·Q_b`, but a clever single-step CoV that
  linearises the incidence would refute it (unlikely — the determinant is genuinely `≥2×2`). (iii) I have
  NOT hard-proved that the strengthened flag carrier actually PRESERVES under the peel (cover's Q1 for
  `min(a,b)≥2`); that is the build's real risk, and the fallback (b) exists.
- **Next.** (a) A decorrelated de-risk of the INTERNAL corank-block determinantal stratification: is the
  corank-block finiteness `∫ frobSq(Γ·Q_b + coupling)^{−c'}` (an `(a,b,q)` sub-problem) itself an
  instance of the same decorated recursion (self-similar), so the nesting bottoms out — or does the
  `C'·B₀` coupling break self-similarity? (b) If self-similar, design the FLAG `γ'` (a nested product /
  incidence carrier) and re-audit `adm` for `min(a,b)≥2` preservation. (c) If not, take option (b) of §4
  (cite Aoyagi for the corank-Gram step) and consolidate the native `(□)` at `min(a,b) ≤ 1` + the two
  native non-square wings (§5), with the `min(a,b)≥2` corank-Gram step as the single cited interface.

Files (absolute):
- `…/threads/genm-decstep/decstep-cert.md` (this cert)
- `…/threads/genm-decstep/codex/crux-{prompt,answer}.md`, `crux-run.log` (decorrelated consult, `GAP-AT-CORANK-2`)
- exact-ℕ recomputations inline (reuse `…/threads/genm-q2gate/q2_arith.py`'s `minAdm` recursion; binding
  cut / corank `⌈n/3⌉` / gap-set / joint rank-`r'` `= ½minAdm` all recomputed and verified in this thread).

---

# ADDENDUM (round 2, 2026-07-17) — the deciding de-risk: SELF-SIMILAR-BOUNDED → build native (option a)

**Question (controller):** is the `≥2×2` corank-block finiteness SELF-SIMILAR (an `(a,b,q)` sub-instance
the arity-IH bottoms out → option (a), native nested build), or does the `C'·B₀` coupling BREAK
self-similarity on `{rank Q_b<b}` → option (b), cite Aoyagi? Decorrelated Codex (`codex/selfsim-{prompt,
answer}.md`, xhigh, my conclusion withheld) + my exact-ℕ, **both converge**.

## ★★ VERDICT: OPTION (a), SELF-SIMILAR-BOUNDED. Build the native determinantal corank descent; no cited-Aoyagi step needed.

The `C'·B₀` coupling remainder is **DROPPABLE** (PROVEN, exact-ℕ, decorrelated ×2): dropping it does NOT
lose the threshold. The corank descent is a *detail-at-scale* determinantal resolution — bounded,
self-similar, terminating — exactly the kind the disposition says to **build**, not cite (the monument to
cite stays the Aoyagi `rlct=½·codim` equality, unchanged; the `(□)` box-finiteness is native).

## 1. The coupling is droppable — PROVEN (exact-ℕ, both lines)

The freed Schur loss is `frobSq(F·Q)`, `F = [[P,0],[C,Γ]]` block-lower-triangular (pivot `P` invertible,
`C` free `a×t`, `Γ` free `a×b`), `Q` the tail `(t+b)×q`. It splits as
`frobSq(P·Q̃ₚ)` [pivot → reduced chain] `+ frobSq([C|Γ]·Q)` [corank residual — a FREE-front `(a, t+b, q)`
sub-chain]. Integrating the free `Γ` block and DROPPING the coupling remainder `frobSq(C'·B₀·Π)` (`Π =
I−Q_b⁺Q_b`, nonneg) gives the upper bound `det(Q_bQ_bᵀ)^{−a/2}·frobSq(B₀)^{−·}` — the det-Gram-weighted
reduced chain. Its threshold, via the joint rank stratification over `k = rank(deeper W)` and `r = rank Q_b`,

    2·T_{k,r} = (n−k)² + t*·k + (b−r)(k−r) + a·r   (codim{rank W=k} + codim{B₀=0} + codim{rank Q_b=r} + active Γ),
    min_{k,r} T_{k,r} = ½·minAdm(n,n,n,n) = c*   EXACTLY.

**Verified `n=3..15`** (my recompute of Codex's `T_{k,r}`, `min_{k,r} 2T = minAdm(n,n,n,n)`, 0 fails;
`codex/selfsim-answer.md` Q1 PROVEN independently). So **dropping the coupling reaches `c*`** — the
remainder is NOT load-bearing. The `{rank Q_b<b}` strata (my round-1 worry) are supplied by the lower-`r`
terms of the stratification, exactly where the round-1 route feared a gap. The critical-Wishart tie (e.g.
`n=4`, `k=3`, `r∈{1,2}`) is a log-boundary (harmless multiplicity), not a lower threshold.

## 2. Why it is SELF-SIMILAR and BOUNDED

- **Self-similar.** The corank residual `frobSq([C|Γ]·Q)` is a genuine DLN sub-chain `(a, t+b, q)` (free
  front `[C|Γ]`), an instance of `(□)` the arity-IH handles. The det-Gram weight `det(Q_bQ_bᵀ)^{−a/2}` is
  a decoration on the reduced chain `(t*, n, n)`, closed by the DECORATED IH.
- **Bounded termination** (Codex Q2, INFERENCE; I concur structurally). The lexicographic measure
  `(chain arity, corank c)` strictly decreases: an outer peel shortens the chain; the internal rank
  resolution shrinks the Gram (`c → r < c`). It bottoms out at the width-2 leaf (proven base
  `decoratedBaseHyp_faithful`), where the Gram is trivial. The determinantal resolution per peel is FINITE
  (finitely many ranks `0..c`); its SIZE grows as `c = ⌈n/3⌉` but is bounded for each fixed chain.
- **The Gram itself is native.** `det(Q_bQ_bᵀ)^{−a/2}` (`Q_b` `c×q`) is Wishart one-shot integrable when
  `2c ≤ q` — **holds for ALL square `(n,n,n,n)` binding cuts** (verified `n=3..15`: `2⌈n/3⌉ ≤ n`). When
  `2c > q` (e.g. `(2,2,3,3)`, `(3,3,5,5)` — 71 arity-4 chains ≤ width 8), the Gram RECURSES via the
  reduced-chain IH — satred's D-cert §3bis per-level pivot-Gram fold, the *same* structure satred banked
  for the `b=0` mirror (now needed for the `a=b≥2` both-corank case). Still self-similar; still bounded.

## 3. The genuinely-new heart (what to BUILD) — the determinantal corank descent + flag-`γ'` carrier

Round-1's `GAP-AT-CORANK-2` is real and stays: **one radial coordinate does NOT resolve a `c×c` corank
block for `c≥2`** (only the origin `Γ=0`, not the rank-`1..c−1` cone). The native fix is the FULL
multi-singular-value (SVD) determinantal resolution of the `c×c` Gram — `d = c` exceptional coordinates —
NOT a single `radialAttach`. Design shape (a sketch, not a Lean route):

- **flag-`γ'` carrier.** The current `gammaPrimeClause` (`RouteMSJAdm.lean:135`) carries `residual =
  Γ·prod(dropHead M)` — a SINGLE-front product. Strengthen it to a FLAG: `d = c` exceptional coords (the
  SVD singular values of the corank Gram) with `jac` monomial `= det(Q_bQ_bᵀ)` after R-blowup, and the
  residual the NESTED front `[C|Γ]·Q` (free front block × deeper tail product) — matching the resolution
  flag. The residual being the self-similar sub-chain `(a, t+b, q)` is what makes the flag = "reduced
  chain's `γ'` + one extra front level".
- **`β` threshold.** The SVD monomial's `monomialThreshold` `≥ ½·minAdm(reduced)` IS the Wishart criterion
  recast (`2·(a/2) < q−c+1` one-shot; else supplied by the Gram recursion). The budget identity `c²/2 +
  ½·minAdm(t*,n,n) = c*` (verified) is why `β` is exactly achievable.
- **Consume the banked bricks.** The full-rank `{Q_bQ_bᵀ PosDef}` stratum is the banked atom
  `corankBlock_morsePeel_lt_top` / `freedSchurLoss_inner_peel_lt_top` (`RouteMSJFreedPeel`), whose three
  interface hyps (`c'>ab/2`, `Q_bQ_bᵀ` PosDef, pivot energy `>0`) are exactly what the measure-level
  descent supplies a.e.; the `{rank Q_b<c}` strata recurse. This IS the `innerCorankDescent_lt_top` hole —
  now known to be native-closable, not cited.

## 4. The build's REAL risk (the one thing not hard-proved here)

**Preservation of the flag-`γ'` for `c≥2`.** The peel must map `flag-γ'(M, d)` → `flag-γ'(redChain t* M,
d+c)` (the `d` grows by the `c` new SVD coords each peel). Whether the SVD monomial + reduced product
satisfies `FaithfulSJAt`'s `β` + (flag-)`γ'` at every level — and whether the coupling-drop is realized
soundly at the MEASURE level (not just the pointwise budget) — is the genuinely-new content the build must
discharge. The exact-ℕ budget + Wishart gate + droppability are PROVEN; the measure-level CoV +
admissibility-preservation for the `c×c` determinantal blow-up is ARGUED (structural), not hard-proved. It
is *detail-at-scale* (decomposable, bounded), so **build it**; but it is the multi-tide heart, and the
`min(a,b)≥2` preservation is where to concentrate the soundness review.

## 5. The fallback (option b) — NOT needed, and even it is native

If the determinantal rank recursion were declined, the minimal object to bank/cite is the **UNCOUPLED
Gram-weighted reduced-chain finiteness** `∫ det(Q_bQ_bᵀ)^{−a/2}·frobSq(reduced)^{−c'} < ⊤` for `c'<c'`
below the shifted threshold — itself native (satred's qbox/Wishart family, `RouteMSJQBoxCore`), NOT a
coupled-incidence theorem (Codex Q3: the coupled integral is bounded by the uncoupled one, §1). So `(□)`
is native EITHER way; the only question is how much of the det-Gram recursion to build vs bank from satred.
There is NO genuine cited-Aoyagi step inside `(□)` — the Aoyagi citation stays where it always was: the
`rlct = ½·codim` equality (the monument), one level up from box-finiteness.

## 6. Net endgame call

**COMMISSION the native-nested build (option a).** The `(□)` capstone `DecoratedStepHyp adm` is native and
bounded: the corank descent is a determinantal (SVD) resolution + a flag-`γ'` carrier + the Wishart
one-shot/recurse dispatch, all self-similar and terminating; the coupling that looked load-bearing is
provably droppable; the Aoyagi monument is untouched. Concentrate the build + soundness review on the
`c≥2` flag-`γ'` preservation (§4). This keeps the full unconditional `∀-M` mint reachable and native
(the #97 mandate), rather than consolidating at a cited-corank-Gram boundary.

Files (round 2): `codex/selfsim-{prompt,answer}.md`, `selfsim-run.log` (decorrelated, `SELF-SIMILAR-BOUNDED`);
`T_{k,r}` min `= minAdm` and the Wishart-gate recursion scan recomputed + verified inline (`n=3..15`
square; 71 gate-recurse chains ≤ width 8).
