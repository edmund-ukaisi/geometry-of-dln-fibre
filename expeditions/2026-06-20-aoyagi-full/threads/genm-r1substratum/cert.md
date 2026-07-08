# genm-r1substratum — CERTIFICATE: the sub-generic strata CLOSE (no counterexample)

**Seat:** pen-and-paper, OBSTRUCTION direction (attack the closure). **Wall:** R1-UPPER, box-finiteness
of the (S,J) native R-blowup, CITE-FREE. **Branch:** `origin/genm-r1substratum` (isolated worktree off
`expedition/aoyagi-full @adb2ad51`). **No Lean.**
**Method:** exact integer arithmetic over the *proven* `minAdm` layer-peel (reused verbatim from
`genm-r1rankcharge/rankcharge.py`, itself brute-validated against `Adm`/`Mval`); the paper's exact
Voight/Ext orbit-codimension formula (validated against the paper's own worked examples); a decorrelated
`local-codex-consult` (xhigh) that independently derived the closure and CORRECTED my provisional charge.

**Scripts (reproduce):** `substratum.py` (candidate charges vs anchors), `sweep_substratum.py`
(exhaustive), `prodrank_codim.py` (product-rank codim vs free-matrix formula), `orbit_codim.py` (paper
Voight/Ext codim, validated), `stratum_codim.py` (true stratum codim by tail rank), `verify_frontpeel.py`
(the front-peel identity + orbit-codim match + entanglement collapse), `adversarial_frontpeel.py`
(wide/deep battery + permutation invariance). Codex artefacts in `codex/`. All exact `ℕ`/`ℤ`; no floats.

---

## HEADLINE (controller-facing, one paragraph)

**The sub-generic strata do NOT break the pure rank-stratified route — they CLOSE, exactly, and the
descent's per-stratum bound reaches `½·minAdm M` on every one of them.** The r1rankcharge cert's flagged
"crude heuristic under-counts (`(4,4,2)` at `s′=1`: `7 < 8`)" was a **strawman on two counts**: (a) it
compared the sub-generic charge `7` to the *generic per-cut charge* `8`, not to the real finiteness target
`minAdm(4,4,2) = 7` — against the real target it *binds exactly*; and (b) it used the **free-matrix**
rank-drop codim `(b−s′)(n−s′)`, which is wrong when the tail is a genuine matrix **product** — the correct
codim is the **product-rank-drop** codim `minAdm(tailchain − s′)` (peeling identity, paper line 826). The
correct per-stratum charge, derived independently by a decorrelated Codex and confirmed against the paper's
exact orbit-codimension formula, is the **`t`-independent, entangled**
`charge(s′) = M₀·s′ + minAdm(M₁−s′, M₂−s′, …, M_L−s′)`, where `s′ = rank` of the tail product
`P = A₁⋯A_{L−1}`. Its two pieces (the tail-rank-stratum codim and the deeper recursion) are **NOT
additive** — they share the deeper matrices `A₂…A_{L−1}` and must be minimised **once** over the shared
deeper rank; the naïve additive charge double-counts. Closure is a **new exact peeling identity** (the
"front-peel"): `minAdm(M) = min_{q} [ M₀·q + minAdm((M₁,…,M_L) − q) ]`, verified 0-fail exhaustively
(L+1 = 3..6, widths to 12) + an 18-chain wide/deep adversarial battery + permutation-invariant, and
**equal term-by-term to the paper's Voight/Ext orbit codimension** on every test chain. Mechanism: the
active-block decay lost to a rank drop (`M₀·s′` below the generic value) is **exactly compensated** by the
entangled codimension `minAdm((M₁…M_L)−s′)` of the tail-rank stratum — each `s′` is one term of the peel
min, so `charge(s′) ≥ minAdm(M)` always, with equality at the binding `s′`, which is frequently
**sub-generic** (e.g. `(4,4,2)` binds at `q=1<2`, `(5,4,3,2)` at `q=0`). The one genuine build obligation
(not a truth-gap): the peel step must be **stratum-aware** — a stratum-blind recursion delivers only
`a·s′ + minAdm(redChain)`, which is `< minAdm` on binding sub-generic strata (`(3,3,3,4)` at `t=1,s′=1`:
`5 < 7`). The clean fix is the **front-peel primitive** (§C), which dissolves the sub-generic case entirely.

---

## (A) THE VERDICT: **CLOSURE — no counterexample stratum**

The dispatch asked, OBSTRUCTION direction: *is there a chain `M`, cut `t`, sub-generic rank
`s′ < min(b,n)` at which the CORRECT accounting (`a·s′/2` + determinantal stratum codim + arity recursion)
FAILS to reach `½·minAdm M`?*

**Answer: NO.** With the CORRECT (product-rank, entangled) accounting, every sub-generic stratum charges
`≥ minAdm M`, with the minimum over strata equal to `minAdm M`. Verified three decorrelated ways, all exact.

### The correct per-stratum charge (exact)

Fix a cut `t`, `a = M₀−t`, `b = M₁−t`, `n = min(M₂,…,M_L)`, generic tail rank `s = min(b,n)`. The tail
product is `P = A₁⋯A_{L−1}` (widths `(M₁,…,M_L)`); the descent's non-pivot block `Q_b` is `b` rows of `P`,
so for sub-generic `s′ < s ≤ b`, `{rank Q_b = s′}` has the same top-dimensional part as `{rank P = s′}`.
The true codimension of that stratum, times `2` (RLCT units → codim), is

    charge(s′)  =  M₀·s′  +  minAdm(M₁−s′, M₂−s′, …, M_L−s′)                     (†)

**INDEPENDENT of the cut `t`.** Its decomposition into the descent's three requested pieces:

- **(i) active-block decay** `a·s′ = (M₀−t)·s′` — the `Γ ↦ Γ·Q_b` shift `a·s′/2`, TIGHT (banked
  obstruction note).
- **(ii)+(iii) the deeper part** `t·s′ + minAdm((M₁,…,M_L)−s′)`, which is the **ENTANGLED** minimum over
  the shared deeper product rank `r = rank(A₂⋯A_{L−1})`:

      t·s′ + minAdm((M₁..M_L)−s′)  =  min_{r=s′..n} [ t·r + (b−s′)(r−s′) + minAdm((M₂..M_L)−r) ]      (‡)

  Here `t·r` = cost of the pivot rows `B·R = 0`, `(b−s′)(r−s′)` = the free `b×r` rank-drop of `D·R`, and
  `minAdm((M₂..M_L)−r)` = the product-rank cost of `R`. The three terms share `r`; **the stratum codim (ii)
  and the recursion (iii) are entangled, not additive.** Adding them independently as
  `minAdm((b,M₂..M_L)−s′) + minAdm(t,M₂..M_L)` **double-counts** the deeper rank variables. `(‡)`'s
  collapse to the closed form `t·s′ + minAdm((M₁..M_L)−s′)` is verified 0-fail (L+1=4,5; the L+1=3
  "fails" are the degenerate `L=2` regime where the deeper product `R` is empty — `(†)` still holds there).

Summing (i)+(ii)+(iii): `a·s′ + t·s′ + minAdm((M₁..M_L)−s′) = M₀·s′ + minAdm((M₁..M_L)−s′) = (†)`.

### The closure — the FRONT-PEEL identity (exact, exhaustive, decorrelated)

`(†)` is one term of a **new exact peeling identity for `minAdm`** — peel the FRONT matrix `A₀` against
the whole tail product `P`, stratified by `rank P = q`:

    minAdm(M₀, M₁, …, M_L)  =  min_{q=0}^{min(M₁,…,M_L)} [ M₀·q  +  minAdm(M₁−q, M₂−q, …, M_L−q) ]     (FP)

Geometry: `M₀·q` = codim `{A₀·(q-dim column space of P) = 0}` (`A₀` kills a `q`-dim subspace of `ℝ^{M₁}`,
cost `M₀·q`); `minAdm((M₁..M_L)−q)` = codim `{rank P ≤ q}` (peeling identity, line 826, applied to the
tail chain). Hence **`charge(s′) ≥ minAdm(M)` for every `s′`, and `min_{s′} charge(s′) = minAdm(M)`.**

| check | scope | result |
|---|---|---|
| (FP) identity `= minAdm` | L+1=3..6, widths 0..12 (≈12k chains) | **0 fails** |
| `charge(q) ≥ minAdm`, all `q` | same | **0 below** |
| tightness `min_q charge = minAdm` | same | **0 non-tight** |
| (FP) adversarial wide/deep | 18 chains incl. `(20,20,3,2,1)`,`(11,11,11,11,2)`,`(2,20,20,2)` | **0 fails** |
| `charge(q) ==` paper orbit codim | 9 chains (Voight/Ext, `r_{1N}=q` strata) | **exact MATCH** |
| (FP) permutation-invariant | all multisets L+1=4 w0..5 | **0 non-invariant, = minAdm** |

The Voight/Ext cross-check is the decorrelated keystone: the paper's orbit-codimension formula
`codim(𝒪) = Σ_{1≤i≤u≤j≤v≤N} m_{(i-1)(j-1)} m_{uv}` (validated: `(2,2,2)→3`, `(2,3,2)→4` [2 comps],
`(2,4,2)→4`, `(3,3,3)→7` [2 comps], matching the paper's §examples) gives, for `Σ⁰` stratified by the
tail-product rank `r_{1N}=q`, the SAME per-`q` codimension as `(†)` — computed by a completely different
route (enumerate Kostant partitions, evaluate the Ext bilinear form) than the peel recursion. Example
`(3,3,3,4)`: `q=0,1,2,3 → 8,7,7,9` by both; `(4,4,2,2)`: `0,1,2 → 4,5,8` by both.

### Mechanism (one line)

**Higher rank-deficiency is never more binding: the active decay lost to the rank drop is exactly
compensated by the entangled codimension of the tail-product-rank stratum, and the result is a single
term of the front-peel min for the full zero-product locus.** The top component (codim `= minAdm`) is
frequently at a *sub-generic* tail rank (`(4,4,2)` at `q=1`, `(4,4,2,2)`/`(5,4,3,2)` at `q=0`) — the
sub-generic strata are exactly WHERE `minAdm` is realised, not a threat to it.

### Structural certainty (independent of the descent)

`minAdm = min codim over the orbits of Σ⁰_M` (confirmed exactly via the paper's Voight/Ext formula,
validated against the paper's worked examples). The descent's rank-stratification, fully recursed,
refines each chart into orbit strata — **all of codim `≥ minAdm`**. So no stratum, generic or sub-generic,
can be more binding than `minAdm`; finiteness (the truth, `rlct = ½·minAdm` cited Aoyagi) holds on every
stratum. The descent *certifies* it provided each peel step is **stratum-aware** (below).

---

## (B) WHAT THE CERT'S "UNDER-COUNT" ACTUALLY WAS (correcting the record)

The r1rankcharge cert (§B, line 221) flagged: crude `a·s′ + (b−s′)(n−s′)` under-counts, `(4,4,2)` at
`s′=1`: `4+3=7 < 8`. Two independent errors, both now exact-resolved:

1. **Wrong reference.** `minAdm(4,4,2) = 7` (faithful, brute-validated), NOT `8`. `8` is the *generic
   per-cut* charge `a·s + minAdm(redChain) = 4·2 + 0` at `t=0`. The finiteness target is `minAdm = 7`.
   The crude charge `7` **equals** it — binds, does not under-count.

2. **Wrong codim formula.** `(b−s′)(n−s′)` is the codim of a rank-drop of a **free** `b×n` matrix. The
   tail is a matrix **product** for `L ≥ 3`; its rank-drop codim is `minAdm(tailchain − s′)` (peeling
   identity), which **differs** from the free formula. My `prodrank_codim.py` (exact rational Jacobian)
   confirms the difference and confirms the free formula both over- and under-shoots on products; the
   authoritative value is the peeling-identity one, cross-checked against the Voight/Ext orbit codim.

The provisional additive charge `C2 = a·s′ + minAdm((b,M₂..M_L)−s′) + minAdm(t,M₂..M_L)` I first tested
is **superseded**: it double-counts (Codex + `(‡)`), so it is neither an upper nor a lower bound on the
true `charge(s′)` — it is simply the wrong (additive) model. Both `C2` and the true `charge(s′)` happen to
stay `≥ minAdm`, but only `(†)` equals the orbit codim (tight, correct geometry).

---

## (C) THE STRATUM-AWARE PEEL PRIMITIVE (Lean-ready SHAPES — sanity, not a build)

**The one genuine build obligation.** A **stratum-blind** recursion (peel `Γ` for shift `a·s′/2`, then
recurse with the *generic* `minAdm(redChain t M)`) delivers only `a·s′ + minAdm(redChain t M)`, which is
**strictly `< minAdm`** on binding sub-generic strata:

    (3,3,3,4), t=1, s′=1:  a·s′ + minAdm(redChain) = 2·1 + minAdm(1,3,4) = 2 + 3 = 5  <  7 = minAdm.

So the peel step must be **stratum-aware** and extract the tail-rank stratum's own (entangled) codimension.
There are two sound ways; the **front-peel is the clean one** — it dissolves the sub-generic case entirely.

### Recommended: the FRONT-PEEL primitive (no Schur/`Q_b` coupling)

Peel the front matrix `A₀` against the whole tail product `P`, stratified by `rank P = q`. On `{rank P = q}`
write `P = U·V` (`U : M₁×q` full column rank spanning `im P`, `V : q×M_L` full row rank). Then
`frobSq(A₀·P) = frobSq((A₀·U)·V)` and the map `A₀ ↦ A₀·U` is a linear surjection onto `M₀×q` with kernel
dimension `M₀·(M₁−q)` — an isotropic `(M₀·q)`-dim Morse block plus a bounded kernel box. This gives shift
`M₀·q/2` (regime A) / a terminal branch (regime B), **using the banked corank brick at `q` directly** with
**no Schur complement and no `Q_b`** — the `Γ`-coupling that made the layer-peel step delicate disappears.
The deeper factor is the tail-rank locus `{rank P ≤ q}`, whose singularity type equals (normal-slice
isomorphism, Thm `addlongest`, line 688) that of `Σ⁰` of the shifted chain `(M₁−q,…,M_L−q)` — recurse.

    /-- Front-peel step: on the outer stratum `{rank P = q}` (P = tail product, widths (M₁,…,M_L)),
        the A₀-integral of `frobSq(A₀·P)^{−c}` splits by a MEASURE-PRESERVING linear surjection
        `A₀ ↦ A₀·U` (U a full-col-rank basis of `im P`) into an `M₀×q` active Morse block and an
        `M₀·(M₁−q)` bounded kernel box, giving shift `M₀·q/2` (regime A) / terminal (regime B). -/
    structure FrontPeelStep (M₀ q : ℕ) : Prop where
      shiftA : c > (M₀*q : ℝ)/2 → (A₀ integral) ≤ Cresid (M₀*q) c · ∫ (tailRankLocus)^{−(c − M₀*q/2)}
      termB  : c < (M₀*q : ℝ)/2 → (A₀ integral) < ⊤

    /-- The front-peel charge/identity (ℕ form), the closure of this cert:
        `minAdm M = min_{q ≤ min(M₁,…,M_L)} [ M₀·q + minAdm ((M₁,…,M_L) − q) ]`. -/
    def frontCharge (M : Fin (L+1) → ℕ) (q : ℕ) : ℕ := M 0 * q + minAdm (fun i => M i.succ - q)
    theorem minAdm_eq_frontPeel (M) :
        minAdm M = (Finset.range (tailMin M + 1)).inf' (by simp) (frontCharge M)
    theorem frontCharge_ge_minAdm (M) (q) (hq) : minAdm M ≤ frontCharge M q          -- (FP), ≥ at every q

  **Banked bricks reused:** `matBox_corank_residual_absZ_le` / `matBox_corank_dominates_absZ_lt_top`
  (regimes A/B at block dim `M₀·q`); the pivot-cover `pivotLocus_eq_iUnion` for the rank-`q` tail
  stratification; `SchurRecStep`/`core_schurGen_lt_top` (WellFounded-on-corank) for the inner tail-rank
  recursion. The shift is `M₀·q/2`, **not** `a·s/2` — the front-peel charges the FULL front width `M₀`,
  which is exactly why it reaches `minAdm` on every stratum without a separate sub-generic case.

### Alternative: keep the layer-peel `RankStratPeelStep`, made stratum-aware

If R1-UPPER stays on the layer-peel (`Γ`, `Q_b`), the `RankStratPeelStep` on `{rank Q_b = s′}` must charge
`a·s′` (active `Γ`) **and then recurse into the entangled deeper amount** `t·s′ + minAdm((M₁..M_L)−s′)` of
`(‡)` — i.e. the deeper recursion must carry the `rank Q_b = s′` constraint (realised by its own rank
stratification of the deeper product `R`, giving the `min_r` of `(‡)`), NOT the stratum-blind
`minAdm(redChain)`. This is correct but strictly more entangled to formalise than the front-peel;
recommend the front-peel.

---

## Firmest result / most likely to break / next step

- **Firmest (certificate):** the sub-generic strata CLOSE. Correct charge `(†) = M₀·s′ + minAdm((M₁..M_L)
  −s′)`, entangled not additive `(‡)`, `t`-independent; closure = front-peel identity `(FP)`, verified
  0-fail exhaustively (≈12k chains, widths to 12) + 18-chain adversarial + permutation-invariant +
  **term-by-term equal to the paper's Voight/Ext orbit codimension** (decorrelated route). No `(M,t,s′)`
  counterexample exists. The cert's `(4,4,2)` "under-count" was a strawman (wrong reference `8`, wrong
  free-matrix codim).
- **Most likely to break it:** *not* the combinatorics (settled three ways). The residual risk is purely
  analytic and lives in the primitive: whether the front-peel's `A₀ ↦ A₀·U` shift `M₀·q/2` and the tail-
  rank-locus recursion compose soundly to `½·minAdm` in Lean — the analog of verifying the layer-peel's
  `a·s/2` shift. The **normal-slice isomorphism** (Thm `addlongest`) is the load-bearing input that lets
  the tail-rank locus recurse as a shifted `Σ⁰`; if that transfer of singularity type has a hidden
  measure-theoretic gap, the front-peel primitive (not the charge) would need repair.
- **Next construction/consult:** hand the `FrontPeelStep` shape to the formaliser and verify the
  `A₀ ↦ A₀·U` shift `M₀·q/2` on the smallest genuine product case (`(3,3,3,4)`, binding at `q∈{1,2}`) —
  the decisive analytic probe, the front-peel analog of the r1rankcharge `a·s/2` verification one axis over.
