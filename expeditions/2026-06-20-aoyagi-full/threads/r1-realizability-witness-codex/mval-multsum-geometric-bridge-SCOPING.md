# #136 Mval = multSum (geometric-codim bridge) — de-risk SCOPING (pen-and-paper, decorrelated)

De-risks the #136 core identity before fm3 commits to formalising the geometric bridge: **is
`Mval(M,T*) = multSum/orbitLinearCodim` (the Ext¹ codim of T*'s orbit-rank-locus) TRUE + provable, and
where would it live?** The LR "geometric codimension is the new content" link.

Exact algebra (sympy: a SYMBOLIC polynomial-identity proof + an exhaustive realizability sweep over ℚ).
Decl-grounded against `Core.OrbitLinearCodim` (`orbitLinearCodim_eq_multSum`), `Core.OrbitKostant`
(`kostantArrayOfRank = diff ∘ embedRank`), `Core.RankPattern` (`diff_apply`), `DLN.RLCT.Lambda` (`Mval`).

## Verdict (one line)

**The identity is TRUE and is a PURE ALGEBRAIC (polynomial) IDENTITY in `(M,T)` — `Mval(M,T) =
multSum(diff(r))` for the explicit rank pattern `r_{ij} = ρ_j + (M_i − ρ_i)` (i≤j), proven symbolically
for L=2,3,4. BUT the GEOMETRIC reading (that this `multSum` is the genuine `codim Ō` of a real orbit)
holds only when that `r` is a realizable rank pattern, i.e. when `diff(r)` is a nonnegative Kostant
partition — which FAILS on width-spike `M` (7310/10820 admissible cases have a negative corner
multiplicity). So: the combinatorial identity is bedrock and general; the geometric identification is
genuine on width-MONOTONE `M` (const-width: all valid; weakly-increasing width: all valid) and needs care
elsewhere.** The recurring trap is live here — name it the **combinatorial** identity (always true),
distinct from the **geometric** codim reading (scoped to realizable strata).

## The A1 SHORTCUT (fm3's question — the route that decides formalisation cost)

**#136 ROUTES THROUGH A1. No fresh quadruple-sum = single-sum proof is needed for the value.** The
decorrelated-confirmed chain (codex 136b, captured, agrees on all 4 Qs):

    multSum(diff r(T*))  =  Mval(M, T*)        [the per-stratum ring-identity FACT, specialised at T*]
                         =  minAdm(M)          [T* is the admissible achiever — attainment]
                         =  2 · cleanCore(c*, sortedSmallest M c*)   [A1 `lambdaCore_eq_clean`, GREEN]
                         =  2 · lambdaCore(M)

So the geometric codim of the achiever orbit equals `2·cleanCore` (Aoyagi's `¼(Σq²−Σm²)` closed form)
**via composition**, not via a direct `multSum = cleanCore` reduction.

Two precision points (both verified, both load-bearing for fm3):

- **`multSum = cleanCore` is a VALUE-COINCIDENCE AT THE ACHIEVER, NOT a per-stratum identity.** `cleanCore`
  is the minimum-value closed form (built from the `c+1` smallest widths + a balanced split); there is no
  per-T `cleanCore`. For `M=(3,3,3,3)`: per-stratum `Mval`∈{6,7,9}, `2·cleanCore` over `c`∈{9,7,6} — same
  set, but NOT a per-stratum correspondence. So fm3 must NOT try to prove `multSum(T)=cleanCore` for
  general `T` (that's false off the achiever); it composes the per-stratum `Mval=multSum` ring-identity
  with A1 at `T*`.
- **A1 is the EXISTENTIAL at the achiever's `c*`, NOT `min over c`.** Exhaustive (L=2..4): `minAdm =
  2·cleanCore` at SOME `c` holds in all 1344 cases; the NAIVE `min_c 2·cleanCore` FAILS in 448 (goes to
  0/negative on width-spike M — exactly the CLAUDE.md "min_ℓ can go negative" trap). A1's
  `lambdaCore_eq_clean` correctly uses the genuine achiever's breakpoint count `c*`, not a minimisation
  over `c`. fm3 must invoke A1 at `c*` (the existential), never `min_c`.

**Cheapest Lean route (codex Q3, ranked):** (a) compose the per-stratum `Mval=multSum` ring-identity
(provable by `ring` after unfolding the finite sums) with A1's green `lambdaCore_eq_clean`, instantiated
at an attaining `T*` — CHEAPEST. (b) a direct `multSum=cleanCore` reduction is heavier and would need the
achiever-c caveat. **No-explicit-T* obstruction (codex Q4):** the proof needs only the existential
argmin package `∃ T*, T* ∈ Adm M ∧ Mval M T* = minAdm M` (already destructed in the green
`close_of_feasible`, `Skeleton.lean`) + the per-stratum identity specialised at that `T*` — NO explicit
formula for `T*` required.

No kill-condition for the combinatorial identity. A scope-boundary (not a kill) on the geometric reading.

## What was tested (exact)

The chain (decl-grounded):
`T → ρ=(M_0,T_0,…,T_{L-1}) → r (the orbit rank pattern) → m = diff(embedRank r) (Kostant array,
OrbitKostant) → multSum(m) = Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1}·m_{uv} (orbitLinearCodim_eq_multSum)`,
vs `Mval(M,T) = Σ_j (ρ_j − T_j)(M_{j+1} − T_j)`.

Three candidate rank patterns were tested (the first pass found the naive one wrong):
1. **`achieverRankPattern` (the #121 cascade pattern, column-constant `r_{ij}=ρ_j` for i<j):** WRONG —
   `Mval ≠ multSum` (the diff gives garbage below the diagonal; `(2,2,2)` achiever → 5, not 3). The #121
   object is the cascade running-rank pattern, NOT the orbit's geometric rank pattern; they differ at
   interior cells (`(2,2,2)`: orbit `r_{1,2}=1`, cascade `r_{1,2}=ρ_2=0`).
2. **Window-min pattern `r_{ij}=min(min_{i≤p<j} T_p, min widths)`:** valid Kostant `m` (0 invalid) but
   `Mval ≠ multSum` (10020/10820 fail). The generic matrix rank pattern — its codim is NOT `Mval`.
3. **`r_{ij} = ρ_j + (M_i − ρ_i)` for i≤j (else 0):** `Mval = multSum` in ALL 10820 cases (0 fail), and
   reproduces the committed anchors `(2,2,2)`→3,4 and `(3,2,3)`→5. THIS is the right pattern for the
   identity. But `diff(r)` has a negative corner entry `m_{N,N}` on width-spike M (7310 invalid).

## The pure-algebraic identity (the bedrock — SYMBOLIC proof, not a sweep)

`multSum(diff(r_candidate)) − Mval = 0` **identically** over symbolic `(M_0,…,M_L, T_0,…,T_{L-1})`,
verified by `sympy.expand` for L=2, L=3, L=4 (no admissibility assumed). So it is a polynomial identity:
the LR quadratic `multSum` evaluated on the second-difference of `r_{ij}=ρ_j+(M_i−ρ_i)` IS Aoyagi's
`Mval`. The corner second-difference is `m_{NN} = M_N − M_{N-1} + ρ_{N-1}` (with `ρ_N=T_{N-1}=0`); the
identity holds regardless of its sign — the algebra does not see realizability.

This is the cleanest statement and where the bridge should live: **a combinatorial identity
`Mval M T = multSum (kostantArrayOf (ρ-pattern M T))`**, provable by `ring`/`decide`-style expansion,
with NO appeal to orbits, Ext¹, or Voigt. It bypasses the rank-pattern realizability question entirely.

## The geometric reading (scoped — the realizability boundary)

`multSum = orbitLinearCodim = finrank Ext¹ = codim Ō` (via `orbitLinearCodim_eq_multSum` + Voigt,
char 0) only when `m = diff(r)` is a genuine Kostant partition (nonnegative). Realizability of the
candidate `r`:

| M-class | admissible cases | `Mval=multSum` fails | invalid Kostant `m` (negative corner) |
|---|---|---|---|
| const-width `M_s ≡ c` | 117 | 0 | **0** |
| weakly-INCREASING width | 655 | 0 | **0** |
| weakly-DECREASING width | 1416 | 0 | 761 |
| all (L=2..4, widths 1..4) | 10820 | 0 | 7310 |

The negative entry is always the corner `m_{N,N} = M_N − M_{N-1} + ρ_{N-1}`, negative exactly when the
penultimate width spikes: `M_{N-1} > M_N + ρ_{N-1}`. On const-width and weakly-increasing-width M the
candidate `r` is a genuine realizable pattern, so the geometric codim reading is honest. The DLN
application uses reduced widths `M^s = H_s − r` (the singular core), which are NOT width-monotone in
general — so the geometric reading does NOT transfer to arbitrary DLN data without either (a) a
different (genuine) orbit rank pattern in the spike cases, or (b) restricting to the monotone-width
class.

[INFERENCE] In the spike cases the genuine orbit (the actual minimal-codim stratum) likely has a
DIFFERENT, nonnegative-`m` rank pattern with the SAME `multSum = Mval` (the codim is an orbit invariant;
the candidate `r` just isn't its rank pattern there). Confirming that — that EVERY admissible `Mval`
value is realized by SOME genuine orbit with `multSum = Mval` — is the residual geometric obligation, and
is exactly the realizability question #121/#99 already navigate on the RLCT side. It is NOT needed for the
combinatorial identity, and the value-headline (`½·minAdm`) consumes only the combinatorial `Mval`.

## Where it would live + the cleanest statement

- **Combinatorial bridge (recommended target, fully de-risked):** a Core or DLN lemma
  `Mval M T = multSum (kostantArrayOfRankPattern (ρ-pattern M T))`, proved by polynomial expansion
  (`ring` after unfolding the finite sums; L is the chain length, fixed per instance — `decide`-able for
  concrete L, `ring`/induction for general L). This is honest, general (all M,T), and bypasses Voigt.
  It is the literal "Aoyagi's `Mval` = the LR quadratic `multSum`" — the paper's bridge at the
  combinatorial level.
- **Geometric reading (scoped):** `multSum = codim Ō` via the committed
  `codimRepCanonical_orbitRankLocus_eq_multSum` (modulo Voigt, already discharged char 0). The honest
  statement names the realizable-stratum hypothesis (or the width-monotone class). Do NOT state it as an
  unconditional general-M geometric identity — name it by its true scope (the precision discipline; the
  recurring `rlct_…`/over-name trap in disguise).

## Most likely thing to break / next step

The geometric reading on width-spike M rests on the [INFERENCE] that a genuine nonnegative-`m` orbit with
`multSum = Mval` exists there. The single highest-value next decorrelated step (if the geometric headline
is wanted general): exhibit, for a spike witness (e.g. `M=(1,2,1), T=(0,0)`, `Mval=2`), a genuine Kostant
partition `m ≥ 0` with `multSum(m) = 2` AND realizing an admissible stratum — or show none exists (which
would scope the geometric headline to width-monotone M as a genuine boundary, not a gap). That witness/
refutation settles whether the geometric bridge is general or width-monotone-scoped. The combinatorial
identity needs none of this — it is bankable now.

## Decorrelation note (honest)

The load-bearing fact (the polynomial identity `multSum − Mval = 0`) is a SYMBOLIC sympy proof over the
free ring — a verified computation, the strongest form, not a judgment call. The realizability-class
breakdown and the A1-existential check are exhaustive over ℚ.

The A1-SHORTCUT route was independently confirmed by a fresh hypothesis-withheld codex consult (xhigh,
read-only sandbox + `--output-last-message`, CAPTURED at `codex/codex136b_answer.md`), agreeing on all
four route questions: route (a) [compose the per-stratum ring-identity + A1 at T*] proves
`minAdm = geometric codim` with no fresh quadruple-sum=single-sum proof (Q1); `multSum=cleanCore` is a
value-coincidence at the achiever, not per-stratum (Q2); route (a) is cheapest (Q3); and no explicit-T*
is needed — the existential argmin package suffices (Q4, a useful formalisation refinement). The earlier
`codex exec` consult on the IDENTITY itself (`codex/codex136_prompt.md`) did not render to capture this
session (the recurring `codex exec` rendering limitation when `--output-last-message` is omitted or the
read-only sandbox blocks code), but the symbolic proof carries that conclusion independently; the route
consult (the load-bearing design call for fm3) IS captured and agrees.

## Scripts (this dir) — exact, re-runnable

- `pp136_mval_multsum.py` — the first pass (found `achieverRankPattern` is the WRONG pattern; the
  cascade-vs-orbit gap).
- `pp136_corrected.py` — the candidate `r_{ij}=ρ_j+(M_i−ρ_i)`: `Mval=multSum` (0 fail) + the invalid-`m`
  count; anchors.
- the inline symbolic proof (`multSum−Mval=0` for L=2,3,4) + the M-class realizability breakdown.
- `codex/codex136_prompt.md` — the decorrelated consult prompt (capture incomplete; see note).
