# A1 (#19) proof — keystone analysis (the perm-invariance wall)

The genuine `lambdaCore_eq_clean` statement is LANDED + green (`∃ c≤L, 1≤c ∧ lambdaCore M =
cleanCore c (sortedSmallest M c)`); Step 1 (`balancedSplit_min`) is PROVEN. The remaining proof has a
hard keystone, characterized precisely below so the controller/pp can decide on investment.

## The keystone: permutation-invariance of `minMval` — and why it's hard

`lambdaCore M = ½·min_{T∈Adm M} Mval(M,T)`. The genuine statement needs the minimizer's value to equal
`cleanCore` at the **sorted smallest** widths. But on **unsorted** M the minimizer's breakpoint widths
are M's actual breakpoint widths, NOT the sorted smallest (e.g. `M=[4,1,1,1]`: `M⁰=4` is forced as a
breakpoint width, so the minimizing T's widths are `[1,1,4] ≠` smallest `[1,1,1]` — yet the value
`cleanCore(2,[1,1,1])=1 = minMval`). So the clean route reduces to **sorted M** via:

> **Keystone:** `lambdaCore M = lambdaCore (M∘σ)` for any permutation σ (i.e. `min_{T∈Adm} Mval` is
> permutation-invariant in M). Verified exhaustively: **15800/15800** (L≤3, widths 0..4).

### Why the keystone has NO slick route (probed, decisive)

It is a **min-level fact, not a structural bijection.** Under an adjacent transposition of M:
- the `Adm` cones genuinely DIFFER: **560/1700** swaps change the cone (the cone is order-sensitive —
  `admBound` treats index 0 specially via `min(M⁰,M¹)`, and the weak-decrease `t¹≥…≥tᴸ=0` is tied to
  the layer order);
- even the **`Mval`-multisets** over the cone are NOT preserved: only **1140/1700** match.

So there is no `Mval`-preserving bijection `Adm M ≃ Adm (M∘σ)` to transport. Perm-invariance holds only
at the level of the **minimum**, which means the proof must either (a) characterize the minimizer
explicitly and show its value is σ-invariant, or (b) a subtler min-transport argument. Either is a
genuine multi-hundred-line theorem (the agent estimated 250-350 lines for the full #19; the keystone is
the bulk of it).

## Flag for pp's card (`threads/14-r1-design/a1-statement-card.md`, route §47-64)

Step 3's "per-c lower bound" as literally stated is the **false `min_c` reading** (`lambdaCore =
min_c cleanCore(c, smallest)` is FALSE — `M=[1,1,4]`: c=2 gives 0 < ½). The exhaustive refutations:
`cleanCore` is NOT monotone in widths (`s=[1,2,4]` vs `[1,2,7]`: 2 vs −2); `max_c` also FALSE
(`[2,2,2]`: 2 ≠ 3/2). The CORRECT per-T bound is `Mval(M,T) ≥ 2·cleanCore(c_T, T's-own-breakpoint-widths)`
(via `balancedSplit_min`), then **perm-invariance + sorted-M** connects to the sorted smallest. The
*statement* (candidate (d), `∃ c` achiever) is correct + total (1360/1360); only the *route* needs the
perm-invariance reframing.

## Recommendation

#19 is OFF the headline critical path (the headline uses `lambdaCore`'s min-definition directly, not the
clean form). The genuine statement + Step 1 are banked. The keystone is a hard, no-slick-route
multi-hundred-line proof. Per bedrock "roadmap it if not within reach, don't thrash": deliver this clean
stuck-statement; the controller decides whether to invest (fm continues / hand to a dedicated tide / pp
reframes the card route first so the proof targets the corrected route).

## Route options re-confirmed (numeric, before committing to the ~250-line build)

The #19 value-claim is rock-solid: `∃ c∈{1..L}, ½·minMval(M) = cleanCore(sortedSmallest M c)` holds
3900/3900 (L≤4, widths 1..5). Two routes to it in Lean, both substantial:

- **(A) Full perm-invariance** `lambdaCore M = lambdaCore (M∘σ)` then sorted-M analysis. Hard: min-level
  fact, no Mval-preserving bijection (proven above). The σ-transport of the minimiser is the bulk.
- **(B) Symmetry-of-cleanCore route** (avoids global perm-invariance): `cleanCore` depends only on the
  *multiset* of widths (it's `Σm²`, `Σm`). So it suffices to show the achiever's witness `T*` has
  breakpoint-width-multiset = `{sortedSmallest M c*}`, and `Mval(M,T*) = 2·cleanCore(those widths)`, plus
  the per-T lower bound `Mval(M,T) ≥ 2·cleanCore(T's breakpoint widths)` via `balancedSplit_min`. This
  is LOCAL to the achiever (no σ-transport of the whole cone) — likely the cleaner route. Still needs:
  the Adm-T → breakpoint-widths reparametrisation (the `Mval` completed-square identity, design §4.3) and
  showing the global min's breakpoint widths are the sorted smallest. ~200 lines, but no perm-invariance.

RECOMMENDATION: route (B). The hard sub-piece is the `Mval`-to-breakpoint completed-square identity
(design-spec §4.3) + that the minimiser's breakpoint widths are the c+1 smallest (the achiever is where
the balanced split on the smallest is Adm-realisable). `balancedSplit_min` (Step 1, DONE) is the lower-
bound engine. A dedicated tide with this route + the verified facts is the efficient path if fm stays
on critical-path work.
