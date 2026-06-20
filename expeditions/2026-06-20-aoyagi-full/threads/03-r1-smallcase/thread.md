# Thread 03 — R1 small-case blueprint + spine-risk probe (pp, parallel/read-only)

- **Seat:** `pp` (pen-and-paper). **Read-only on repo + /tmp scratch** (`/tmp/r1_*.py`,
  `/tmp/codex-r1-*.md`); controller integrates (this doc). **Reports to:** controller.
- **Status:** round 1 (L=2) done; round 2 (L=3) in-progress.

## Verdict (round 1): the spine is SOUND; design-spec §9.3 was mis-stated

**The strong claim "R1's chart exponents = Adm" is FALSE** — the counts forbid a bijection:
(1,1,1) 2 T's ↔ 1 chart; (2,1,2) 2 T's ↔ 4 charts; (2,2,2) 3 T's ↔ 24 charts. Confirmed by `pp`
**and** a decorrelated Codex consult (xhigh), independently.

**The weak (value-match) claim HOLDS on all three cases:** the resolution's minimum chart-ratio
`= ½·min_{T∈Adm} Mval(T) = λ_core =` ground truth. This is the only thing the headline needs.

**What `T` actually indexes (the useful finding).** For L=2, `T=(t,0)` indexes the **rank-incidence
stratum** `{rank C¹ = t, C¹C² = 0}`, and
> `Mval(T) = (M¹−t)(M²−t) + t·M³ = codim` of that stratum
(the `(M¹−t)(M²−t)` = codim{rank C¹ ≤ t}; the `t·M³` = columns of C² forced into ker C¹). Hence
`λ_core = ½·min over strata of codim` — the `rlct = ½·codim` structure made concrete on the singular
core. The resolution's minimizing **divisor types** (not charts) correspond to the minimizing T's, with
ratio `½·Mval(T)`; chart multiplicity is just affine-chart duplication of one exceptional divisor. The
order θ = #{minimizing divisor types} = `a(ℓ−a)+1` — NOT the chart count and NOT |argmin Adm|
(verified earlier: (2,2,2,2,2) has 6 admissible minimisers but θ=5).

## Per-case chart blueprint (all exponents symbolically verified)

- **(1,1,1)** `F=(c₁c₂)²` — already normal-crossing, **no blow-up**. Identity chart: k=(1,1), h=(0,0),
  ratios (½,½), min=½=λ ✔. → the cleanest end-to-end **first** validation case.
- **(2,1,2)** `F=(a₁²+a₂²)(b₁²+b₂²)` — blow up the a-cone and b-cone (4 product charts); every chart
  `F=x²z²(1+y²)(1+w²)`, `|det|=|xz|` ⇒ k=h=1 on x,z, ratios (1,1), min=1=λ ✔, θ=2 (two exc. divisors).
- **(2,2,2)** `F=‖AB‖²` — 24 affine charts: blow up A-origin (Jac x³) → after a det-1 B-change,
  `AB = x·[…]`, `F=x²Q` → blow up smooth center {E=F₀=δ=0} (3 charts) → δ-pivot residual cone needs one
  more blow-up (4 charts). Minimizing chart: `F=x²s²·unit`, `|det|=|x|³|s|²` ⇒ (k_x,h_x)=(1,3)→ratio 2,
  (k_s,h_s)=(1,2)→ratio 3/2. min=3/2=λ ✔, attained only by s ⇒ θ=1 ✔. 24 charts cover.

## The corrected R1 obligation (supersedes design-spec §9.3 flag 3)

Hand the R1 rung the **value-match**, not a set bijection:
- **(i) [λ]** resolution's min chart-ratio `= ½·min_{T∈Adm} Mval(T)`. (What A1's minimisation computes;
  Theorem 3 + resolution existence give it.)
- **(ii) [meaning]** `Adm`'s T ↔ rank-incidence strata; `Mval(T) = codim` (proven L=2; general-L is the
  nested-rank version — the new top open item, round 2).
- **(iii) [θ]** per-chart tie-count at the min = #{minimizing divisor types} = `a(ℓ−a)+1` (rides inside
  S2 as divisor-type multiplicity; consistent with the §3 θ-seam).

`Adm` remains the correct **definition** substrate for `aoyagiλ` (its min gives λ); R1's obligation is
the value-match (i) — far weaker/cleaner than the exponent-set-equality. The spine is sound.

## Validate-small-first ordering (recommended)
`(1,1,1)` [no blow-up; normal-crossing in original coords] → `(2,1,2)` [cone blow-ups, θ>1] →
`(2,2,2)` [real recursive resolution]. `(1,1,1)` is the cleanest first full top-to-bottom Lean case.

## Open (round 2, in-progress): general-L `Mval = codim(nested-rank stratum)`
L=2 verified; L≥3 nested-rank version (t¹≥t²≥… as ranks at successive partial products) is the natural
generalization, NOT yet proven. `pp` is on `(2,2,2,2)` (λ=3/2, θ=3) to pin it + the divisor-type↔T
count + assess whether `λ_core = ½·min_strata codim` is the cleanest R1 obligation (possibly a cleaner
R1 architecture than chart enumeration).
