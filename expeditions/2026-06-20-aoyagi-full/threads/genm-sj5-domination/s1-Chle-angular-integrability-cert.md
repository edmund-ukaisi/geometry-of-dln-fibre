# S1 `C_hle` angular-integrability cert — the P-radial-blow-up finiteness gate (Part A §Close(ii))

**Seat:** pen-and-paper (design-space math, one truth-value, decorrelated), aoyagi-full Stage 2,
`genm-sj5-domination`, S1 pre-tide load-bearing gate. **Date:** 2026-07-13. **NO Lean edits, NO git, NO
build.** Exact algebra (radial-blow-up bookkeeping + det-1 sphere / compact-box codimension) + numeric MC
guide only. Decorrelated `local-codex-consult` (xhigh, my conclusion WITHHELD — "adjudicate either
direction"): `codex/s1-Chle-angular-{prompt,answer}.md`. Numeric guides (guide only, not proof):
`/tmp/chle_sweep.py`, `/tmp/chle_categorize.py`, `/tmp/chle_refine.py`, `/tmp/chle_sound.py` (threshold
sweeps over `M∈[2..6]^{3,4,5}` all binding cuts), `/tmp/chle_mc.py` (exact map-rank check), `/tmp/chle_vol.py`
(sublevel-volume exponent).

**The ONE truth-value adjudicated.** In the P-radial blow-up of Part A of `s1-spine-headsplit-cert.md`
(§A.2/§A.4), is the reorganization constant `C_hle` genuinely FINITE — does the angular/absorbed integral
converge, or diverge (a wall)?

---

## ★ HEADLINE VERDICT

**FINITE `C_hle` — labour, S1's Part A stands — WITHIN the scope `M₂ ≤ M₁` (both brief anchors sit inside,
at the marginal boundary).** The absorbed integral is over a COMPACT box; its only singularity is the
zero-locus of the pivot energy, of exact codimension `u·ρ` (`ρ = min(M₁,M₂,…,M_last)` = the generic rank of
the deep-tail product `Q`), so it converges iff the post-corner-peel exponent `c'' < u·ρ/2`. C_hle is finite
throughout the comparator's convergence range **iff `u·ρ ≥ minAdm(M')`** (`M' = redChain(u)M = (u,M₂,…,M_last)`).
This holds for **every `M₂ ≤ M₁` chain** (exhaustively; equality — the marginal case — exactly on equal-width
chains like the anchor `(3,3,3)`), so C_hle is finite in scope.

**Three findings beyond a bare "finite":**
1. **The cert's A.4 finiteness JUSTIFICATION is wrong (but the conclusion, in scope, is right).** A.4 argues
   the integrand is *bounded* via `σ_min(P̂) ≥ σ_max(P̂)^{−(u−1)}` on `{|det P̂|=1}`. That RHS `→ 0` (σ_max is
   unbounded on the non-compact det-1 sphere), so it is **no uniform lower bound** — the integrand is
   **unbounded for every `c'>0`**. Finiteness comes not from boundedness but from the singularity being
   *integrable* (codim `u·ρ`). The det-1 sphere's non-compactness is a red herring: the underlying integral
   is over a compact `(P,B₁₂)`-box and needs no blow-up to see finiteness. (Codex independently flagged the
   same reasoning error.)
2. **A genuine WALL exists for `M₂ > M₁` wide chains** (`u·ρ < minAdm(M')`): the pivot-block absorbed integral
   is strictly *more* singular than the comparator, so C_hle diverges. This is a SECOND wide-chain wall,
   distinct in mechanism from Part B.2b's corank-weight wall but sharing the same safe boundary `M₂ ≤ M₁`.
3. **SOUNDNESS SHARPENING — the corrected statement (B.4) hypothesis set is insufficient as written.** The
   corank convergence clause `hconv` (`m = min(M₁,n)−j ≥ a+b`) does **NOT** imply C_hle finiteness: there are
   `M₂>M₁` chains (e.g. `M=(3,3,4,4)`, `u=2`, `t=j=1`: `hconv` holds, `m=2=a+b`, yet `u·ρ=6 < minAdm(M')=7`)
   where the corank weight converges but the pivot block diverges. **The `C_hle < ⊤` clause must be gated by
   `M₂ ≤ M₁` (equivalently the pivot admissibility `u·ρ ≥ minAdm(M')`), a condition strictly stronger than
   `hconv` on those chains** — not merely by the existing hypotheses. This reinforces and sharpens the
   Part B.2b boundary (which recommended `M₂≤M₁` but justified it only through the corank weight).

---

## 1. What `C_hle` is — the absorbed integral, isolated

After the exact `B₁₂→Γ'` shear (§A.1, `chartInner_schurShearFree_eq`) the freed loss is
`frobSq(P·Q_p + B₁₂·Q_b)` [pivot] `+ frobSq(C·Q_p + Γ'·Q_b)` [corank]. The corank side (Γ', C) is peeled by
the banked S3 brick `shell_corankOffSector_le_unif`, which is **uniform in `Ccross = C·Q_p`**, producing the
`−ab/2` corner-Gaussian exponent shift `c' ↦ c'' := c' − ab/2` and integrating `C` to a bare box volume
`(2T)^{au}` (the pivot energy has no `C`). What remains — the genuine `C_hle` content, the "P-angular +
`B₁₂`-box directions with no image in the RHS" of §A.4 — is the **front-layer pivot-block absorbed integral**

    J(c'') := ∫_{P ∈ [−T,T]^{u×u}} ∫_{B₁₂ ∈ [−T,T]^{u×b}}  frobSq(P·Q_p + B₁₂·Q_b)^{−c''}  dB₁₂ dP,     (∗)

evaluated at a **generic** `z` (so `Q = A'₀·Z_deep = [Q_p ; Q_b]` has generic rank; the rank-deficient `z`
are the SHELL's / comparator's job, handled by the Part B containment `{Z∈S_j} ⊆ G`). `C_hle` finite ⟺ `(∗)`
finite at the critical exponent, with the ratio `J / (comparator inner)` bounded as `c'' →` criticality.

Here `Q_p` is `u×n`, `Q_b` is `b×n`, `n = M_last`, and the stacked `[Q_p;Q_b] = Q` is `M₁×n` (since
`u+b = M₁`), the product of the deep-tail generic matrices of shapes `M₁×M₂, M₂×M₃, …`. Its generic rank is

    ρ := rank(Q) = min(M₁, M₂, …, M_last).                                                          (rank)

## 2. The P-radial blow-up — the exact Jacobian and the exact angular integral to be bounded

Write `P = s·P̂` with `s := |det P|^{1/u}` (scalar scale) and `|det P̂| = 1` (the det-1 unit clear, §A.2).
This is a *uniform*-scalar dilation of `ℝ^{u²}`, so the Lebesgue measure decomposes polar-fashion with the
det-1 hypersurface `Σ := {|det|=1}` as the angular cross-section:

    dP = s^{u²−1} · ds · dμ_Σ(P̂),        μ_Σ = the cone (spherical) measure on Σ.                  (JacP)

Rescale the cross-term companion `B̃₁₂ := s⁻¹·B₁₂`, so `dB₁₂ = s^{ub}·dB̃₁₂` and, by homogeneity,

    frobSq(P·Q_p + B₁₂·Q_b) = s²·frobSq(P̂·Q_p + B̃₁₂·Q_b) =: s²·G(P̂, B̃₁₂).                         (homog)

Collecting the scale powers, `(∗)` becomes a RADIAL integral times an s-cut ANGULAR integral:

    J(c'') = ∫₀^{s★} s^{ (u²−1) + ub − 2c'' } ds  ·  A(s),     u²−1+ub = u·M₁−1,                     (split)
    A(s) := ∫_{P̂∈Σ, |P̂|_∞≤T/s} ∫_{B̃₁₂ : |B̃₁₂|_∞≤T/s}  G(P̂, B̃₁₂)^{−c''}  dB̃₁₂ dμ_Σ(P̂).           (ang)

**The exact `|Jac|` of `dP ↦ (ds, dP̂-angular)` is `s^{u²−1}`** (JacP); the accumulated scale-power feeding
the `s`-monomial is `s^{u·M₁−1−2c''}` (with the `B̃₁₂`-rescale contributing `+ub`). **The exact angular
integral to be bounded is `A(s)` of (ang)**, over the det-1 sphere `Σ` (dim `u²−1`) capped at `|P̂|≤T/s` and
`B̃₁₂` capped at `T/s`.

**Anchor `(3,3,3)`, `u=2`:** scale power `u·M₁−1 = 2·3−1 = 5` — this is exactly the comparator's Jacobian
monomial `|v₀|^{jc}=|v₀|^5` (`jc = minAdm(M')−1 = 5`), the beautiful consistency the cert observed. **Companion
`(3,3,3,3)`, `u=2`:** scale power `5`, but comparator `jc = minAdm(2,3,3)−1 = 4` — the LHS scale-monomial is
`|v|^5`, *less* singular than the comparator `|v|^4`, so the `s`-monomial dominates comfortably (`|v|^5 ≤
|v|^4` on `[−1,1]`).

## 3. The exact threshold — `A(s)` finiteness is where n < M₁ bites; the clean route is the compact box

The naive separation `J = [∫s^{uM₁−1−2c''}ds]·[A(∞)]` predicts threshold `c'' < u·M₁/2`. **That is valid only
when the full (`s→0`, cap `→∞`) angular integral `A(∞)` converges**, i.e. when the per-row map has no kernel
on the non-compact directions — equivalently `ρ = M₁` (`M₁` the smallest tail width). **When `ρ < M₁` the
angular integral `A(s) → ∞` as `s→0`**, the split does not factorize, and the true threshold drops. The
`σ_min(P̂)→0` worry of §Close(ii) is real *as a chart artefact* — but it is fully diagnosed by the compact box:

**Clean exact threshold (no blow-up needed).** The map `(P,B₁₂) ↦ P·Q_p + B₁₂·Q_b` is LINEAR
`ℝ^{u·M₁} → ℝ^{u·n}`, equal to `u` independent copies of `x ↦ x·Q` (`x ∈ ℝ^{M₁}`, `Q` the `M₁×n` stack). Its
rank is `u·rank(Q) = u·ρ`; its kernel (the zero-locus of the pivot energy inside the box) has dimension
`u·(M₁−ρ)` and **codimension `u·ρ`**. Transversally `frobSq(·)^{−c''} ≡ ‖z‖^{−2c''}` on the `u·ρ`
normal directions, so

    J(c'') < ∞   ⟺   c'' < u·ρ/2,        ρ = min(M₁,M₂,…,M_last).                                    (THRESH)

This is the exact-algebra core. **Verified exactly** (`/tmp/chle_mc.py`): the map rank equals `u·ρ` on every
tested chain including interior-min ones (`M=(3,4,2,4)`, `M=(4,4,3,2,5)`, `ρ=2` from an interior width),
`match=True` in all rows. **MC-corroborated** (`/tmp/chle_vol.py`): for `u=1`, `Vol{frobSq<ε} ~ ε^{ρ/2}`
(log-log slopes `1.508 ≈ 3/2`, `1.484 ≈ 3/2` at `ρ=3`); `u≥2` unreachable by uniform MC (codim ≥ 4) — the
exact rank argument covers those. The blow-up's `u·M₁/2` over-predicts precisely because `A(∞)` diverges when
`ρ<M₁`; the honest threshold is `u·ρ/2 ≤ u·M₁/2`, with equality iff `ρ=M₁`.

## 4. The criterion — `u·ρ ≥ minAdm(M')` — and the `M₂ ≤ M₁` safe scope

`C_hle` finite (up to and at the comparator's critical exponent) requires the pivot threshold `u·ρ/2` to be
`≥` the reduced-chain comparator threshold `½·minAdm(M')` (in the shared post-peel exponent `c''`;
`M' = redChain(u)M = (u,M₂,…,M_last)`, `minAdm` the landed recursion). Hence

    C_hle < ⊤   ⟺   u·ρ ≥ minAdm(M').                                                                (CRIT)

**Anchor check (why the comparison is against `minAdm(M')`, not `minAdm(M)`).** `(3,3,3)`, `u=2`: `u·ρ = 6 =
minAdm(2,3) = minAdm(M')` — EQUALITY, marginal-finite (the `ab=1` corner charge is the separate Gaussian, so
`minAdm(M)=7=ab+minAdm(M')` is NOT the comparison). At equality both sides blow up at the *same* rate
`~ 1/(2(3−c''))` as `c''→3` (the LHS is `∫_{ℝ⁶}‖·‖^{−2c''}`, the RHS `∫|v|^{5−2c''}dv`), so the ratio stays
bounded — genuinely finite at criticality, not merely below it. `(3,3,3,3)`, `u=2`: `u·ρ = 6 > minAdm(2,3,3)
= 5` — LHS strictly less singular, comfortable.

**Exhaustive sweep** (`/tmp/chle_refine.py`, `/tmp/chle_sound.py`; genuine cuts `u = t+j ≥ 2` with `t,j≥1`,
`a,b≥1`, binding, `M∈[2..6]^{3..5}`): **3988 FINITE, 419 WALL, and every single WALL is `M₂ > M₁`.** The
cross-check `M₂ ≤ M₁ ∧ genuine cut ⇒ C_hle wall?` returns **False** — **`M₂ ≤ M₁ ⟹ C_hle finite`, with no
exception**. The tightest in-scope cases (slack `u·ρ − minAdm(M') = 0`) are the equal-width chains
`(2,2,…)`, `(3,3,3)`, … — exactly the anchor family. So the safe scope is `M₂ ≤ M₁`, inside which C_hle is
finite; both brief anchors are inside (at the marginal boundary).

## 5. The WALL for `M₂ > M₁`, and why it is a genuine (second) obstruction — NOT inside scope

For `M₂ > M₁` chains `(CRIT)` can fail. Exact witness `M=(3,3,4)`, `L=0`, `u=1` cut: `ρ = min(3,4)=3`,
`u·ρ=3`, `M'=(1,4)`, `minAdm(M')=4`, `3 < 4` — pivot threshold `3/2` below comparator `2` → C_hle diverges
for `c'' ∈ [3/2, 2)`. Genuine-cut witness `M=(3,3,4,4)`, `u=2`: `u·ρ=6 < minAdm(2,4,4)=7`. This is a REAL
divergence of the absorbed integral (not a bound artefact): the pivot energy's zero-locus is codim `6`, too
low for the comparator's codim-`7`-flavoured singularity, so `∫frobSq^{−c''}` blows up before the comparator
does. It reflects that for wide chains the front-peel/head-split route CANNOT reach the true RLCT
`½·minAdm(M)` — the pivot block binds first — so a DIFFERENT branch (saturated / finer `Z_deep`
stratification, per B.2b) is required. Consistent with the paper's RLCT: no contradiction, because the true
RLCT of those chains is delivered by the other branch, not this route.

## 6. SOUNDNESS SHARPENING — `hconv` does not imply C_hle finite; the scope hypothesis must be `M₂ ≤ M₁`

The corrected statement B.4 encodes convergence through the corank clause
`hconv : (M₀−u) < m − (M₁−u) + 1` (`m = min(M₁,n)−j ≥ a+b`) but carries no explicit `M₂≤M₁` /
pivot-admissibility hypothesis. **`hconv` is insufficient for `C_hle < ⊤`.** Exhaustive search
(`/tmp/chle_sound.py`): **82 genuine cuts where `hconv` PASSES but `(CRIT)` FAILS** — all `M₂>M₁`. Smallest:

    M = (3,3,4,4),  u=2, t=1, j=1:  a=b=1, m = min(3,4)−1 = 2 = a+b  ⟹ hconv holds (corank weight converges),
    yet  u·ρ = 6 < minAdm(2,4,4) = 7  ⟹ C_hle = ⊤ (pivot block diverges).

So a chain can satisfy every current B.4 hypothesis while `C_hle` is infinite — the asserted
`∃ C_hle < ⊤` would be **false** there. **Fix:** the `C_hle < ⊤` clause (and the whole domination) must be
gated by `M₂ ≤ M₁` — equivalently by the sharper pivot-admissibility `u·ρ ≥ minAdm(M')`
(`ρ = min(M₁,…,M_last)`). This is *strictly stronger* than `hconv` on the offending chains and is exactly the
condition that makes BOTH the corank weight (B.2b) and the pivot block (this cert) finite. It unifies the two
wide-chain walls under one clean boundary and closes the soundness gap.

## 7. Decorrelated Codex (my conclusion WITHHELD; prompt framed "either direction")

`codex/s1-Chle-angular-{prompt,answer}.md` (xhigh). Codex CONCURS on every load-bearing point, decorrelated
(my threshold `u·ρ/2`, the `M₂≤M₁` scope, and the soundness example were NOT in the prompt):
- **Threshold [FACT]** `sup{c : J(c)<∞} = u·ρ/2`, via `u` copies of `x↦xQ`, rank `u·ρ`, kernel codim `u·ρ`,
  transversal `∫‖z‖^{−2c}` over `ℝ^{u·ρ}`. Independent of `a,b,n` except through `ρ`. Matches (THRESH).
- **Non-compactness [FACT]** the det-1 sphere non-compactness + `s⁻¹B₁₂` amplification cause **no** extra
  divergence below `u·ρ/2` (box `s·|P̂|≤T` + Jacobian `dB₁₂=s^{ub}dB̃₁₂` compensate the angular tails); and
  **the `σ_min≥σ_max^{−(u−1)} ⟹ bounded` reasoning is WRONG** (RHS `→0`, no uniform bound; integrand
  unbounded for every `c>0` but integrable when `c<u·ρ/2`). Matches §5's correction of A.4 exactly.
- **Comparator [FACT]** finite constant possible ⟺ `minAdm(M') ≤ u·ρ`; worked `(3,3,3)@u=2` → `3=3` equally
  singular, `(3,3,4,4)@u=2` → J-threshold `3 < 7/2` "here J is more singular". Codex independently reproduced
  my exact soundness witness `(3,3,4,4)`.
- **Verdict (b) [FACT]** a finite absorption constant exists **only under `minAdm(M') ≤ u·ρ`**; [INFERENCE]
  it flags that threshold-comparison alone does not by itself pin the constant at criticality — addressed
  here by the equal-rate ratio check at the marginal anchor (§4).

## 8. What the formaliser uses (finite side, in scope `M₂ ≤ M₁`)

1. **Pivot-block finiteness as a linear-image codimension fact** — NOT the det-1 blow-up. Prove `(∗)` finite
   by: `(P,B₁₂) ↦ P·Q_p + B₁₂·Q_b` linear of rank `u·ρ` (`u` copies of `·Q`, `rank Q = ρ`); its zero-locus
   has codim `u·ρ` in the box; `∫_{box} dist^{−2c''}` converges for `c'' < u·ρ/2`. Mathlib has
   `Matrix.rank`, singular-value / eigenvalue API; the "integral of `dist^{−2c}` over codim-`r` locus
   converges iff `2c<r`" is the standard blow-up/monomial lemma the S2 substrate already carries. The
   integrand is genuinely singular (unbounded) — do NOT try to prove it bounded (the A.4 `σ_min` route is a
   dead end; see §5).
2. **The scope hypothesis `M₂ ≤ M₁`** (or the sharper `u·ρ ≥ minAdm(M')`, `ρ = min(M₁,…,M_last)`) gating the
   `C_hle < ⊤` clause — a `decide`-checkable Nat inequality per binding cut. Add it to B.4; drop the reliance
   on `hconv` alone for pivot finiteness (§6).
3. **The `s`-monomial** `s^{u·M₁−1−2c''}` from (JacP)+(homog) matches the comparator `|v|^{jc}` at the anchor
   (`u·M₁−1 = 5 = jc`) and dominates it off-anchor — the blow-up remains the way to EXPOSE the `v`-monomial
   structure to the comparator, even though FINITENESS is cleanest via the compact-box codim (#1).

---

## Close

- **Firmest result.** `C_hle` is FINITE within `M₂ ≤ M₁` (both brief anchors inside, marginal at equality).
  The absorbed integral `(∗)` is over a compact `(P,B₁₂)`-box; its sole singularity is the pivot-energy
  zero-locus of exact codim `u·ρ` (`ρ = min(M₁,…,M_last)`), so `(∗)<∞ ⟺ c'' < u·ρ/2` (exact map-rank verified;
  `u=1` sublevel-volume MC-corroborated; Codex-concurred). C_hle finite ⟺ `u·ρ ≥ minAdm(M')`, which holds for
  every `M₂≤M₁` chain (equality only on equal-width chains). The det-1 sphere non-compactness / `σ_min(P̂)→0`
  worry is a chart artefact, fully tamed by the box + Jacobian; the cert's A.4 "bounded integrand"
  justification is wrong but its in-scope conclusion is right.
- **Most likely to break it.** The `M₂ > M₁` regime: there `u·ρ < minAdm(M')` occurs and `C_hle` genuinely
  DIVERGES (exact witnesses `(3,3,4)@u=1`, `(3,3,4,4)@u=2`), a real second wide-chain wall. And — the
  soundness edge — since `hconv` passes on some of these (`(3,3,4,4)`: `m=2=a+b`), the corrected statement
  B.4 as written asserts a `C_hle<⊤` that does not exist unless the scope is tightened to `M₂≤M₁`.
- **Next.** (a) Formaliser: prove `(∗)` finite via the codim-`u·ρ` linear-image argument (#1), NOT the
  boundedness route; add the `M₂≤M₁` (or `u·ρ≥minAdm(M')`) hypothesis to B.4's `C_hle` clause. (b) Controller:
  decide whether the ∀M mountain carries `M₂≤M₁` (unifying BOTH wide-chain walls — corank B.2b and pivot,
  this cert — under one boundary) or routes `M₂>M₁` through the saturated branch. (c) Optional: confirm the
  marginal-anchor ratio bound (`u·ρ = minAdm(M')`) survives the exact constant chase (equal-rate argument
  §4 is the mechanism); the strict cases (`u·ρ > minAdm(M')`) are comfortable.
