# Design cert — the EDGE direct-coupled bound (`a+b=ρ+1`), formaliser-ready + frontier map

**Seat:** pen-and-paper (design, decorrelated), `genm-corneradj`, follow-on 2. **Date:** 2026-07-16.
**NO Lean.** Math design only (per role: I hand the reduction + CoV + exponent bookkeeping + banked pieces;
the controller synthesises the Lean route). Extends `corner-cert.md` + `corner-cert-addendum.md`. Numerics
guide (`scripts/{spot,scope,deeper}.py`); exact algebra + Codex (`codex/coupled-answer.md`) decide.

---

## ★ SUMMARY

1. **(Part 1) The edge bound.** For a binding cut `u` with `a=M₀−u≥1`, `b=M₁−u≥1`, and `a+b=ρ+1`
   (`ρ=tailMinWidth M`), the honest `shellSpineIntegrand` is finite for every `c' < ½·minAdm M`, via a
   clean **corank polar-`Γ` blow-up** giving reduction `ab/2` into the reduced comparator `redChain u M`.
   The crux new atom is the finiteness, at the edge, of an **angular front charge** `J` (§3) — which
   REPLACES the divergent `Ch` and is finite (log) exactly because the `{Γ=0}` blow-up separates the
   `ab/2` from the corank rank-drop. Per-exponent `C(ε,δ)`; NO endpoint-uniform claim.

2. **(Part 2) Binding-edge spot-check.** `(3,3,4)@t=1` and `(3,4,4)@t=1` (both binding, both `a+b=ρ+1`):
   **NO RLCT-VALUE surprise** — both converge to `½·minAdm M`. `(3,3,4)` (`a=b=2`) reduction = `ab/2` exactly
   (marginal, log at endpoint = correct binding); `(3,4,4)` (`a=2,b=3`) reduction `> ab/2` (extra margin, no
   log stack). The log/multiplicity bump does NOT stack non-transversely; the VALUE `λ=½minAdm` is intact.

3. **(Part 3) Frontier map — NOT one design; but the HARD content is one shared mechanism.** The `{Γ=0}`-
   codim-`ab` mechanism needs `a≥1 ∧ b≥1`, so it is **vacuous** at satred's saturated corner (`a=0`) and at
   the `b=0` output-charge. It covers ONLY the edge `a+b=ρ+1`. The **deeper** corank cuts `a+b≥ρ+2`
   (70 binding cuts in the scan) UNDERSHOOT the clean `ab/2` and need the **joint determinantal rank-sector
   resolution** — the SAME hard content as satred's `A>2Δ` saturated corner. So the coupled frontier is:
   (A) my clean edge `{Γ=0}` brick [`a,b≥1`, `k=1`]; (B) satred's clean saturated fold [`a=0`, `A≤2Δ`];
   (C) satcover's SD-7 [`ab=0`, simplest]; (D) **ONE genuinely-hard build — the joint rank-sector
   resolution — shared by satred's `A>2Δ` AND the deeper corank cuts `a+b≥ρ+2`.** Commission (A),(B),(C) as
   clean bricks and (D) once.

---

## 1. Scope of THIS design (the edge, `k := a+b−ρ = 1`)

`ρ = tailMinWidth M = min(M₁,…,M_last)`. Over binding cuts with `a,b≥1` the scan (`scope.py`) gives
`a+b−ρ ∈ {−3,…,+4}`:

| `a+b−ρ` | # binding cuts | owner |
|---|---|---|
| `≤ 0` (interior) | 307 | front charge / Wishart bolt-on (schurrec) — `Ch<∞`, `corner-cert.md` |
| `= +1` (EDGE) | 205 | **THIS design (`{Γ=0}` clean)** |
| `≥ +2` (deep) | 70 | couplerad E-recursion / joint rank-sector (§4) |

This design is EXACTLY the `k=1` column. `a≥1 ∧ b≥1` is load-bearing (else `{Γ=0}` is vacuous).

## 2. The object (exact, from Lean)

`shellSpineIntegrand M u κ ε r ⟨0⟩ c'` (`RouteMSJDeeperFlagCore.lean:444`), `u=t`, `j=0`:

    ∫_{A' ∈ paramsBoxM(tailChain M) 1 ∩ singularShell ε r ⟨0⟩}
      ∫_{x=(P,B₁₂,C) ∈ outerDom u a b 1}
        ∫_{Γ}  (freedSchurLoss x Γ Q)^{−c'},         Q = (prod(tailChain M) A').submatrix (blockSplitEquiv κ) id,

and (`RouteMSJChartShear.lean:146`)

    freedSchurLoss = frobSq(P·Q̃ₚ)              [PIVOT energy, Γ-free, ≥0]
                   + frobSq(C·Q̃ₚ + Γ·Q_b),     [CORANK energy], Q̃ₚ = Q_p + P⁻¹B₁₂Q_b, Q_b = A_cor·Zf.

Dims (edge `a=b=2,ρ=3` shown): `P` `u×u`, `B₁₂` `u×b`, `C` `a×u`, `Γ` `a×b`, `Q_p` `u×q` (`z₀·Zdeep`),
`Q_b=A_cor·Zdeep` `b×q`, `Zf=Zdeep=deeperFlagZdeep` `M₂×q` (`q=M_last`), rank `ρ` on the shell.
`A_cor` = the `b` corank rows of the leading tail layer `A₀` (a sub-block of the shell-constrained `A'`).

## 3. The reduction (Part 1) — steps, atomic CoV + `|det J|`, exponent bookkeeping

**Target (per-exponent domination).** For each `c' < ½·minAdm M`, pick `δ>0` with `c'−ab/2+δ <
½·minAdm(redChain u M)` (possible: at binding, `½minAdm(redChain)=½minAdm M − ab/2 > c'−ab/2`). Then

    shellSpineIntegrand M u κ ε r ⟨0⟩ c'  ≤  C(ε,δ) · RouteMLayerBoxIntegral (redChain u M) (c'−ab/2+δ) T★,

RHS finite by the arity-IH (`RMBTF(redChain u M)` valid `< ½minAdm(redChain u M)`). NO endpoint-uniform `C`.

**Step A — loss split (banked).** `freedSchurLoss = decLossPart + corankEnergy`, both `≥0`, so
`freedSchurLoss^{−c'} ≤ decLossPart^{−c'}` pointwise (used only for the trivial floor `½minAdm(redChain)`;
the sharp bound uses the corank integration, Step C). Banked: `freedSchurLoss` def, `frobSq_nonneg`.

**Step B — pivot P-radial blow-up (banked, from couplerad `headSplit_domination`).** `P = commonDivisor(v)·P̂`
(`det`-normalised `P̂`), giving the pivot energy `decLoss = commonDivisor(v)²·frobSq(prod(redChain u M) z)`
and reduced params `z`. **ATOMIC — carry `|det J|`:** the P-radial CoV has Jacobian the monomial
`∏_ℓ|v_ℓ|^{jc_ℓ}` (`jc = minAdm(redChain u M)−1`) times the radial factor; this is `k=![1]`, `jc` comparator
data. Do NOT drop it (the recurring tide-D trap). Result: the object becomes
`∫_z ∫_v (∏|v_ℓ|^{jc_ℓ}) · ∫_{A_cor}∫_Γ (decLoss(v,z) + frobSq(Ccross(z) + Γ·A_cor·Zf(z)))^{−c'}`.

**Step C — corank polar-`Γ` blow-up (THE NEW ATOM).** Fix `(z,v)`, write `w := decLoss(v,z) ≥ 0`,
`C₀ := Ccross(z)`, `K := A_cor·Zf(z)` (`b×q`). Polar coordinates on `Γ ∈ ℝ^{ab}`: `Γ = s·Ω`, `s=‖Γ‖_F ≥ 0`,
`Ω ∈ S^{ab−1}`. **ATOMIC — carry `|det J| = s^{ab−1}`** (the standard polar Jacobian). Then (worst case
`C₀=0`, the `C≈0` region that fixes the binding threshold; generic `C₀` only helps, §5):

    ∫_Γ (w + s²·frobSq(ΩK))^{−c'} s^{ab−1} ds dΩ
      = w^{−(c'−ab/2)} · [ ∫_{S^{ab−1}} frobSq(ΩK)^{−ab/2} dΩ ] · B(ab/2, c'−ab/2)      (c' > ab/2),

`B` a finite Beta constant. **This is the exact `ab/2` reduction — from `|det J|=s^{ab−1}` (codim `ab` of
`{Γ=0}`), NOT from a `det(KKᵀ)^{−a/2}` Jacobian.** The reduction is CLEAN and independent of `K`'s rank.

**Step D — the angular front charge `J` (the crux finiteness).** The residual is

    J(z) := ∫_{A_cor ∈ box} ∫_{Ω ∈ S^{ab−1}} frobSq(Ω·A_cor·Zf(z))^{−ab/2} dΩ dA_cor.

`J(z) < ∞` at the edge `a+b=ρ+1` — this is the new lemma that REPLACES the divergent front charge `Ch`.
Mechanism: `frobSq(ΩK)` vanishes on `S^{ab−1}` only where `ΩK=0`; the `A_cor` rank-drop locus (`K=A_cor Zf`
drops to rank `b−1`, codim `ρ−b+1 = a`) makes the `Ω`-integral log-singular but NOT power-singular at
`k=1` (`∫₀ σ^{−1}dσ`-type, the SAME log as `Ch`, now integrated angularly). So `J(z) ~ ln(1/floor)`-mild,
FINITE. [At `k≥2` this angular charge is power-divergent — §4, the deeper regime.] Numerics confirm the
net `H(w) ~ w^{−(c'−ab/2)}·ln(1/w)` (`scripts/tight.py`, `spot.py`): reduction `= ab/2` with a log.

**Step E — fold the log into `+δ`, apply the IH.** `w^{−(c'−ab/2)}·ln(1/w) ≤ C_δ·w^{−(c'−ab/2+δ)}` for any
`δ>0` (log `≤` any negative power near 0). Then `∫_z∫_v(∏|v|^{jc})·w^{−(c'−ab/2+δ)}` **is** `RMBTF(redChain
u M)` at exponent `c'−ab/2+δ`, finite by the IH. This is why the claim is **per-exponent** (`C` blows up as
`c'→½minAdm M` — the log = a **multiplicity/pole-order bump**, not a threshold shift; §Part 2).

**Banked pieces consumed:** `freedSchurLoss`, `frobSq`, `commonDivisor`/`decLoss` (Step A/B, couplerad
`headSplit_domination` for the P-radial CoV data `k=![1],jc`), `RouteMBoxThresholdFinite (redChain u M)`
(the arity-IH, at the bumped exponent `c'−ab/2+δ` and rescaled radius `T★` — `frobSq(prod)` is degree
`2·arity` homogeneous), the shell `σ_min(Zf)≥ε` (keeps `Zf` full rank `ρ`), `minAdm` binding identity
`minAdm M = ab + minAdm(redChain u M)` (`peelCharge`, `RouteMSJResolution`). **New content:** Step C (polar-Γ
`ab/2` reduction) + Step D (`J`-finiteness at the edge). Diamond guard: raw-`Pi` instances for the matrix
products (`lean/CLAUDE.md`).

## 4. Part 3 — does `{Γ=0}` cover the other corners? (frontier map)

**NO — `{Γ=0}` needs `a≥1 ∧ b≥1`.** Precise coverage:

- **satred saturated `a=0` (`A>2Δ`, small-`b`):** at `a=0` there is NO `Γ` (`Γ` is `0×b`), so `{Γ=0}` has
  codim `ab=0` — **vacuous**. This corner's reduction comes entirely from the FRONT reassembly density
  `ρ(z̃₀)` of `[P|B₁₂]·[z₀;A_cor]` (satred §4), and its `A>2Δ` subcase (`A=max_j j(M₂−b−j)`) needs the
  **joint determinantal rank-sector resolution**. NOT covered by `{Γ=0}`.
- **`b=0` output-charge (transpose-dual):** at `b=0`, `Γ` is `a×0` — vacuous. satcover's verdict: `ab=0` is a
  SEPARATE, SIMPLER mechanism (SD-7: drop the empty corner + a single direct pivot-radial blow-up onto the
  reduced chain; the corank Gram divisor is a unit). NOT covered by `{Γ=0}`, but it is the EASY corner.
- **deeper corank `a+b≥ρ+2` (`k≥2`, `a,b≥1`):** `{Γ=0}` still gives the LEADING `ab/2`, but the angular
  front charge `J` (Step D) becomes **power-divergent** (order `~(k−1)/2` at `k`), so the clean bound
  UNDERSHOOTS `½minAdm M` by `~(k−1)/2`. Reaching threshold needs the **joint rank-sector** (the `A_cor`
  rank-drop deficit `a·(b−r)/2` vs its codim must be balanced across strata `r`) — the SAME content as
  satred's `A>2Δ`. (Numeric guide `deeper.py`; couplerad's DEEP E-recursion is the intended owner.)

**Bottom line for the build decision.** The genuinely-HARD content is a SINGLE mechanism — the joint
determinantal rank-sector resolution — shared by satred's `A>2Δ` saturated corner AND the deeper corank
cuts `k≥2`. Commission **one** hard build for it. The remaining corners are clean, separable bricks:
**(A)** this edge `{Γ=0}` design (`k=1`, `a,b≥1`); **(B)** satred's `A≤2Δ` saturated fold; **(C)** satcover
SD-7 (`ab=0`). The edge (A) does NOT need (D) — it is clean (the `J`-log folds via `+δ`).

*(One open question for the controller/couplerad: are the `k≥2` corank cuts actually USED in the flag
coverage, or does the cut-selection route them through the E-recursion so only `k≤1` corank bricks are
built directly? If the coverage uses only `k≤1` corank cuts, (A)+(B)+(C) close the corank+saturated
frontier and (D) is needed only for satred's saturated `A>2Δ`.)*

## 5. Part 2 — binding-edge spot-check (no VALUE surprise; multiplicity does not stack)

`scan.py`: the edge occurs at 205 binding cuts. Two hardest small ones (`scripts/spot.py`, worst case
`Ccross=0`):

| chain@cut | `a,b,ρ` | `½minAdm M` | `½minAdm(redChain)` | reduction (num) | verdict |
|---|---|---|---|---|---|
| `(3,3,3)@t=1` | `2,2,3` | 3.5 | 1.5 (`(1,3)`) | `ab/2=2` (+log) | conv `<3.5`, marginal at endpoint |
| `(3,3,4)@t=1` | `2,2,3` | 4.0 | 2.0 (`(1,4)`) | `ab/2=2` (+log) | conv `<4.0` |
| `(3,4,4)@t=1` | `2,3,4` | 5.0 | 2.0 (`(1,4)`) | `> ab/2=3` (no log) | conv `<5.0`, extra margin |

RLCT **VALUE** `= ½minAdm M` in all cases — **no surprise**. The log-correction (multiplicity/pole-order
bump) appears only where the reduction is exactly `ab/2` (`a=b`, tight); it does NOT stack non-transversely
(`(3,4,4)` with `b>a` has reduction `>ab/2` and negative log-slope — the corank over-covers). For the tide:
claim `λ=½minAdm`; do NOT claim a specific multiplicity `m` at edge cuts unless separately computed.

## Close

- **Firmest result.** The edge `a+b=ρ+1` (`a,b≥1`) has a CLEAN Lean-buildable design: loss-split →
  P-radial blow-up (carry `|det J|=∏|v|^{jc}`) → corank polar-`Γ` blow-up (carry `|det J|=s^{ab−1}`, gives
  `ab/2`) → the angular front charge `J<∞` at the edge (the crux, replaces divergent `Ch`) → IH at
  `c'−ab/2+δ`. Per-exponent, threshold `½minAdm M`, marginal (log) at the endpoint. Spot-checks: no VALUE
  surprise. `{Γ=0}` does NOT cover `a=0` (satred), `b=0` (SD-7), or `k≥2` (joint rank-sector); the HARD
  content is one shared build (joint determinantal rank-sector), covering satred's `A>2Δ` + the deep corank.
- **Most likely to break it.** (i) The `J`-finiteness at the edge (Step D) is the load-bearing new atom —
  it is a mini-front-charge that is finite (log) precisely at `k=1`; a formaliser must prove `J<∞`
  (angular average of `frobSq(ΩK)^{−ab/2}` over `A_cor`), not reuse the divergent `Ch`. (ii) The
  reduced-comparator threshold `½minAdm(redChain)` "in the exponent" is the IH; the `+δ` fold needs the IH
  valid on an OPEN exponent range (it is: `RMBTF` is `< ½minAdm(redChain)`). (iii) `a≥1∧b≥1` scope must be a
  hypothesis — the design is vacuous otherwise.
- **Next.** A formaliser builds (A) [this edge brick]; the crux is Step D (`J<∞` at edge). The hard build
  (D) [joint rank-sector] is satred's open content — one build covers its `A>2Δ` + the deep corank `k≥2`.
