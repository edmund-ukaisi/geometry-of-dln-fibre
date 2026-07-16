# The front-charge off-by-one — threshold `a+b ≤ ρ`; the edge `ρ=a+b−1` DIVERGES; coupled `I` = +∞ (no rescue)

**Seat:** pen-and-paper (obstruction-leaning, decorrelated), aoyagi-full, `genm-corneradj`.
**Date:** 2026-07-16. **NO Lean, NO build.** Exact algebra (four independent derivations) + a
dyadic-shell numerical confirmation (MC is a guide, the exact algebra decides) + a decorrelated
`local-codex-consult` (xhigh, my conclusion WITHHELD — `codex/threshold-{prompt,answer}.md`).
**Decorrelation:** derived from first principles; couplerad's / schurrec's certs read ONLY after my
own answer was locked (reconciliation in §5).

---

## ★ VERDICT

1. **Q1 — `Ch(S)` for fixed generic `S` of rank `ρ` (`b ≤ ρ`): finite ⟺ `a + b ≤ ρ`.** The boundary
   `ρ = a+b−1` (⟺ `a+b = ρ+1`) **DIVERGES logarithmically**. So the test case `b=2, a=2, ρ=3` is
   `+∞`. **schurrec's threshold (`a+b ≤ ρ`) is correct; couplerad's (`a+b ≤ ρ+1`, "shallow" covers
   `ρ ≥ a+b−1`) is off by one — the edge it calls convergent in fact log-diverges.**

2. **Q2 — the honest coupled shell `I` (schurrec's `ChargedRectSchurCore`): `I = +∞` at the edge,
   EXACTLY.** No coupled rescue. `I` factors EXACTLY (Tonelli, nonnegative integrand) as
   `∫_S Ch(S)·Loss(S) dS`; `Ch(S)=+∞` for a.e. `S` and `Loss(S)∈(0,∞)` a.e., so `I=+∞`. This is
   **genuinely different** from the LATE-16/17 reassembly direction-error: there the charge and loss
   shared an integration variable (a lossy Hölder/Cauchy–Schwarz split of a non-separable integral,
   rescued by correlation); here the charge variable `A_cor` and the loss variable `Δ` are **disjoint
   and independent given `S`**, so the factorization is not a bound but the exact value — there is no
   correlation to exploit.

3. **Build consequence — (b)+(c): the edge is DEEP, and needs a genuinely-coupled argument the
   factored route cannot give.** The separable charge×loss object is `+∞` at `ρ=a+b−1` — provably, not
   merely "looks vacuous." Hence: couplerad's shallow/deep boundary must move to **SHALLOW = `ρ ≥ a+b`,
   DEEP = `ρ ≤ a+b−1`** (the edge is the *first* deep value); schurrec's `ChargedRectSchurCore` finiteness
   must carry the scope `a+b ≤ ρ` (excluding the edge — matching its own "rankgen scope OPEN" note); and
   the edge chains (e.g. `(5,5,3,3)@u=3`) must be routed through a joint rank-sector resolution that keeps
   charge and loss **coupled** (does NOT fold `Front ⊥ A_cor`). **This does NOT threaten `(□)`** — it kills
   the *factored route at the edge*, not the RLCT statement (the true, non-separated fibre integral can
   still be finite; §4).

Decorrelated **Codex CONCURS on both Q1 and Q2** (independent derivation, my conclusion withheld) —
including the Tonelli mechanism verbatim: "correlation through `S` cannot produce cancellation" (§6).

---

## 1. The object and the reduction (what actually governs convergence)

`Ch(S) = ∫_{A_cor ∈ [−T,T]^{b×n}} det( (A_cor S)(A_cor S)ᵀ )^{−a/2} dA_cor`, `A_cor` is `b×n`, `S` is
`n×p` of rank `ρ`, the Gram is `b×b`. Assume `b ≤ ρ` (else the `b×b` Gram is identically singular and
`Ch ≡ +∞` trivially).

**Reduction to a `b×ρ` problem (the free directions are a red herring).** Factor `S = L R` with `L`
(`n×ρ`) and `R` (`ρ×p`) each of rank `ρ`. Then `A_cor S = (A_cor L) R`, and with `B := A_cor L` (`b×ρ`)
and `W := RRᵀ` (`ρ×ρ`, SPD),

    det((A_cor S)(A_cor S)ᵀ) = det(B W Bᵀ) = det(B̃ B̃ᵀ),   B̃ := B·W^{1/2}  (invertible reparam of B).

`W^{1/2}` is a fixed invertible change, so the singular locus and the transverse vanishing order match
those of `det(B Bᵀ)`. The map `A_cor ↦ B = A_cor L` is surjective with kernel of dimension `b(n−ρ)`
(rows of `A_cor` orthogonal to `col L`). Over the **bounded** box the integrand is constant along that
kernel, so `∫_box f(B) dA_cor = ∫_{B} f(B)·[fiber-volume(B)] dB` with a bounded, piecewise-polynomial,
positive density. **The `b(n−ρ)` free directions parallel to `ker S` contribute only a finite volume
factor; they do NOT change the codimension or the threshold.** (They would matter only over an unbounded
`A_cor`-domain — an infinite-volume divergence unrelated to the singularity. The singularity here is in
the box *interior*: the locus `{rank B < b}` contains `A_cor = 0`, the box center.)

So convergence of `Ch(S)` ⟺ local integrability of `det(BBᵀ)^{−a/2}` over `B ∈ ℝ^{b×ρ}` near the
rank-drop locus.

## 2. Q1 threshold — FOUR independent exact derivations, all giving `a + b ≤ ρ`

**Singular locus.** `Σ = {B ∈ ℝ^{b×ρ} : rank B < b}` has codimension
`codim Σ = (b−(b−1))(ρ−(b−1)) = ρ − b + 1`.

**(D1) Transverse normal form (exact, sympy `sym_transverse.py`).** At a generic rank-`(b−1)` point,
`det(BBᵀ) ≍ |z|²` with `z ∈ ℝ^{ρ−b+1}` the normal coordinate — a **nondegenerate** (positive-definite)
transverse quadratic (Morse–Bott of corank `ρ−b+1`; higher orders killed). Exact witnesses:
- `b=2, ρ=3`, `r₁ = e₁`: `det(BBᵀ) = z₁² + z₂²` **exactly** (`z ∈ ℝ²`).
- `b=2, ρ=3`, `r₁ = (2,−1,3)`: `det(BBᵀ) = (7/2)(5z_a² − 6z_a z_b + 13z_b²)`, discriminant `65−9=56>0`,
  positive-definite — vanishing order **exactly 2**, transverse dim 2.

Then `det(BBᵀ)^{−a/2} ≍ |z|^{−a}`, and `∫_{ℝ^{ρ−b+1}} |z|^{−a} dz` near 0 converges ⟺ `a < ρ−b+1`.

**(D2) Singular-value Jacobian.** For `B` (`b×ρ`, `b≤ρ`), `dB ∝ ∏_{i<j}|σ_i²−σ_j²| ∏_i σ_i^{ρ−b} dσ`
(verified: `b=1` gives spherical `σ^{ρ−1}`). Integrand `∏σ_i^{−a}`. Near `σ_b → 0` (others bounded, so
Vandermonde `→` const): `∫_0 σ_b^{ρ−b−a} dσ_b`, converges ⟺ `ρ−b−a > −1`.

**(D3) Gram–Schmidt base-height (Codex's tool, exact).**
`det(BBᵀ) = ∏_{j=1}^b dist(x_j, span(x_1,…,x_{j−1}))²` (rows `x_j`). At stage `j` the transverse dim is
`ρ−j+1`; the binding stage is `j=b` (transverse dim `ρ−b+1`) — deeper strata impose **no stronger**
condition.

**(D4) Ingham–Siegel / matrix-variate gamma (Wishart, exact — the couplerad-facing form).** Flat `dB`
pushes to `dW ∝ det(W)^{(ρ−b−1)/2} dW` on `W = BBᵀ ≻ 0`. So near `W=0`,
`∫ det(W)^{−a/2}·det(W)^{(ρ−b−1)/2} dW = ∫ det(W)^{s−(b+1)/2} dW` with `s = (ρ−a)/2`, which converges
⟺ `s > (b−1)/2` (the first pole of `Γ_b`). The single-smallest-eigenvalue stratum binds (deep "all
`λ→0`" strata give the *weaker* `γ > −1 − (b−1)/2`).

All four give the **same** boundary:

    Ch(S) < ∞  ⟺  a < ρ − b + 1  ⟺  a + b ≤ ρ    (integers);
    at a = ρ−b+1 (⟺ ρ = a+b−1 ⟺ s = (b−1)/2):  LOG-DIVERGENT endpoint.

**Calibration (all confirmed by D1–D4 and numerics §3):**

| `(a,b,ρ)` | `a+b` vs `ρ` | transverse dim `ρ−b+1` | `s=(ρ−a)/2` vs `(b−1)/2` | verdict |
|---|---|---|---|---|
| `(2,2,3)` **EDGE** | `4 = ρ+1` | `2` | `1/2 = 1/2` | **LOG-DIVERGE** |
| `(2,2,4)` interior | `4 = ρ` | `3` | `1 > 1/2` | converge |
| `(2,3,3)` deep | `5 = ρ+2` | `1` | `1/2 < 1` | power-diverge |
| `(1,1,1)` `b=1` edge | `2 = ρ+1` | `1` | `0 = 0` | **LOG-DIVERGE** |
| `(1,1,2)` `b=1` interior | `2 = ρ` | `2` | `1/2 > 0` | converge |

**Test case `b=2, a=2, ρ=3` (`S=I₃`, `A_cor∈[−1,1]^{2×3}`): `∫ det(A_cor A_corᵀ)^{−1} dA_cor = +∞`
(log).** Transverse dim 2, integrand `|z|^{−2}` over `ℝ²` ⟹ `∫ r^{−2}·r dr = ∫ r^{−1} dr` diverges.

## 3. Numerical confirmation — dyadic-shell mass (`probe_q1.py`, `probe_q2.py`)

Signature test: bin MC samples by `det(Gram) ∈ (2^{−(k+1)}, 2^{−k}]` and track the integral mass per
octave. **Convergent** ⟹ mass decays geometrically; **log-divergent** ⟹ mass ≈ constant per octave;
**power-divergent** ⟹ mass grows.

- `b=1,a=1,ρ=1` (edge): mass ≈ **0.693 = ln 2 constant** per octave over 25 octaves — textbook log.
- `b=1,a=1,ρ=2` (interior): mass decays `×0.707/octave` — converges.
- **`b=2,a=2,ρ=3` (EDGE): mass rises then PLATEAUS at ≈ 80 per octave** (from `k≈7`) — log-divergent,
  in sharp contrast to `b=2,a=2,ρ=4` (interior) which decays `87→66→38→21→11→…`.
- `b=2,a=3,ρ=3` (deep): mass grows `27→64→119→199→…` — power-divergent.

**Q2 joint probe** (`S` also free, `n=p=3`, edge): joint-front shell mass **grows** per octave
(`5.9k→14k→29k→…→10⁶`) — divergence even stronger than the fixed-`S` log rate (the free-`S` rank-drop
adds strata); adding the loss factor `frobSq(ΔS)^{−c'}` makes the numbers **larger**, never smaller —
no rescue. The interior joint (`n=p=4`) decays and converges.

## 4. Q2 — the coupled shell `I`: `+∞` at the edge, exactly (Tonelli), no rescue

    I = ∫_{Δ,A_cor,S ∈ boxes} det((A_cor S)(A_cor S)ᵀ)^{−a/2} · frobSq(Δ S)^{−c'}  dΔ dA_cor dS.

The integrand is `g(A_cor,S)·h(Δ,S) ≥ 0` with `g` the charge (depends on `A_cor,S`) and `h` the loss
(depends on `Δ,S`). `A_cor` and `Δ` are **disjoint** variables, both coupling only through `S`. By
Tonelli (nonnegative),

    I = ∫_S [ ∫_{A_cor} g dA_cor ] · [ ∫_Δ h dΔ ] dS = ∫_S Ch(S)·Loss(S) dS   (EXACT, not a bound).

For a.e. `S` in the box, `rank S = ρ`. At the edge `ρ = a+b−1`, `Ch(S) = +∞` for **every** such `S`
(§1–2: the locus contains the box center `A_cor=0`; the log-divergence is intrinsic to any full-rank
`S`). `Loss(S) = ∫_Δ frobSq(ΔS)^{−c'} dΔ ∈ (0,∞)` for a.e. `S` (finite for `c' < mρ/2`, i.e. `c'` below
its own threshold; strictly positive). Hence `I = ∫_S (+∞)·(>0) dS = +∞`.

**Why the coupling does NOT rescue (the mechanism, named).** The only coupling that could create a
saving *correlation* between charge and loss would require them to share an integration variable, so that
where the charge blows up the loss is small. Here they do not: `g` sees `A_cor`, `h` sees `Δ`, and these
are integrated independently. `Loss(S)` is a positive multiplicative weight that cannot cancel a `+∞`
which is independent of it. **Neither `S`-integration nor the loss factor regularizes.**

**Why this is NOT the LATE-16/17 direction error.** That trap was a *lossy* bound
(`I ≤ ‖charge‖·‖loss‖` via Hölder/Cauchy–Schwarz, or a factorization across a **shared** variable) of a
genuinely non-separable integral: the bound was `+∞` while the true joint was `Θ(1)` because the
blow-up region had small loss (correlation). Here the object as defined is *already separable* — Tonelli
makes the factorization the **exact value**, so there is no Hölder slack to recover. The `+∞` is real
**for this object**.

**What this does and does NOT say about `(□)`.** It says the *separable charge×loss object* is `+∞` at
the edge. schurrec's docstring records that the folding step which produces that object is "pointwise
FALSE `Front ⊥ A_cor`" — i.e. `ChargedRectSchurCore` is a **separated over-estimate** of the true
(non-separated) fibre integral, in which the loss and charge share the underlying data. My argument does
NOT compute that true coupled object; it shows the separated one is vacuous at the edge. The LATE-16/17
precedent shows a genuinely-coupled object *can* be finite where its factored bound is `+∞`. So: **KILL
for the factored route at the edge; NOT a kill for `(□)`.**

## 5. Reconciliation — who is right, and where couplerad erred

- **schurrec (`RouteMSchurRectCharged.lean`): RIGHT on the threshold.** Its charged core is
  charge-agnostic at `δ=0` with threshold `½·minAdm(![m,n,p])`, and it explicitly flags the **"rankgen
  scope OPEN"** (docstring §"OPEN"): "off the binding-shell rankgen (`a+b ≤ ρ−1`) the charge lowers the
  codim below the floor, so the `δ=0` claim NEEDS a rankgen hypothesis." schurrec has **not** claimed the
  edge closed — correct. Its `ChargedRectSchurCore` **is exactly my `I`** (three free boxes `Δ,A_cor,S`;
  integrand `det((A_cor S)(A_cor S)ᵀ)^{−a/2}·frobSq(ΔS)^{−c'}`), and it is `+∞` at the edge, so its
  finiteness predicate must carry `a+b ≤ ρ` (excluding the edge). This matches, not contradicts, §4.

- **arch1build: RIGHT on the edge.** "j=0 at `a+b=ρ+1` ⟹ factored charge `+∞` ⟹ fold VACUOUS there
  (LATE-16 trap); HELD." Confirmed exactly. Its independent statement "charge finite iff `a+b ≤ M₂`
  (Wishart)" (arch1-cert L75) equals my `a+b ≤ ρ`.

- **couplerad: OFF BY ONE at the boundary.** Its "shallow = `rank S ≥ a+b−1` = Wishart bolt-on (finite)"
  puts the edge `ρ = a+b−1` on the **convergent** side. The precise error: the Wishart / multivariate-
  gamma criterion is **strict**, `s = (ρ−a)/2 > (b−1)/2` ⟺ `ρ ≥ a+b`; couplerad used the **non-strict**
  `s ≥ (b−1)/2` ⟺ `ρ ≥ a+b−1`, i.e. it counted the **first pole** `s=(b−1)/2` of `Γ_b` (equivalently the
  radial endpoint `a = ρ−b+1`, `∫ r^{−1}dr`) as convergent. It is the log-divergent endpoint. **The
  Wishart bolt-on is correct only for `ρ ≥ a+b` (strict); `ρ = a+b−1` is DEEP.** (couplerad's *own*
  `coupling-verdict-cert.md` §3 already saw a sibling of this: off-shell `A_cor` rank-drops degrade the
  pivot threshold `uρ/2 → 5/2`, excluded by a shell — the same corner, seen from the pivot side.)

## 6. Decorrelated Codex (my conclusion WITHHELD; `codex/threshold-{prompt,answer}.md`, xhigh)

Independent derivation, **CONCURS on both**:
- **Q1 [exact]** `Ch(S) < ∞ ⟺ a < ρ−b+1 ⟺ ρ ≥ a+b`; `codim = ρ−b+1`, `det(XXᵀ) ≍ |z|²`, `∫r^{d−1−a}dr`,
  log-divergence at `a=d`; edge `ρ=a+b−1` diverges; test case `+∞`. Free directions: "over a bounded box
  contribute only a finite, locally positive fibre-volume factor" — no threshold change. Supplied the
  base-height identity `det = ∏ dist(x_j, span(<j))²` (D3).
- **Q2 [exact]** `I = +∞`: "for a.e. `S`, `rank S = ρ`, Tonelli gives (∫_A f_S)(∫_Δ g_S); the first is
  `+∞`, the second finite positive ⟹ inner `+∞` for a.e. `S` ⟹ `S`-integral `+∞`. Neither varying `S`
  nor the loss factor can regularize. The decisive mechanism is nonnegative Tonelli factorization
  conditional on `S`; correlation through `S` cannot produce cancellation." Verbatim my §4.

## Close

- **Firmest result.** `Ch(S) < ∞ ⟺ a+b ≤ ρ`; the edge `ρ = a+b−1` log-diverges (four exact derivations +
  dyadic-shell numerics + decorrelated Codex). The coupled `I` (= schurrec's `ChargedRectSchurCore`) is
  `+∞` at the edge, exactly, by nonnegative Tonelli factorization `I = ∫_S Ch(S)Loss(S)dS` — no rescue
  from `S`-integration or the loss factor; genuinely different from LATE-16/17 (charge ⊥ loss on disjoint
  variables). **schurrec/arch1 right; couplerad off by one** (non-strict `s ≥ (b−1)/2` at the first `Γ_b`
  pole). **Build: the edge is DEEP** — move the shallow/deep boundary to `ρ ≥ a+b` / `ρ ≤ a+b−1`, scope
  the separable charged core to `a+b ≤ ρ`, route edge chains (e.g. `(5,5,3,3)@u=3`) through a coupled
  (non-folded) rank-sector resolution. `(□)` is **not** threatened — only the factored route at the edge.
- **Most likely to break it.** The verdict is exact for the object **as literally defined** (independent
  `A_cor, Δ, S` boxes). It would change ONLY if the real assembly object is *not* separable — e.g. the true
  fibre integral ties `A_cor` to the loss's data (then Tonelli does not apply and the LATE-16 rescue can
  recur — the true coupled object may be finite), or the effective charge exponent at the edge chain is not
  `a/2` (a Jacobian shift). Both are for the controller to check against the real reduction; my `+∞` binds
  the *separated* object regardless.
- **Next.** (i) Confirm whether the item-4 reduction to `ChargedRectSchurCore` is an EXACT reduction or a
  factored UPPER BOUND of the true fibre integral — if a bound, the edge `+∞` is a vacuous-bound (route
  fix), not a `(□)` risk; if exact, `(□)` at edge chains genuinely needs the coupled resolution. (ii) The
  concrete coupled object to test for the edge (`(5,5,3,3)@u=3`, `a=b=2, ρ=3`): the *non-separated*
  `∫ det((A_cor S)(A_cor S)ᵀ)^{−a/2}·frobSq(ΔS)^{−c'}` where `A_cor` and `Δ` are tied to the same fibre
  data — is IT finite? That is the pen-and-paper follow-on that settles the build route.
