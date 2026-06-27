# Thread 02 — R1 the decisive computation (pen-and-paper)

**Target:** the local rlct of the DEEPEST stratum of the fibre for `(2,2,2,2,2)`, `r=0` (the |δ|=2 witness where the three θ-invariants diverge). Confirm it equals ½·codim (mildness holds; the wall is surmountable) or is strictly less (the cited equality is subtler than stated — a genuine finding). Exact algebra (sympy/Newton-polyhedron); decorrelated Codex. Output: the local-rlct value + certificate.

## RESULT (certificate)

**Verdict: MILD.** Local rlct at the deepest stratum (origin) `λ = 3/2 = ½·codim`. The cited Aoyagi equality is clean at this `|δ|=2` witness. Two independent routes agree on `3/2`; the value is rigorously bounded `≤ 3/2` and corroborated `= 3/2`.

The genuinely informative side-finding (for R3): the Newton polyhedron of `K` in the **standard coordinates** does NOT compute the rlct (proven Newton-DEGENERATE). The naive toric/Newton value is `2 ≠ 3/2`. So R3's high-value "cite one Saito–Varchenko theorem" gamble fails for the coordinate Newton polyhedron — a determinantal/rank-aware resolution is needed (or a coordinate change that makes a resolved Newton polyhedron nondegenerate, which is what both routes below effectively do).

### Conventions confirmed (from the repo)
- `mult d A = A_{N-1}·…·A_0` (prefix product; `Core.MultComorphism`), here the 2×2 product `P = A₄A₃A₂A₁` of the 4-arrow chain `2→2→2→2→2`.
- Fibre over `B` = `{A : mult A = B}`; over `B=0` it is the zero-product locus `Σ⁰ = {A₄A₃A₂A₁ = 0}`.
- Loss `K = ‖mult A − B‖²_F`; at `B=0`, `K = Σ_{i,j}(A₄A₃A₂A₁)²_{ij}` = sum of `c=4` squared product entries.
- Deepest point = origin (all `Aᵢ = 0`).
- Watanabe RLCT `λ(K) = sup{z : ∫ K^{−z} φ < ∞ near 0}`. Locked against exact benchmarks: `λ(Σ_{i=1}^c xᵢ²) = c/2` (`x²`→1/2, `x²+y²`→1, codim-3 CI→3/2).

### The explicit K
16 variables (4 matrices × 4 entries). `K` is **multi-homogeneous of degree (2,2,2,2)** — degree exactly 2 in each matrix block (every one of its 136 monomials picks two paths, one entry per matrix per path). Total degree 8. Each product entry `P_{ij}` is a sum of `2³=8` degree-4 path monomials; `K = Σ P_{ij}²`.

### Codimension (the comparison target)
Exact, via rank-pattern stratum dimensions of `Σ⁰` (stratum dim `= Σᵢ (d_{i−1}−s_{i−1})d_i + s_i(s_{i−1}+d_i−s_i)`):
- `dim Rep = 16`, `dim Σ⁰ = 13`, so `C = codim = 3`.
- `δ = r(d₀+d_N−r) = 0` (r=0) ⇒ `codim = C = 3`; `½·codim = 3/2`.
- **6** distinct codim-3 top rank-patterns — matches the θ-count `binom(4,2) = 6` from `docs/expositions/theta-invariants-distinction.md`.
- Cross-check: repo `Aoyagi.ClosedForm.lambda(d22222,0) = 3/2 = C/2` (matches for ALL tested cases `(2,2,2)→3/2`, `(3,3,3)→7/2`, `(2,2,2,2)→3/2`, `(2,2,2,2,2)→3/2`, `(4,4,4)→6`, `(3,3,3,3,3)→3`).

### Method 1 (mine): rigorous upper bound + degeneracy + mechanism
- **Upper bound `λ ≤ 3/2` (RIGOROUS, exact).** At a generic point of any codim-3 top component the Jacobian of the 4 product entries has rank **exactly 3** (verified: smooth, codim 3, dim 13). So `Σ⁰` is locally a smooth codim-3 complete intersection there → local rlct `= 3/2`. The origin lies in the closure of these top components, so its local rlct (cutoff includes nearby smooth top points) is `≤ 3/2`.
- **Newton-DEGENERACY (RIGOROUS, exact).** The principal (compact) face of `Γ₊(K)` is `K` itself (multi-homogeneity ⇒ A-block degree constant). Explicit torus critical point: `A₁=A₂=A₃=[[1,1],[1,1]]`, `A₄=[[1,−1],[2,−2]]` — all 16 entries ≠ 0, `A₄A₃A₂A₁ = 0` exactly, so `K=0` and (sum of squares) `∇K=0`. By Kushnirenko–Varchenko this makes `K` Newton-degenerate; the naive toric/Newton bound (LP `inf|w|/ord = 2`) is NOT the rlct.
- **Mechanism for why `2 → 3/2`.** Iterated quadratic integral: integrating out the leftmost factor `A_N` given the running product `W` yields a factor `(pseudodet W)^{−d_N}` — a *determinantal* weight that lowers the threshold below the per-block radial bound 2. The rlct is genuinely a nested determinantal-singularity quantity, not a monomial/toric one.
- **Lower bound `λ ≥ 3/2` (the WALL).** This is exactly Aoyagi mildness; NOT float-certifiable here (see below). Corroborated by Method 2 + the validated formula; the formal proof is R3's job.

### Method 2 (decorrelated Codex, xhigh, independent route) — `codex/rlct-value-answer.md`
Reported `λ = 3/2` FIRST (before seeing my value/the ½·codim target). Independent route: SVD/rank blow-up `Aᵢ = ρᵢUᵢ` (radial threshold 2, not binding) → resolved angular entry-ideal `J = ⟨zr−cp, a(c−zq), dr, adq⟩` in 7 angular variables → toric LP on the *resolved* ideal gives `lct(J)=3` → half for sum-of-squares → `λ = 3/2`. Independently confirmed: `K` Newton-degenerate (same torus-zero mechanism), naive value 2 not tight, and the rank-one-bottleneck local model `= u₁²+u₂²+c₁²` (three independent squares) → 3/2. Disagreement: Codex pole multiplicity `m=4` vs repo/Aoyagi `m=5` — Codex self-flagged moderate confidence ("missed binomial-cancellation chart"); the VALUE 3/2 is robust, the multiplicity is the soft part and is not R1's question.

### Validation of the pipeline (where float CAN certify)
- `(2,2,2)` r=0 (multiplicity `m=1`, no log confound): clean tail-slope numeric → `λ ≈ 1.55→1.5` as `t→0`, matches `C/2 = 3/2` AND the classical peer-reviewed Aoyagi–Watanabe (2005) reduced-rank-regression value. Pipeline sound.
- `(2,2,2,2,2)` r=0 numeric (Gaussian sampling, 40–200M): tail index `≈ 1.2–1.5`, multiplicity-confounded — with `m=5` the log factor biases the naive `log V/log t` slope DOWN; the `m`-corrected fits sit at `~1.5`, consistent with `3/2` but NOT discriminating `3/2` from `<3/2` on float alone. **This is the float-doesn't-certify wall**; the exact upper bound + two-route `3/2` is what certifies.

## (a)(b)(c) for the interface scout's Newton-nondegeneracy question
- **(a)** Newton polyhedron `Γ₊(K) = conv(136 monomials)+ℝ₊¹⁶`; all monomials degree 8, multi-homogeneous degree `(2,2,2,2)`; principal compact face = `K` itself.
- **(b)** `K` is **Newton-DEGENERATE** (explicit torus critical point above; Kushnirenko–Varchenko fails on the principal face). The standard-coordinate Newton polyhedron does NOT compute the rlct (it gives 2, the true value is 3/2). Matches the cusp warning (degeneracy off coordinate hyperplanes).
- **(c) Verdict: R3-Newton NOT viable in standard coordinates → R3-resolution needed** (rank/SVD blow-up à la Aoyagi, or determinantal-aware). Caveat/opening: BOTH routes resolve to a tractable model AFTER a rank/SVD coordinate change — Codex's resolved angular ideal is toric and gave `lct=3` cleanly. So a *refined* gamble survives: "Newton-nondegenerate after the rank/SVD blow-up chart" may discharge R3 with a Saito–Varchenko-type theorem applied in the RESOLVED chart. Worth R3 probing whether the resolved-chart Newton polyhedron is provably nondegenerate.

## Confidence
- `C = 3`, `½·codim = 3/2`: **certain** (exact, two methods, matches banked repo values + θ-count).
- `λ ≤ 3/2`: **certain** (exact Jacobian-rank-3 smooth top stratum).
- Newton-degeneracy of `K` (standard coords): **certain** (exact torus critical point).
- `λ = 3/2` (MILD): **high** — rigorous upper bound `3/2` + decorrelated Codex `3/2` + validated Aoyagi formula `= C/2` + clean `(2,2,2)` validation. The only un-discharged piece is the rigorous lower bound `λ ≥ 3/2` (the R3 wall); no evidence of `< 3/2`.
- Pole multiplicity: `m=5` (Aoyagi/repo) vs Codex `m=4` — UNRESOLVED, low stakes for R1.

## Most likely way this is wrong
A hidden deeper-corner stratum with local rlct `< 3/2` that the smooth-top-stratum upper bound and both resolution routes miss (a "missed chart"). The mitigation: the lower-bound `λ ≥ 3/2` must be proved in R3, not assumed; if some corner gives `< 3/2`, the headline flips to SUBTLE. Current evidence (two routes + validated formula) points firmly to MILD.

## Next move to settle the open part
The rigorous lower bound `λ ≥ 3/2`: either (i) finish the iterated determinantal integral for the width-2 chain exactly (track the `(pseudodet)` cascade, validate against `(2,2,2)`), or (ii) prove the resolved angular ideal (Codex's `J` chart) is Newton-nondegenerate and apply the Newton-polyhedron rlct theorem there. Route (ii) is the cheaper R3 path if it holds.

---
*Codex artefacts: `codex/rlct-value-prompt.md`, `codex/rlct-value-answer.md`. Scratch scripts in `/tmp` (rank-pattern codim, Newton LP + torus-degeneracy, Jacobian-rank, numeric tail/Hill, Aoyagi-formula sweep).*
