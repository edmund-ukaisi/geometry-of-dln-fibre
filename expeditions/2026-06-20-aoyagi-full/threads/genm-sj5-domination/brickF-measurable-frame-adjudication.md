# Brick-F measurable-frame adjudication — the `measurableEigendecomp` primitive: LABOUR (contour-free algebraic recipe), no KRN

**Seat:** pen-and-paper (design-space math, one truth-value, decorrelated), aoyagi-full Stage 2,
`genm-sj5-domination`. **Date:** 2026-07-13. **NO Lean edits, NO git, NO build.** Exact algebra
(sympy, `/tmp/measframe_verify.py`) + numeric guide (labelled, guide only). Decorrelated
`local-codex-consult` (xhigh, my LABOUR/WALL conclusion WITHHELD — "argue whichever direction is
correct"): `codex/brickF-measframe-{prompt,answer}.md`.

**The truth-value adjudicated** (the controller's sharpened, verbatim primitive — the sole remaining
Mathlib void of the (□) endgame). For a measurable Hermitian family `A : X → Matrix (Fin M₂)(Fin M₂) ℝ`
(`hA : Measurable A`, `hherm : ∀z, (A z).IsHermitian`):

    Measurable (fun z => (hherm z).eigenvalues₀)                                       -- conjunct (i)
    ∧ ∃ U, Measurable U ∧ (∀z, (U z)ᵀ*U z = 1)
         ∧ (∀z, A z = U z * diagonal(sorted eigenvalues) * (U z)ᵀ)                     -- conjunct (ii)

Can `U` be a **CONCRETE Borel formula** in the entries of `A`, through **degenerate eigenspaces**,
**WITHOUT** any Kuratowski–Ryll-Nardzewski / von-Neumann / Jankov measurable-selection theorem (which
Mathlib entirely lacks)?

---

## ★ HEADLINE VERDICT: **LABOUR.** Both conjuncts are an explicit Borel formula; **no KRN, no contour integral**.

- **Conjunct (i)** — `Measurable eigenvalues₀`. Rests on **Weyl's perturbation inequality**
  `maxᵢ |λᵢ(A) − λᵢ(B)| ≤ ‖A − B‖_op` ⟹ sorted eigenvalues are (Lipschitz-)**continuous** in `A` ⟹ Borel.
  The ~1-module "Weyl brick" the recon flagged. **[FACT / STANDARD].** (Measurability alone would even
  follow from measurable-dependence of polynomial roots on the char-poly coefficients; continuity is the
  cleaner sufficient route.)
- **Conjunct (ii)** — the full sorted diagonalizing `U`. **LABOUR** via the **stratified-Sylvester +
  Gram-Schmidt-pivot** construction below. The `O(k)` within-degenerate-block ambiguity — the controller's
  identified crux, where KRN *would* enter — is collapsed to a **single canonical representative by a
  deterministic formula**, not an abstract selection. **The two obstacles in the brief DISSOLVE** under
  the controller's full-`U` reframing (build all eigenvalues sorted, select top-`m` by the constant index
  map). Decorrelated Codex reached the **identical** construction and verdict independently.

**This decides F2 = LABOUR (a build recipe for `U`), NOT a wall.** The one genuine non-labour escalation
the recon feared (KRN unavoidable at degenerate blocks) **does not materialise**: finite-dimensional +
semialgebraic ⟹ a definable-by-cases section, which is constructive.

---

## The construction (the certificate object) — stratified Sylvester + Gram-Schmidt-pivot

Fix `N := M₂`. All ingredients are exact rational/`sqrt` operations on the entries of `A(z)` and the
(measurable) eigenvalues.

**Step 1 — sorted eigenvalues (conjunct (i)).** `λ₁(z) ≥ … ≥ λ_N(z)`, measurable by Weyl (above).

**Step 2 — finite multiplicity-pattern stratification.** Partition `X` by the *coincidence pattern* of
the sorted eigenvalues: a composition `α = (m₁,…,m_r)` of `N` recording which consecutive sorted
eigenvalues are equal. Writing `s_a = m₁+…+m_a`, the stratum
`S_α = {z : λ_{s_{a-1}+1} = … = λ_{s_a} for each a, and λ_{s_a} > λ_{s_a+1} for a<r}` is a **finite
Boolean combination of `{λᵢ = λ_{i+1}}` / `{λᵢ > λ_{i+1}}`** conditions on measurable functions ⟹ **Borel**
(and semialgebraic in the entries by Tarski–Seidenberg, but that is not needed for measurability).
**Finitely many strata** (one per composition of `N`). On `S_α` the *distinct* eigenvalues
`μ₁ > … > μ_r` are separated and measurable.

**Step 3 — Sylvester (Lagrange) eigenprojection, per stratum.** On `S_α`,

    P_a(z) = ∏_{b ≠ a} (A(z) − μ_b(z)·I) / (μ_a(z) − μ_b(z))

is the **exact orthogonal projection onto ker(A − μ_a I)** — a rational function of the entries and the
`μ`'s (denominators nonzero on `S_α`), hence **continuous on `S_α`**. **[EXACT, verified]:** idempotent
`P²=P`, symmetric `P=Pᵀ`, eigenprojection `A·P = μ·P`, rank `= m_a`. This is **matrix-polynomial
arithmetic + division by measurable eigenvalue-gaps — NO contour integral, NO resolvent, NO holomorphic
functional calculus** (all absent from Mathlib).

**Step 4 — deterministic ONB of each block (this is where KRN would have entered; it does not).** The
columns `{P_a e₁, …, P_a e_N}` span `range P_a`. For each size-`m_a` subset `I ⊆ {1..N}` set
`d_I = det((V_I)ᵀ V_I)`, `V_I = [P_a e_{i₁} … P_a e_{i_{m_a}}]` (a Gram minor). Some `I` has `d_I > 0`
(the columns of a rank-`m_a` projection contain `m_a` independent ones). Take the **lexicographically
first** such `I`: the cell `C_I = {d_I ≠ 0} ∩ ⋂_{J<I} {d_J = 0}` is **Borel** (finite Boolean combo of
polynomial conditions). On `C_I`, ordered Gram-Schmidt of `V_I` is a **continuous** (rational + `sqrt`)
ONB of the eigenspace. This is a **finite deterministic case-split**, not a continuum selector.

**Step 5 — assemble in sorted order.** Concatenate the block frames `U = [Q₁ | … | Q_r]`. Eigenspaces
are orthogonal ⟹ `Uᵀ U = 1`; the sorted order places each block into a **FIXED index range** (the
controller's `Fin.castLE` point — no per-point column choice), giving `A = U · diag(λ↓) · Uᵀ`.

`U` is **measurable** as a finite glue of continuous-on-Borel-cells functions (Step 2 × Step 4 = finitely
many Borel cells, continuous formula on each). **No measurable-selection theorem.** Codex adds: standard
Borelness of `X` is not even needed — the construction is pointwise-defined-by-formula.

---

## Where the two brief-obstacles go — both DISSOLVE under the full-`U` reframing

**Obstacle 1 (spectral-gap dependence at `ε'²`) — DISSOLVED.** Building the *full* sorted eigendecomposition,
one **never places a contour at `ε'²`**. The threshold enters only through `weakEigCount ε'` (= #{eigenvalues
`< ε'²`}, measurable from conjunct (i)), which defines the good set `G = {weakEigCount ε' ≤ M₂ − m}`. The
`≥ε'²`-frame is `U_sf = ` first `m` columns of `U`; on `G` the top `m` eigenvalues are `≥ ε'²`, giving the
Loewner floor **with no gap at `ε'²` required** — only the *inter-eigenvalue* separations matter, and those
are handled by the stratification (Step 2). **[EXACT, E3]:** the 3×3 family `A(t)=Q·diag(2+t, 1+t², ¼−t)·Qᵀ`,
`ε'²=½`, `m=2`: `weakEigCount = 1 = M₂−m` on `t∈[0,¼]` (so `z∈G`), and the congruence-diagonalized floor
`Uᵀ(AAᵀ − ε'²·U_sf U_sfᵀ)U = diag(g₁²−½, g₂²−½, g₃²)` is PSD throughout — **even as `g₃=¼−t` sits below
`ε'²` and the count would jump at the crossing locus `{det(A−ε'²I)=0}`**; the construction is indifferent to
that locus.

**Obstacle 2 (rank/dimension jumps of `range P`, "select `m` columns measurably = smuggled KRN?") — DISSOLVED.**
There is no single `range P` whose rank jumps: `U` is always `N×N` orthogonal, `U_sf` is always exactly `m`
columns (the **constant** index map — not a choice). The `#{eigenvalues ≥ ε'²}` jump is absorbed by Brick
F's *existing* piecewise device (`Zf = Zdeep`/`U_sf` on `G`, fixed `V` off `G`). The only place a "which"
could hide — the ONB of a degenerate block — is fixed by the Step-4 formula (lex-first pivot on Borel
`{Gram-minor ≠ 0}` cells). **NOT KRN.** **[EXACT, E5]:** multiplicity merge `A(s)=Q₂·diag(1+s,1−s,0)·Q₂ᵀ`;
at `s=0` the rank-2 block gets its ONB by Gram-Schmidt of the rank-2 Sylvester projection, `U₀ᵀU₀ = I₃`,
`U₀ᵀA(0)U₀ = diag(1,1,0)` — exact.

---

## The sharpest test — the diabolical point (no *continuous* choice, yet an explicit *Borel* formula)

`A(x,y) = [[x, y],[y, −x]]` on `X = ℝ²`, eigenvalues `±r`, `r = √(x²+y²)`; conical intersection at `0`.
**[EXACT, E1/E2]** Sylvester `P₊ = (A + rI)/(2r)` verified idempotent/symmetric/eigenprojection. The
Step-4 pivot gives

    u₊(x,y) = (r+x, y)ᵀ / √(2r(r+x))   where  ‖P₊e₁‖² = (x+r)/(2r) > 0   [exact closed form confirmed],
              e₂                        on the ray {y=0, x<0}  (where P₊e₁ = 0, pivot to column 2).

The eigenvector is **exact** (`A·P₊ = r·P₊` proved exactly ⟹ `A·col1 = r·col1`; numeric check
`max‖Au−ru‖ = 4e−12` over 1e5 points confirms the nested-radical residual is genuinely 0). Full `U`'s
discontinuity locus is the whole `x`-axis `{y=0}` (`u₊` jumps on `x<0`, `u₋` on `x>0`), of **measure zero
and Borel**. **[FLOAT GUIDE]** the eigenvector carries an **odd** sign-flip around a loop enclosing `0`
(Berry phase) ⟹ **no global continuous choice exists** — yet the measurable-by-formula choice succeeds.
This is the sharpest possible probe of the degenerate-block/KRN worry: **exactly where continuity provably
fails, the concrete Borel formula still delivers `U`.** (Codex names the same object — the Möbius rank-one
projector `P(θ)` — as the "cheapest kill": replacing "Borel" by "continuous" flips the verdict; under Borel
it does not.)

---

## Structure & ideas observed (data, not a prescribed Lean route)

- **The load-bearing invariant** is the *multiplicity-pattern stratification*: over a semialgebraic base,
  the eigendecomposition is **definable by finitely many cases**, each a continuous rational+`sqrt`
  formula. Measurable diagonalization needs KRN **only in infinite dimensions** (von Neumann); the finite,
  semialgebraic case is constructive. The whole KRN scare is an infinite-dimensional import that does not
  bite here.
- **The mechanism why obstacles 1/2 vanish:** decoupling *what carries the threshold* (`weakEigCount`, a
  measurable **count**) from *what carries the frame* (the full sorted `U`, an algebraic **formula**). The
  threshold `ε'²` never touches the eigenvector construction; it only indexes the good set and the constant
  column-selection. This is the controller's "build the full decomposition, select top-`m` by `Fin.castLE`"
  reframing, and it is exactly what removes the gap-at-`ε'²` requirement.
- **[Speculation — decorrelation-safe structural observation, corroborated by Codex, ranked independently]**
  The **algebraic Sylvester route (candidate (b)/(c)) strictly dominates the resolvent-Riesz contour route
  (candidate (a))** for a finite-dimensional formalisation: (a) needs a parameter-dependent complex contour
  integral of a matrix-valued resolvent (an analytic primitive Mathlib lacks and the recon rightly flagged
  "heavy"); (b)/(c) need only matrix-polynomial arithmetic + division by measurable gaps + Gram-Schmidt
  (all present or elementary). **This removes "contour-integral-of-a-matrix" from the critical path
  entirely** — a real de-risking of the recon's proposed F1. (Reported as structure/idea; I hold no
  Mathlib-feasibility model and do not prescribe the Lean proof route — the controller synthesizes that.)
- **[Question]** The genuinely-new Lean pieces (each elementary, none a wall): (1) Weyl-continuity of
  `eigenvalues₀` [conjunct (i)]; (2) the multiplicity strata as Borel sets; (3) Sylvester-projection
  measurability on strata; (4) Gram-Schmidt measurability + the lex-first pivot; (5) finite-glue
  measurability of the assembly. Which of these already has partial Mathlib support (Gram-Schmidt is
  present; the eigenvalue-continuity brick is the recon's flagged absence) is a formaliser-scoping
  question, not a truth-value one.

---

## Decorrelated Codex (my conclusion WITHHELD; prompt framed "argue whichever direction")

`codex/brickF-measframe-{prompt,answer}.md` (xhigh). Codex **independently reconstructed the identical
construction** and verdict — genuine decorrelation (the LABOUR conclusion and the Sylvester/stratification
idea were NOT in the prompt; the prompt offered (a)/(b)/(c) neutrally and asked to rank them):
- **(i) [FACT/STANDARD]** Weyl ⟹ continuous ⟹ Borel. (Concurs.)
- **(ii) [FACT] LABOUR** — explicit Borel diagonalizer, no selection theorem, "standard Borelness of `X`
  not even needed." (Concurs.)
- **Degenerate block** — same multiplicity-stratum `S_α`, same Sylvester `P_a`, same lex-first Gram-minor
  pivot `C_I`, same finite-Borel-pasting. (Identical to Steps 2–5.)
- **Diabolical point** — same `u₊` formula, discontinuity locus `{y=0}`, Borel. (Concurs; enriches my
  `u₊`-only trace with the `u₋` cut on the positive axis.)
- **Candidate ranking [FACT]:** **(c) best, (b) second, (a) last** — "(a) works but introduces an
  unnecessary analytic primitive (parameter-dependent complex contour integration) for Lean." (Matches my
  independent structural observation above.)
- **Cheapest kill:** the continuous-vs-Borel boundary — replacing Borel with continuous flips it. (This is
  precisely the diabolical-point Berry-phase fact; names the exact scope of the theorem.)

The concurrence is decorrelated: two independent derivations, same object, same ranking, same scope.

---

## Close

- **Firmest result.** `measurableEigendecomp` is **LABOUR**: the full sorted orthogonal `U` is a concrete
  Borel formula (stratified Sylvester eigenprojection + lex-first-pivot Gram-Schmidt), verified exactly on
  the diabolical point, a 3×3 threshold-crossing (obstacle 1), and a multiplicity merge (obstacle 2).
  **No KRN, no contour integral.** The `O(k)` degenerate-block ambiguity — the identified crux — is
  collapsed by a deterministic formula, not a selection. Conjunct (i) is the Weyl-continuity brick.
  Decorrelated Codex independently reproduced the construction, ranking, and scope.
- **Scope named precisely.** The theorem is **TRUE for Borel/measurable `U`**; it is **FALSE for continuous
  `U`** (the diabolical-point Berry-phase obstruction — the exact continuous/Borel dividing line). The
  verdict is about *existence of a Borel formula*, not Lean line-count (I hold no Mathlib-feasibility
  model). Levels kept separate: this is the abstract measurable-diagonalization primitive; Brick F's
  `exists_headSplitFrame` wraps it with the good-set/piecewise-`Zf`/Loewner-floor bookkeeping (the floor
  verified in E3), a distinct and straightforward level given the primitive; the RLCT payoff is a third.
- **Most likely to break it (implementation friction, not a math wall).** The Lean formalisation of (2)
  the multiplicity strata as Borel sets and (4) Gram-Schmidt *measurability with pivoting* may need
  constant-rank / continuity-on-cells lemmas that are painful at the v4.29 pin; and (1) `eigenvalues₀`
  continuity must be built from scratch (Mathlib's `eigenvalues₀` is choice-built, no measurability rider).
  These are labour, not a wall — **there is definitely no KRN requirement**.
- **Next construction / consult that would settle the open part.** (a) A formaliser-scoping pass on which
  of the five new pieces has Mathlib support at the pin (Gram-Schmidt present; the Weyl brick absent) — a
  scout/self-recon task, not a truth-value one. (b) If desired, pin the finite-glue-measurability lemma
  shape (continuous-on-each-of-finitely-many-Borel-cells ⟹ measurable) — elementary, but the assembly
  step. Neither reopens the truth-value: F2 is labour with the contour-free algebraic recipe.
