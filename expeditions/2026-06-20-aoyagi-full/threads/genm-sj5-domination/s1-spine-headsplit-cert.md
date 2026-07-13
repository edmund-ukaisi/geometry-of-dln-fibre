# S1 spine→core head-split cert — the x-chart pivot-energy reorganization (Part A, DOMINATION-with-constant) + the corrected `deeperFlag_spineToCore` statement + satisfiability verdict (Part B: **labour + corrected statement**)

**Seat:** pen-and-paper (design-space math, one truth-value, decorrelated), aoyagi-full Stage 2,
`genm-sj5-domination`, T-Obl3b OWED-3 de-risk. **Date:** 2026-07-13. **NO Lean edits, NO git, NO build.**
Exact algebra (Ky-Fan/Weyl singular-value inequalities, Loewner/PSD monotonicity, Schur/shear identities,
radial-blow-up bookkeeping) + numeric MC guide only (`scripts` inline below). Decorrelated
`local-codex-consult` (xhigh, my conclusion WITHHELD — "adjudicate either direction"):
`codex/s1-headsplit-{prompt,answer}.md`. Numeric guide (guide only, not a proof): `/tmp/sj_guide.py`
(σ-submultiplicativity 0/20000, shell⊆G containment 0/114058), `/tmp/minadm.py` (charge budgets).

**Anchors.** Two are used deliberately:
- **`(3,3,3)@t★=1, j=1` (the brief's anchor, `L=0`).** `u = t★+j = 2`; `a = M₀−u = 1`, `b = M₁−u = 1`,
  `ab = peelCharge M u = 1`; `M₂ = 3`, `n = M_last = 3`; `M' = redChain 2 (3,3,3) = (2,3)`,
  `minAdm(2,3)=6`; binding cut `minAdm(3,3,3)=7 = ab + 6`. **At `L=0` the deep tail is empty:**
  `Z_deep = prod(dropHead(tailChain M))(A'∘succ) = I₃` (a single-width chain has product `1`), so
  Part B's rank/PSD tension is **VACUOUS** here (`Zf ≡ I₃`, rank 3, floor trivial). Used for Part A.
- **`(3,3,3,3)@t★=1, j=1` (`L=1`, the tension-exhibiting companion).** Same `u=2, a=b=1, ab=1`; now
  `tailChain M = (3,3,3)`, `A' = (A'₀, A'₁)` two deep layers, `Z_deep = prod((3,3))(A'₁) = A'₁` (3×3),
  which **is `0` at `z=0`** — the genuine tension. `M' = redChain 2 M = (2,3,3)`, `minAdm(2,3,3)=5`;
  binding cut `minAdm(3,3,3,3)=6 = 1 + 5` (UNIQUE binding, `/tmp/minadm.py`). Used for Part B.

**Consumed / read (signatures, not re-derived).** `RouteMSJDeeperFlagCore` — `deeperFlag_spineToCore`
(S1, the sorry), `shellSpineIntegrand`, `deeperFlagCoreIntegrand`, `deeperFlag_shell_core_le` (L1),
`shell_corankOffSector_le_unif`/`shellCorankWeight_le_unif`/`strongBlock_lintegral_le_unif`
(S3, **the constant `deeperFlagUnifConst = Cresid·(ε^{−ab}·C_strong_unif)` is `Z`/`Ccross`/`w`-uniform**);
`RouteMSJChartShear` (`freedSchurLoss x Γ Q = frobSq(P·Q') + frobSq(C·Q'+Γ·Q_b)`, `Q'=Q_p+P⁻¹B₁₂Q_b`,
`outerDom`, `schurShift`, `chartInner_schurShearFree_eq`); `RouteMSJHeadSplit` (`prod_headSplit`,
`paramsHeadSplit`, `minAdm_le_mul_head`); `RouteMSJBlockReindex` (`blockSplitEquiv`,
`chartInner_blockReindex_eq_of_emb`); `RouteMSJCornerComparator` (`cornerComparator`,
`cornerComparator_decLoss = commonDivisor(u)²·frobSq(prod M' z)`, `cornerComparator_adm`,
`exists_cornerComparator_adm` → clean `d=1, k=[1], jc=[minAdm M'−1]`); `RouteMLayerSplit`/`RouteMSJResolution`
(`redChain`, `tailChain = redChain (M 1) M`, `minAdm`, `peelCharge`, `sjChargeBudget_binding`);
`RouteMSJShellCover` (`singularShell ε r j = {min(weakEigCount ε Z) r = j}`, `weakEigCount` = # eigen of
`Z Zᵀ` below `ε²`, `singularShell_iUnion`). Prior certs corrected/extended here:
`tobl3b-cornershift-chart-cert.md`, `tobl3b-deepercut-admissibility-cert.md`.

**The clean part (formaliser-established, taken as given).** Row-split `A' ↔ (z, A_cor)` via
`blockSplitEquiv κ` on the `M₁` rows of `A'₀`: `z 0` = the `u` pivot rows (`u×M₂`), `A_cor` = the
`b=M₁−u` complement rows (`b×M₂`), `z∘succ = A'∘succ`; then (head-split `prod_headSplit`)
`Z := prod(tailChain M) A' = (A'₀)·Z_deep`, so `Q_p = z0·Z_deep = prod(redChain u M) z = Q̃_p` (pivot
rows of `Z`), `Q_b = A_cor·Z_deep = Q̃_b` (corank rows of `Z`), `Z_deep = prod(dropHead(tailChain M))(A'∘succ)`
(`M₂×n`, depends ONLY on `z∘succ`).

---

## ★ HEADLINE VERDICTS

- **PART A — RESOLVED, as a DOMINATION carrying a bounded constant `C_hle < ⊤`** (NOT a clean `≤`, NOT
  an equality, NOT pointwise-termwise). The pivot energy `frobSq(P·Q')` reorganizes to
  `commonDivisor(v)²·frobSq(Q̃_p)` via a P-radial blow-up (`v`-coords + Jacobian monomial `∏|v_ℓ|^{jc_ℓ}`
  + det-1 unit clear); `B₁₂` is absorbed exactly into the Γ-shear (`Γ' = Γ + C·P⁻¹B₁₂`); `C` and the
  P-angular/`B₁₂`-box directions integrate to a **finite constant** (they have no image in the RHS
  coordinates — a coordinate-count fact, §A.4). This constant is a **real correction to the current
  constant-free `hle`** (see Part B, correction (3)).

- **PART B — SATISFIABLE with a CORRECTED statement (labour, NOT reroute), WITHIN the convergence scope
  `min(M₁,n)−j ≥ a+b` (all `M₂≤M₁`; both anchors, tight).** The current `∀z` rank/PSD hyps on `Zf z` are
  FALSE if `Zf z = Z_deep` (rank 0 at `z=0`, `L≥1`), and cannot be fixed by a z-uniform full-rank `Zf`
  (breaks `A_cor·Zf z = Q̃_b`). The correct fix is threefold — (1) rescale the PSD floor to
  `ε' = ε/√(M₁·M₂)`; (2) take `m = min(M₁,n) − j` (the SHELL-guaranteed strong rank; `min(M₂,n)` at `L=0`)
  with the range condition `b ≤ m ≤ min(M₂,n)` (else shell EMPTY — Codex flag) AND the convergence
  condition `m ≥ a+b`; (3) `hle` carries a bounded constant — plus a **piecewise `Zf`** (`= Z_deep` on the
  good set `G`, a fixed full-rank `V` off `G`) that makes the `∀z` hyps literally TRUE while `hle` still
  holds because the shell mass sits inside `G`. **L1 (`deeperFlag_shell_core_le`) is UNCHANGED** (used
  verbatim, instantiated at `ε'`). Genuinely-new residuals: a measurable `m`-frame selection `z ↦ U_sf z`
  (Borel functional calculus — labour). **Genuine scope BOUNDARY (B.2b):** for `L≥1 ∧ M₂>M₁` wide chains
  the shell-forced `m < a+b`, `hconv` fails, and the corank weight genuinely diverges — those shells need a
  finer `Z_deep`-stratification (corrects the cornershift cert's over-assumed `m=M₂−j`). Decorrelated Codex
  concurs (all FACT; verdict LABOUR).

---

## PART A — the x-chart / pivot-energy reorganization (the ~65–75%-new content)

### A.0 What must be shown

`shellSpineIntegrand` (LHS) integrates `∫_{A'∈tailbox∩shell} ∫_{x=(P,B₁₂,C)∈outerDom} ∫_Γ
(freedSchurLoss x Γ Q)^{−c'}` with `Q = (prod(tailChain M) A').submatrix (blockSplitEquiv κ) id`.
`deeperFlagCoreIntegrand` (RHS) integrates `∫_{z∈redbox} ∫_{v∈unitBox d} (∏|v_ℓ|^{jc_ℓ}) · ∫_{A_cor∈matBox b M₂ 1}
∫_{Γ'∈sΓf z} (decLoss v z + frobSq(Ccrossf z + Γ'·(A_cor·Zf z)))^{−c'}`, with
`decLoss v z = commonDivisor(v)²·frobSq(prod(redChain u M) z) = commonDivisor(v)²·frobSq(Q̃_p)`
(`cornerComparator_decLoss`).

**Variable ledger (anchor `(3,3,3)`).** The FRONT layer `W₁` (`M₀×M₁ = 3×3 = 9` real params) is the
reindexed block matrix `B = fromBlocks P B₁₂ C D`: `P` (`u×u = 2×2`), `B₁₂` (`u×b = 2×1`), `C` (`a×u = 1×2`),
`D` → the freed corner `Γ` (`a×b = 1×1`). The deep layers `A'` (= `W₂,…`) split into `z`-layers + `A_cor`.
So the CoV is `{A'} ↔ {z-layers, A_cor}` (row-split, measure-preserving) and `{W₁} = {x, Γ} ↔ {v, Γ',
absorbed}`.

### A.1 The pivot energy is the pivot-row energy of `B·Q` (exact identity, banked shape)

`freedSchurLoss x Γ Q = frobSq(B·Q)` split into pivot rows + corank rows, because
`P·Q' = P·Q_p + B₁₂·Q_b` (the `P·P⁻¹` cancels on the `B₁₂` term) and `C·Q' + Γ·Q_b = C·Q_p + D·Q_b`
(the shift `Γ = D − C·P⁻¹B₁₂` cancels). So:

    pivot energy  = frobSq(P·Q_p + B₁₂·Q_b)                 [ = frobSq of the u pivot rows of B·Q ]
    corank energy = frobSq(C·Q_p + Γ'·Q_b),  Γ' := Γ + C·P⁻¹B₁₂  [ = D·Q_b restated ]

The rename `Γ' = Γ + C·P⁻¹B₁₂` is an exact measure-preserving translation at fixed `(P,B₁₂,C)`
(`measurePreserving_add_right`, already used in `chartInner_schurShearFree_eq`). This is step (ii)'s
**absorption-by-renaming of `B₁₂` into `Γ'`**: after it, the corank energy is `frobSq(C·Q̃_p + Γ'·Q̃_b)`,
with `Ccross := C·Q̃_p` and `Q̃_b = A_cor·Z_deep`. `shell_corankOffSector_le_unif`'s bound is UNIFORM in
`Ccross` (its constant is `Ccross`-free), so `C` may be treated as a fixed matrix per its box-slice.

### A.2 The P-radial blow-up (step (i)) — the anchor Jacobian + monomial, explicit

The pivot energy `frobSq(P·Q_p + B₁₂·Q_b)` with `P` invertible on `outerDom`. Radially blow up `P` at the
exceptional `v`-coordinates of the reduced comparator. Write `P = commonDivisor(v)·P̂(ang)` where
`commonDivisor(v) = ∏_ℓ |v_ℓ|^{k_ℓ}` is the **scale** and `P̂` a de-scaled direction with `|det P̂| = 1`
(the **det-1 unit clear**). Then

    frobSq(P·Q_p + B₁₂·Q_b) = commonDivisor(v)² · frobSq(P̂·Q_p + commonDivisor(v)⁻¹·B₁₂·Q_b),

and the Jacobian of `dP ↦ (dv, d·ang)` contributes the monomial `∏_ℓ |v_ℓ|^{jc_ℓ}` (the accumulated
resolution Jacobian `jc`). **Anchor `(3,3,3)` numbers.** Comparator clean data (`exists_cornerComparator_adm`):
`d = 1`, `k = [1]`, `jc = [minAdm(M')−1] = [6−1] = [5]`. So

    commonDivisor(v) = |v₀|^{k₀} = |v₀|,     Jacobian monomial = ∏|v_ℓ|^{jc_ℓ} = |v₀|^5,
    monomialThreshold 1 [1] [5] = axisRatio 5 1 = (5+1)/(2·1) = 3 = ½·minAdm(2,3)   (BINDING).

(Companion `(3,3,3,3)`: `M'=(2,3,3)`, `minAdm=5`, clean `d=1,k=[1],jc=[4]`,
`monomialThreshold = (4+1)/2 = 2.5 = ½·5`.) The `½·peelCharge = ½·ab` charge is SEPARATE: it is the
`a×b` freed-corner `Γ'`-Gaussian (`corankBlock_morsePeel` inside `shell_corankOffSector_le_unif`),
producing `w^{−(c'−ab/2)}`, `w = decLoss`. So the exponent shift `c' ↦ c' − ½·peelCharge` is the corner
Gaussian, and the `v`-monomial threshold `½·minAdm(M')` is the reduced chain's charge (IH's job).

### A.3 It is a DOMINATION (≤), not equality; and NOT pointwise-termwise

Two `≤`'s enter, neither pointwise-termwise:
- **De-scaled direction (near-singular `P`).** After the det-1 clear, `frobSq(P̂·Q_p + s⁻¹B₁₂Q_b)`
  (`s = commonDivisor(v)`) still carries the `B₁₂`-cross term (now amplified by `s⁻¹`, singular as `s→0`).
  The reduction to `commonDivisor(v)²·frobSq(Q̃_p)` DROPS this cross-coupling. This is a domination that is
  valid only after the P-angular and `B₁₂` integrations (the cross term averages/bounds), NOT a pointwise
  `frobSq(P̂·Q_p + …) ≥ frobSq(Q̃_p)` (which is false near singular `P`). Hence "not a pointwise termwise
  bound (near-singular `P`)", exactly as the brief anticipated.
- **PSD weak-direction elimination** on the corank side (Part B) — a Loewner `≤`, not `=`.

### A.4 Where `C`, `B₁₂`, and the P-angular directions go — the CONSTANT (correction to `hle`)

**Coordinate count.** `W₁` has `M₀·M₁ = 9` params (anchor). The RHS-specific new coordinates from `W₁`
are `v` (`d = 1`) and `Γ'` (`ab = 1`) — total `2`. The remaining `M₀M₁ − d − ab = 7` params (P-angular
`u²−1 = 3`, `B₁₂` `ub = 2`, `C` `au = 2`) have **NO image in the RHS variables** (`z, v, A_cor, Γ'`), so
they must be integrated out on the LHS. Over the `[−1,1]` boxes with a bounded integrand (the de-scaled
`P̂` has `σ_min(P̂) ≥ σ_max(P̂)^{−(u−1)}` bounded below on the box since `|det P̂|=1`; the `Ccross`-uniform
corank bound is finite), this yields a **finite multiplicative constant `C_hle < ⊤`** — NOT `≤ 1`
(box volume `2^7`). Therefore

    corrected hle:   shellSpineIntegrand …  ≤  C_hle · deeperFlagCoreIntegrand …    (∃ C_hle < ⊤),

which the prior `tobl3b-cornershift-chart-cert.md` §1 Step 4 independently exhibits as
`const(ε) = Cresid·ε^{−(a−j)(b−j)}·C_box·[∫det-Gram]`. **The current constant-free clause
`shellSpineIntegrand ≤ deeperFlagCoreIntegrand` is therefore under-stated (a probable wrong statement);
it must carry `C_hle`.** The headline `deeperFlag_shell_le` composes it fine: `shellSpine ≤ C_hle·core ≤
C_hle·C_L1·comparator.integral`, so the headline's `∃C` becomes `C = C_hle·C_L1` (a one-line
`mul_le_mul`/`mul_assoc` change to the existing `hle.trans hcore`).

---

## PART B — the S1 statement satisfiability (the flagged tension)

### B.1 The tension is REAL (only) for `L ≥ 1`; the companion `(3,3,3,3)`

`Zf z = Z_deep = prod(dropHead(tailChain M))(A'∘succ)` depends only on `z∘succ`. At `z = 0` (all deep
layers zero) `Z_deep = 0`, rank `0 < m`, so the current UNCONDITIONAL `∀z, m ≤ (Zf z).rank` and
`∀z, (Zf z (Zf z)ᵀ − ε²•U_sf U_sfᵀ).PosSemidef` are **FALSE**. A z-uniform full-rank `Zf` would satisfy
them but then `A_cor·Zf z ≠ Q̃_b`, breaking the domination. At the brief's `(3,3,3)` `L=0` anchor
`Z_deep = I₃` is CONSTANT, so the tension is vacuous there; the companion `(3,3,3,3)` (`Z_deep = A'₁`,
`0` at `z=0`) exhibits it.

### B.2 The crux (controller refinement #2): which quantity carries rank/PSD, and is it provable

**The shell on the FULL product `Z = A'₀·Z_deep` does NOT floor `Z_deep` pointwise-∀z — but it CONTAINS
the good set, which suffices.** Exact facts:

- **(Ky-Fan/Weyl, FACT)** `σ_i(A'₀·Z_deep) ≤ σ_1(A'₀)·σ_i(Z_deep)` for all `i` (rectangular OK). On the
  box `σ_1(A'₀) ≤ ‖A'₀‖_F ≤ √(M₁·M₂)`. Guide: `/tmp/sj_guide.py`, 0/20000 violations.
- **(containment, FACT)** Set `ε' := ε/√(M₁·M₂)`, `m := min(M₁,n) − j`, `G := {z : σ_m(Z_deep(z)) ≥ ε'}`.
  Then **`Z ∈ singularShell ε r ⟨j⟩ ⟹ z∘succ ∈ G`**: on `S_j` (`j<r`), `σ_m(Z) ≥ ε`; if `z∉G` then
  `σ_m(Z) ≤ σ_1(A'₀)·σ_m(Z_deep) < √(M₁M₂)·ε' = ε`, contradiction. So `{A' : Z∈S_j} ⊆ {A' : z∘succ∈G}`.
  Guide: `/tmp/sj_guide.py` `(3,3,3,3)`, ε=0.5, **0 violations / 114058 shell hits**. This is the answer
  to refinement #2: **rank/PSD is carried by `Z_deep = Zf z` (NOT the full product), and the shell FORCES
  it (with the rescaled `ε'`) because the shell domain is contained in `G`.** The full-product quantity is
  only the trigger; `Z_deep` carries the floor.
- **(range condition, Codex flag — FACT)** For `G` to be nonempty on the shell need `m ≤ min(M₂,n)` (else
  `Z_deep` cannot have `m` singular values `≥ε'`, so `S_j` is EMPTY — vacuous). Anchor `(3,3,3,3)`:
  `m = min(3,3)−1 = 2 ≤ min(3,3) = 3` ✓.

### B.2b The USABLE floor rank `m` and the CONVERGENCE SCOPE (a genuine finding beyond the anchor)

L1's `hconv : a < m − b + 1` (`⟺ m ≥ a+b`, integers) demands the floor rank `m` be LARGE; the shell only
GUARANTEES `m` up to the shell-forced strong count. Two regimes (`/tmp/sweep{2,3}.py`, exhaustive over
`M∈[2..5]^{3,4,5}`, all binding cuts, `a,b≥1`):
- **`L = 0`** (`Z_deep = I`, full rank): `m = min(M₂,n)` (identity is full rank, ALL σ = 1 ≥ ε'=1).
  Convergence `a < min(M₂,n)−b+1` — **0/45 failures**. The shell is not even needed here.
- **`L ≥ 1`** (genuine variable `Z_deep`): the SHELL-GUARANTEED strong rank is `m = min(M₁,n) − j` (because
  `Z_full = A'₀·Z_deep` has `≤ M₁` rows, so the shell can certify at most `min(M₁,n)−j` strong directions
  of `Z_deep`). Convergence `⟺ min(M₁,n)−j ≥ a+b`. **Empirical scope (64 binding shells): 0 failures when
  `M₂ ≤ M₁` (57/57 converge — 20 narrow + 37 wide-but-OK); 7 failures, ALL with `M₂ > M₁`** (the wide
  family `M = (4,3,·)` at `u=2`: `a=2, b=1, m = min(3,n)−1 = 2 < a+b = 3`).

**The genuine finding.** For `L≥1 ∧ M₂>M₁` chains where `min(M₁,n)−j < a+b`, the shell-forced floor rank is
insufficient and the corank weight `∫_{A_cor∈box(b×M₂)} det((A_cor Z_deep)(A_cor Z_deep)ᵀ)^{−a/2}`
**genuinely DIVERGES on the `rank(Z_deep)=m` sub-locus** (the integral converges iff `rank(Z_deep) > a+b−1`,
and the shell admits `Z_deep` of rank exactly `min(M₁,n)−j` inside `S_j`). This is NOT a bound artifact —
it is a real divergence, so L1's `hconv` FAILS and the single-`ε` shell on `Z_full` is not fine enough
there; a finer stratification (of `Z_deep` directly) or the bottleneck/saturated branch is required.

**Correction to `tobl3b-cornershift-cert`.** That cert used `m = M₂−j` (giving convergence `a < M₂−b−j+1`).
That is **not shell-justified for `L≥1 ∧ M₂>M₁`**: the shell on `Z_full` (an `M₁`-row matrix) can force only
`min(M₁,n)−j < M₂−j` strong directions on `Z_deep`. They coincide only when `M₂ ≤ M₁` (or `L=0`, `Z_deep=I`),
e.g. the anchor `M₂=M₁=n=3`. So `m = min(M₁,n)−j`, and the mechanism's convergence scope is
`min(M₁,n)−j ≥ a+b` — **satisfied at BOTH anchors (tight: `m=2=a+b`), and for ALL `M₂≤M₁` chains.**

### B.3 The correct `Zf` (piecewise) — keeps L1's `∀z` hyps literally TRUE (controller refinement #1)

**Route taken: NEITHER (a) restate L1 NOR (b) restrict the RHS `∫_z` domain.** Instead define

    U_sf z := (measurable m-frame of the ≥ε'²-eigenspace of Z_deep(z) Z_deep(z)ᵀ)   on G,   fixed U_s0 off G
    Zf z   := Z_deep(z)                                                              on G,   fixed V off G

with `V` (`M₂×n`) of rank `≥ m` and `V Vᵀ ⪰ ε'²·U_s0 U_s0ᵀ` (e.g. `V = [I_m | 0]ᵀ`-shaped isometry).
Then **for ALL `z`**: `m ≤ (Zf z).rank` (on G by def of G; off G by construction of V) and
`Zf z (Zf z)ᵀ ⪰ ε'²·(U_sf z)(U_sf z)ᵀ`. So `hmZ`, `hshell`, `hUs` hold literally `∀z` at `ε'` — **L1 is
consumed verbatim, RHS z-domain is the full box.** The `hle` domination still holds because (B.2
containment) the shell mass on the LHS sits inside `{z∘succ∈G}`, where `Zf z = Z_deep` and the honest
PSD-elimination bound (`shell_corankOffSector_le_unif` at `ε'`) applies; off-`G` and off-shell mass is
nonneg slack ADDED to the RHS (integrand `≥0`), preserving `≤`. `decLoss` uses the honest
`prod(redChain u M) z = Q̃_p` (independent of `Zf`), so `hpos` (a.e. `decLoss>0`) is unaffected.

**Refinement #1 answer (compose consistency).** L1's `deeperFlag_shell_core_le` is instantiated by the
headline `deeperFlag_shell_le` with `ε := ε'` (not the shell `ε`); L1 is ε-polymorphic and `0<ε ⟹ 0<ε'`,
so L1 typechecks and closes unchanged — its constant becomes `deeperFlagUnifConst … ε' …` (still finite).
No landed clean-three theorem is edited.

### B.4 The corrected `deeperFlag_spineToCore` signature (precise)

Changes vs the current statement (marked ⚑):

    theorem deeperFlag_spineToCore {L : ℕ} (M : Fin (L+1+1+1) → ℕ) (t j : ℕ)
        (κ : Fin (t+j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
        (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
        (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i) :
      ∃ (M₂ m n d : ℕ) (ε' : ℝ) (k jc : Fin d → ℕ)          -- ⚑ add ε' (the rescaled floor)
        (C_hle : ℝ≥0∞)                                       -- ⚑ add the bounded reorganization constant
        (Zf : Params (redChain (t+j) M) → Matrix (Fin M₂) (Fin n) ℝ)
        (Ccrossf : …) (U_sf : …) (sΓf : …) (_i₀ : …),
        0 < ε'                                               -- ⚑
        ∧ C_hle < ⊤                                          -- ⚑
        ∧ (∀ z, (U_sf z)ᵀ * U_sf z = 1) ∧ (M 1 - (t+j) ≤ m) ∧ (m ≤ M₂) ∧ (∀ z, m ≤ (Zf z).rank)
        ∧ (∀ z, (Zf z * (Zf z)ᵀ - (ε'^2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)   -- ⚑ ε' not ε
        ∧ (((M 0 - (t+j):ℕ):ℝ) < (m:ℝ) - ((M 1 - (t+j):ℕ):ℝ) + 1)
        ∧ (∀ᵐ z …, ∀ᵐ v …, 0 < (cornerComparator (redChain (t+j) M) k jc).decLoss v z)
        ∧ (1 ≤ d)
        ∧ ((minAdm (redChain (t+j) M) : ℝ≥0∞)/2 ≤ monomialThreshold d k jc)
        ∧ shellSpineIntegrand M (t+j) κ ε (min (M 0-t) (M 1-t)) ⟨j,_⟩ c'
            ≤ C_hle * deeperFlagCoreIntegrand M (t+j) k jc Zf Ccrossf sΓf c'   -- ⚑ C_hle·(RHS)

with the intended witnesses `ε' = ε/√(M₁·M₂)`, `m = min(M₁,n) − j` (`L≥1`) or `min(M₂,n)` (`L=0`),
`n = M_last`, `M₂ = M 2`, clean `d=1, k=[1], jc=[minAdm(redChain(t+j)M) − 1]`, `Zf` piecewise (B.3).
**Load-bearing side-conditions the corrected `hconv` clause encodes (do NOT drop):** `b ≤ m ≤ min(M₂,n)`
(range/nonvacuity — else `S_j` empty) AND `m ≥ a+b` (convergence, `⟺ a < m−b+1`). Per B.2b the latter holds
for ALL `M₂ ≤ M₁` and at both anchors (tight, `m=2=a+b`), but FAILS for the `L≥1 ∧ M₂>M₁` wide family —
there the clause is genuinely unsatisfiable and the shell term needs a finer/separate treatment. The
headline `deeperFlag_shell_le` reads `obtain … ε' C_hle …`, passes `hε' : 0 < ε'` (from `hε`) to
`deeperFlag_shell_core_le`, and closes with `(mul_le_mul_left' hcore C_hle).trans` folding `C := C_hle · C_L1`.

**VERDICT (Part B): satisfiable-with-corrected-statement (LABOUR) — within the convergence scope
`m = min(M₁,n)−j ≥ a+b` (all `M₂≤M₁`; both anchors, tight).** Not a reroute. The obstruction the brief
flagged (unconditional `∀z` rank/PSD on `Zf = Z_deep`) is real but is dissolved by the rescaled floor `ε'`,
the shell⊆G containment, and the piecewise `Zf` — all TRUE and provable. The single admissible data choice
is (B.3)+(B.4). The residual `L≥1 ∧ M₂>M₁` scope gap (B.2b) is a genuine BOUNDARY to surface: the mechanism
does not cover it, so the ∀M statement must carry the scope hypothesis or route those shells through a finer
`Z_deep`-stratification / the saturated branch.

---

## Build-path for the formaliser

**Banked, consume directly:** `deeperFlag_shell_core_le` (L1, verbatim, instantiate `ε := ε'`);
`shell_corankOffSector_le_unif` / `shellCorankWeight_le_unif` / `strongBlock_lintegral_le_unif` (S3, the
`Z`/`Ccross`/`w`-uniform corank weight — this is exactly the PSD-elimination brick, `U_s`-uniform);
`chartInner_schurShearFree_eq` (the `B₁₂`→`Γ'` shear, exact MP); `chartInner_blockReindex_eq_of_emb` +
`blockSplitEquiv` (front-factor block-reindex); `prod_headSplit` / `paramsHeadSplit(_mp,_preimage_box)`
(the row/head split, MP); `cornerComparator_decLoss` / `cornerComparator_adm` (the reduced comparator +
its clean `d=1,k=[1],jc=[minAdm−1]`); `singularShell(_iUnion)` + `lintegral_le_sum_finCover` (shell cover,
measurability-free); `det_le_det_of_posSemidef_sub` (Loewner det-monotone, inside S3);
`sjChargeBudget_binding` / `flagShift_lt_carrierThreshold` (the binding cut + threshold).

**Genuinely-new (the S1 labour, in dependency order):**
1. **P-radial blow-up CoV** on `outerDom`'s `P`-block: `∫_P f(P) = ∫_{v,ang} f(commonDivisor(v)·P̂)·|Jac|`
   with `|Jac|` the `∏|v_ℓ|^{jc_ℓ}` monomial × bounded angular factor + `|det P̂|=1` clear. The single
   real analytic piece; Aoyagi §5's method. (This is where the constant `C_hle` and the `v`-monomial are born.)
2. **Ky-Fan/Weyl `σ_i(A B) ≤ σ_1(A)·σ_i(B)`** (rectangular) → the containment `Z∈S_j ⟹ σ_m(Z_deep) ≥ ε'`.
   Small linear-algebra lemma; Mathlib has singular values via `Matrix.…`/eigenvalues of `ZZᵀ`.
3. **Measurable `m`-frame selector** `z ↦ U_sf z` from the `≥ε'²` spectral subspace of `Z_deep(z)Z_deep(z)ᵀ`
   on `G` (Borel functional calculus: `B ↦ 𝟙_{[ε'²,∞)}(B)` Borel; then a measurable frame). The residual
   noted by the admissibility cert; labour, not a wall.
4. **Piecewise `Zf` / `U_sf`** assembly + `hle` domination = `[1]·[shear]·[blockReindex]·[headsplit]` CoV
   then `[containment ⊆ G]` domain-monotone `≤` then S3's `shell_corankOffSector_le_unif` at `ε'`
   pointwise-in-`(z,v)`. Then integrate; `C_hle` from the bounded absorbed directions.

**Do NOT:** re-open the dead plain-IH hole `innerCorankDescent_lt_top` (build in the `DecoratedStepHyp adm`
framing, decorated IH via `cornerComparator_adm`); do NOT keep the constant-free `hle` (it is under-stated);
do NOT use the shell `ε` in the PSD floor (use `ε' = ε/√(M₁M₂)`); do NOT set `Zf = Z_deep` with `∀z` hyps
(rank 0 at `z=0`) — use the piecewise `Zf`.

---

## Decorrelated Codex (my conclusion WITHHELD; prompt framed "either direction")

`codex/s1-headsplit-{prompt,answer}.md` (xhigh). Codex CONCURS, decorrelated, all-FACT:
- **Q1 [FACT]** Ky-Fan/Weyl `σ_i(A₀Z_deep) ≤ σ_1(A₀)σ_i(Z_deep)`, rectangular OK.
- **Q2 [FACT]** floor `Z_deep Z_deepᵀ ⪰ (ε²/(M₁M₂))·U_sU_sᵀ` pointwise, **with range condition
  `m = min(M₁,N)−j ≤ min(M₂,N)`** (else `S_j` empty).
- **Q3 [FACT]** the containment `{Z_full∈S_j} ⊆ G` is TRUE; no counterexample once `m ≤ min(M₂,N)`.
- **Q4 [FACT]** `∫_{S_j} F ≤ ∫_G F` (indicator monotonicity/Tonelli); the row-split is a MP coordinate
  projection — no disintegration.
- **Q5 [FACT]** the piecewise `Zf` preserves the bound and enforces `(R),(P)` everywhere; the needed
  measurability is Borel functional calculus (`B ↦ 𝟙_{[δ²,∞)}(B)` Borel).
- **Q6 VERDICT: LABOUR.** Most likely failure point: **neglecting the range condition `m ≤ min(M₂,N)`**
  (would make the shell void). — Folded into B.2/B.4 (the nonvacuity side-condition).

The concurrence is decorrelated (my rescaled-`ε'` / containment / piecewise-`Zf` conclusion was NOT in the
prompt). Codex independently surfaced the range condition, which I have promoted to a load-bearing
side-condition.

---

## Close

- **Firmest result.** Part A resolves: the x-chart reorganization is a **DOMINATION carrying a bounded
  constant `C_hle`** (P-radial blow-up + det-1 clear producing `commonDivisor(v)²·frobSq(Q̃_p)` with the
  anchor monomial `|v₀|^5`, `commonDivisor=|v₀|`, threshold `3 = ½·minAdm(2,3)` binding; exact `B₁₂→Γ'`
  shear; `C`/angular absorbed to a finite constant), NOT clean-≤, NOT pointwise-termwise. Part B verdict:
  **satisfiable with the corrected statement (labour)** — floor rescaled to `ε' = ε/√(M₁M₂)`,
  `m = min(M₁,n)−j` with range `m ≤ min(M₂,n)`, piecewise `Zf`, and `hle` carrying `C_hle`; L1 consumed
  verbatim at `ε'`. Exact + decorrelated-Codex-corroborated.
- **Most likely to break it.** (i) **The `L≥1 ∧ M₂>M₁` convergence scope gap (B.2b) — the sharpest limit
  on the ∀M statement.** For wide chains (`M = (4,3,·)` at `u=2`) the shell-forced floor rank
  `m = min(M₁,n)−j < a+b`, so `hconv` fails and the corank weight genuinely diverges on the `rank(Z_deep)=m`
  sub-locus; the single-`ε` shell on `Z_full` is not fine enough there (0 failures for `M₂≤M₁`, 7/64 for
  `M₂>M₁`). This also CORRECTS the cornershift cert's over-assumed `m=M₂−j`. The anchor (`M₂=M₁`) is safely
  inside scope, so it does not expose this — the reviewer must decide whether the mountain carries the
  `M₂≤M₁` (or `min(M₁,n)−j≥a+b`) scope hypothesis or a finer `Z_deep`-stratification covers the rest.
  (ii) The P-radial blow-up's angular integrability if `σ_min(P̂)→0` on the det-1 sphere is not controlled
  — the genuine analytic piece (build-path #1); if it diverges, `C_hle` may not be finite. (iii) The
  measurable `U_sf` selector (#3) if the spectral subspace lacks a clean gap — resolved by selecting an
  `m`-frame of the `≥ε'²` subspace, not the exact top-`m`.
- **Next.** (a) Pen-and-paper pin of build-path #1 (the P-radial blow-up angular integrability / exact
  `|Jac| = ∏|v|^{jc}` bookkeeping and finiteness of the angular `C_hle` factor) — the load-bearing analytic
  gap. (b) Confirm the nonvacuity side-conditions hold at every binding cut `u = t★+j` (a `decide`-style
  sweep over the relevant `(M₀,M₁,M₂,n,t,j)` — extend `/tmp/minadm.py`). Recommend (a) before the S1
  formalisation tide, since it is the only place "labour" could still hide a wall.
