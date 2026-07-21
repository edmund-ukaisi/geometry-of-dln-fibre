import DLNFibre.Core.Aoyagi.BlockBlowup
import Meta.Cordon

/-!
# `Core.Aoyagi.PrincipalInv` — the path invariant + the algebraic recursion leaves

**BLUEPRINT (aoyagi-engine rung C; RESHAPED per the pnp-case1 + rev-leaves + elder δ-adjudication).**
The network-free algebraic spine of the coupled product-ideal resolution monument (charter §1.B),
universalized over a general ambient dimension `Fin D` and generator family `F` (the DLN driver
instantiates `D := flatDim d`, `F := coreGen d e`).

## Two invariants: interior `StepInv` (divisibility only) vs terminal `PrincipalInv` (both)

The pnp-case1 verdict established that a per-step invariant CANNOT bundle divisibility AND Bézout:

* **Divisibility (D)** — `⟨(∏C)∘g⟩ ⊆ ⟨b₁⟩`, each entry `= b₁·q` — IS per-step preservable (`StepInv`).
* **Bézout / principality (B)** — is **FALSE at the root and every interior state** (the pending tail
  vanishes at `0`, forcing every quotient `q(0) = 0`); it is BORN at the TERMINAL node by the cleared
  pivot (`terminal_bezout`). In-tree corroboration: thread-28 line 73; worked.tex:659.

`StepInv` carries the **deepest-point vanishing** `(Fᵢ∘g) 0 = 0` (elder S3, kernel-checked): the real
states always have it (`coreGen i 0 = 0`, the R0/R1 deepest-point reduction), it is preserved by every
step (`σ 0 = 0`), and δ=1 children genuinely NEED it (the child `b'` vanishes at `0`, so the child
entry must too). Its positive face is the SAME fact whose negative face defeats interior Bézout.

## Step-map shape (elder S1) — BLOCK-CENTER blow-ups with spectators, NOT full-ambient

Each step is `σ = sh ∘ blockBlowupMap S p`: a unipotent shear `sh` (Jacobian-exactly-1) after the
**block-center** blow-up (`Core.Aoyagi.BlockBlowup`) — center `S`, pivot `p ∈ S`, spectators FIXED.
The full-ambient `blowupMap` (`S = univ`) is WRONG for interior steps (W2: the Jacobian exponent is
`|S|−1` = center-size accumulation, NEVER ambient−1; a shear cannot undo spectator multiplication).

## The δ discriminator (elder S2/A) — a STATE property `[J=0]`, edge-spec-supplied

The child dominant obeys `b' = u_p^δ · (b∘σ)` with `δ = [J=0] ∈ {0,1}` a STATE property (thread-34
cert line 16), UNIFORM across the 1(1)/1(2) sub-cases (and case-2) — NEVER branch-coded (that shape is
false at every interior 1(2)-`J≥1` state). The preservation Props take a small **per-edge `EdgeSpec`**
(the fold reads `δ` off the salvaged `ConState.cleared`, and the center `S` off the same edge); this
also blocks the LAZY-WITNESS hole (`|S|=1` / `sh=id` children satisfying a bare `∃`-child shape and
silently relocating the monument into L5 — a charter bar-(iii) regression).

## Branch distinction (elder S2/B) — ONE center, TWO distinct pivots

The Case-1 center `{d-block ∪ u_{s,k}}` is blown up at TWO distinct pivots: 1(1) merge pivots at the
existing exceptional `u_{s,k} ∈ S` (a genuine substitution, `|S|−1` = the printed 1(1) increment);
1(2) split pivots at a `d`-entry (the old `u` transforms as a non-pivot member). `p_merge ≠ p_split`
forces the two children distinct — one witness package cannot discharge both (the collapse rev-leaves
flagged). Pivot-kind (existing-exceptional vs fresh) is the branch semantic; no ledger machinery.

W1 (no T-comparability transcription anywhere). Rollover is only-at-exhaustion (R4; under the M'=1
compression the `b`-truncation is invisible — only the residual re-binds).
-/

open MeasureTheory Set Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

variable {M D : ℕ}

/-! ## The two invariants -/

/-- **The interior step invariant** — DIVISIBILITY ONLY + DEEPEST-POINT VANISHING (pnp-case1 + elder
S3). On the region `V` the pulled-back family factors through the residual block
`(Fᵢ∘g) u = ∑ⱼ qᵢⱼ u · (b u · residⱼ u)` (so `⟨F∘g⟩ ⊆ ⟨b⟩`, `q` `ContinuousOn V`), AND every entry
vanishes at the deepest point `(Fᵢ∘g) 0 = 0`. NO Bézout direction (born only at the terminal). -/
def StepInv (F : Fin M → (Fin D → ℝ) → ℝ) (g : (Fin D → ℝ) → (Fin D → ℝ))
    (b : (Fin D → ℝ) → ℝ) {nR : ℕ} (resid : Fin nR → (Fin D → ℝ) → ℝ)
    (q : Fin M → Fin nR → (Fin D → ℝ) → ℝ) (V : Set (Fin D → ℝ)) : Prop :=
  (∀ i j, ContinuousOn (q i j) V) ∧
    (∀ i, (F i ∘ g) 0 = 0) ∧
    (∀ u ∈ V, ∀ i, (F i ∘ g) u = ∑ j, q i j u * (b u * resid j u))

/-- **The terminal principal invariant** — BOTH divisibility `q` and Bézout `r`, the M'=1 compression
(`⟨F∘g⟩ = ⟨b⟩` on `V`): divisibility `(Fᵢ∘g) = qᵢ·b` and Bézout `b = ∑ᵢ rᵢ·(Fᵢ∘g)`, all
`ContinuousOn V`. BORN at the terminal state (`terminal_bezout`); consumed by
`principalInv_regionRepresents` (L1). -/
def PrincipalInv (F : Fin M → (Fin D → ℝ) → ℝ) (g : (Fin D → ℝ) → (Fin D → ℝ))
    (b : (Fin D → ℝ) → ℝ) (q r : Fin M → (Fin D → ℝ) → ℝ) (V : Set (Fin D → ℝ)) : Prop :=
  (∀ i, ContinuousOn (q i) V) ∧ (∀ i, ContinuousOn (r i) V) ∧
    (∀ u ∈ V, ∀ i, (F i ∘ g) u = q i u * b u) ∧
    (∀ u ∈ V, b u = ∑ i, r i u * (F i ∘ g) u)

/-! ## The path map — the composed shears ∘ block-center blow-ups along a branch -/

/-- **The path map**: the composition of the per-step coordinate changes `σ` along a root→leaf branch.
Head = root (outermost, applied last); tail = deeper toward the leaf. `pathMap [] = id`;
`pathMap (σ :: rest) = σ ∘ pathMap rest`. Each `σ = sh ∘ blockBlowupMap S p` is a unipotent shear ∘
block-center blow-up (shear-pin certificate): NOT a monomial map, but the shears are
Jacobian-exactly-1, so `|det D(pathMap)|` is a pure block-exceptional monomial and `unit ≡ 1`. -/
def pathMap : List ((Fin D → ℝ) → (Fin D → ℝ)) → (Fin D → ℝ) → (Fin D → ℝ)
  | [] => id
  | σ :: rest => σ ∘ pathMap rest

@[simp] theorem pathMap_nil : pathMap ([] : List ((Fin D → ℝ) → (Fin D → ℝ))) = id := rfl

@[simp] theorem pathMap_cons (σ : (Fin D → ℝ) → (Fin D → ℝ))
    (rest : List ((Fin D → ℝ) → (Fin D → ℝ))) :
    pathMap (σ :: rest) = σ ∘ pathMap rest := rfl

/-! ## L1 — `PrincipalInv → RegionRepresents` (both directions) -/

/-- **L1 — the terminal principal invariant gives both region-ideal inclusions.** The divisibility
quotients `q` and Bézout coefficients `r` ARE the `RegionRepresents` witnesses for the single dominant
monomial family `fun _ : Fin 1 ↦ b` — the `hideal_fwd`/`hideal_bwd` `Chart` fields. Strike-able
(repackage `q`/`r` through the `Fin 1` sum); region-quantified throughout. -/
@[blueprint]
theorem principalInv_regionRepresents (F : Fin M → (Fin D → ℝ) → ℝ)
    (g : (Fin D → ℝ) → (Fin D → ℝ)) (b : (Fin D → ℝ) → ℝ) (q r : Fin M → (Fin D → ℝ) → ℝ)
    (V : Set (Fin D → ℝ)) (h : PrincipalInv F g b q r V) :
    RegionRepresents (fun i ↦ F i ∘ g) (fun _ : Fin 1 ↦ b) V ∧
      RegionRepresents (fun _ : Fin 1 ↦ b) (fun i ↦ F i ∘ g) V := by
  -- map: B-L1-principalInv-to-region (divisibility ⇒ fwd inclusion; Bézout ⇒ bwd inclusion)
  sorry

/-! ## L3 / L4 — one recursion step preserves the interior `StepInv`

`σ = sh ∘ blockBlowupMap spec.center p` (block-center blow-up ∘ unipotent shear). `sh` is
Jacobian-exactly-1 (`∀ u, jacDet sh u = 1`), so `|det Dσ| = |det D(blockBlowupMap …)|` is a pure
`|S|`-center monomial, `unit ≡ 1` (feeds L6). The `EdgeSpec` (δ + center) is supplied by the fold per
tree edge; the child dominant law `b' = u_p^δ · (b∘σ)`, `δ = spec.δ = [J=0]`. -/

/-- **A per-edge spec** (elder A): what the fold reads off a `buildTree` edge — `δ = [J=0]` (off the
salvaged `ConState.cleared`) and the blow-up center `S`. δ and the center are one package (S1's
`blockBlowupMap` needs the center; δ is never guessed from the state nor branch-coded). -/
structure EdgeSpec (D : ℕ) where
  /-- `δ = [J = 0]` — whether the equal run starts at the dominant (a STATE property). -/
  δ : Bool
  /-- The blow-up center `S ⊆ Fin D` (block coordinates; spectators are `∉ S`). -/
  center : Finset (Fin D)

/-- **The coordinate-block coherence** (pnp-cover): the step map `σ = sh ∘ blockBlowupMap S p` is
injective off the pivot hyperplane `{w_p = 0}` — its exceptional/center locus is that coordinate
block. Feeds L6's a.e.-injectivity and L7's cover. -/
def CenterCoordAligned {D : ℕ} (sh : (Fin D → ℝ) → (Fin D → ℝ)) (S : Finset (Fin D)) (p : Fin D) :
    Prop :=
  Set.InjOn (fun u ↦ sh (blockBlowupMap S p u)) (Set.univ \ {w : Fin D → ℝ | w p = 0})

/-- **One recursion child** conforming to an `EdgeSpec` at pivot `p` (elder A/B): the CONSTRUCTION
supplies the unipotent shear `sh` (Jacobian-exactly-1), the child region (the pullback of the parent
region intersected with a chart domain — no implicit shrinking, D1), and the child `StepInv` for
`σ = sh ∘ blockBlowupMap spec.center p`, with the dominant law `b' = u_p^(if δ then 1 else 0)·(b∘σ)`
(δ = spec.δ = [J=0], UNIFORM across sub-cases — S2). `pivot ∈ spec.center` is imposed by the caller. -/
def BlockChild (F : Fin M → (Fin D → ℝ) → ℝ) (g : (Fin D → ℝ) → (Fin D → ℝ))
    (b : (Fin D → ℝ) → ℝ) (V : Set (Fin D → ℝ)) (spec : EdgeSpec D) (p : Fin D) : Prop :=
  ∃ (sh : (Fin D → ℝ) → (Fin D → ℝ)) (Vchart : Set (Fin D → ℝ)) (b' : (Fin D → ℝ) → ℝ)
    (nR' : ℕ) (resid' : Fin nR' → (Fin D → ℝ) → ℝ) (q' : Fin M → Fin nR' → (Fin D → ℝ) → ℝ),
    AnalyticOnNhd ℝ sh Set.univ ∧ sh 0 = 0 ∧ (∀ u, jacDet sh u = 1) ∧
      CenterCoordAligned sh spec.center p ∧ IsOpen Vchart ∧ (0 : Fin D → ℝ) ∈ Vchart ∧
      (∀ u, b' u = (u p) ^ (if spec.δ then 1 else 0) * b (sh (blockBlowupMap spec.center p u))) ∧
      StepInv F (fun u ↦ g (sh (blockBlowupMap spec.center p u))) b' resid' q'
        ((fun u ↦ sh (blockBlowupMap spec.center p u)) ⁻¹' V ∩ Vchart)

/-- **The case-2 one-step preservation obligation** (the Prop `case2_preserves_stepInv` proves; the
hypothesis the fold `leaf_stepInv_of_path` (L5) consumes). For an edge spec with a NONEMPTY center, a
case-2 (append) edge produces ONE child conforming to the spec at a center pivot. `0 < D` (elder C:
`|S| = 1` is a legitimate step; center-size bounds live in the spec, never the ambient). -/
def Case2Preservation : Prop :=
  ∀ {M D : ℕ} {F : Fin M → (Fin D → ℝ) → ℝ} {g : (Fin D → ℝ) → (Fin D → ℝ)}
    {b : (Fin D → ℝ) → ℝ} {nR : ℕ} {resid : Fin nR → (Fin D → ℝ) → ℝ}
    {q : Fin M → Fin nR → (Fin D → ℝ) → ℝ} {V : Set (Fin D → ℝ)},
    IsOpen V → (0 : Fin D → ℝ) ∈ V → StepInv F g b resid q V → 0 < D →
    ∀ spec : EdgeSpec D, spec.center.Nonempty →
    ∃ p : Fin D, p ∈ spec.center ∧ BlockChild F g b V spec p

/-- **The case-1 (coupled corank ≥ 2) one-step preservation obligation** (the Prop
`case1_preserves_stepInv` proves; the hypothesis L5 consumes). For an edge spec whose center has
`≥ 2` coordinates, a case-1 step produces TWO children at DISTINCT pivots of the ONE center (elder B:
`p_merge` at the existing exceptional, `p_split` at a `d`-entry) — `p_merge ≠ p_split` forces the two
children distinct (no single witness discharges both). `0 < D` (elder C). -/
def Case1Preservation : Prop :=
  ∀ {M D : ℕ} {F : Fin M → (Fin D → ℝ) → ℝ} {g : (Fin D → ℝ) → (Fin D → ℝ)}
    {b : (Fin D → ℝ) → ℝ} {nR : ℕ} {resid : Fin nR → (Fin D → ℝ) → ℝ}
    {q : Fin M → Fin nR → (Fin D → ℝ) → ℝ} {V : Set (Fin D → ℝ)},
    IsOpen V → (0 : Fin D → ℝ) ∈ V → StepInv F g b resid q V → 2 ≤ nR → 0 < D →
    ∀ spec : EdgeSpec D, 2 ≤ spec.center.card →
    ∃ (p_merge p_split : Fin D),
      p_merge ∈ spec.center ∧ p_split ∈ spec.center ∧ p_merge ≠ p_split ∧
        BlockChild F g b V spec p_merge ∧ BlockChild F g b V spec p_split

/-- **L3 — a case-2 step preserves the interior `StepInv` (the CLEAN regime, width ≤ 2).** The
residual telescopes; divisibility (+ vanishing) carried by the block-center witness law. NO Bézout
(false interior — pnp-case1). -/
@[blueprint]
theorem case2_preserves_stepInv : Case2Preservation := by
  -- map: B-L3-case2-preserves-stepInv (telescoping divisibility; b'=u_p^δ·(b∘σ), block-center σ)
  sorry

/-- **L4 — a case-1 (coupled corank ≥ 2) step preserves the interior `StepInv`. ⟨THE WALL⟩** The
frontier this expedition must build (charter §1.B — the coupled `diag(b)` recursion). Produces the
1(1) merge + 1(2) split children at distinct pivots of one center. The wall is the coupled
DIVISIBILITY at corank ≥ 2 (the residual entries share divisors; proving the coupled block-center
blow-up ∘ shear keeps `⟨entries⟩ ⊆ ⟨b'⟩` with the exact `u_p^δ` factor). The pnp-case1 certificate
refines THIS PROOF, not this statement. -/
@[blueprint]
theorem case1_preserves_stepInv : Case1Preservation := by
  -- map: B-L4-case1-coupled-preserves-stepInv ⟨THE WALL — coupled corank≥2 block-center divisibility⟩
  sorry

/-! ## `terminal_bezout` — principality is BORN at the terminal node -/

/-- **The terminal Bézout obligation** (the Prop `terminal_bezout` proves; L5 consumes it at each
leaf). See `terminal_bezout`. -/
def TerminalBezout : Prop :=
  ∀ {M D : ℕ} {F : Fin M → (Fin D → ℝ) → ℝ} {g : (Fin D → ℝ) → (Fin D → ℝ)}
    {b : (Fin D → ℝ) → ℝ} {q : Fin M → Fin 1 → (Fin D → ℝ) → ℝ} {V : Set (Fin D → ℝ)},
    IsOpen V → (0 : Fin D → ℝ) ∈ V →
    StepInv F g b (fun _ : Fin 1 ↦ 1) q V →
    ∀ (i₀ : Fin M) (unit : (Fin D → ℝ) → ℝ),
      ContinuousOn unit V → unit 0 ≠ 0 → (∀ u ∈ V, (F i₀ ∘ g) u = b u * unit u) →
    ∃ (V' : Set (Fin D → ℝ)) (r : Fin M → (Fin D → ℝ) → ℝ),
      IsOpen V' ∧ (0 : Fin D → ℝ) ∈ V' ∧ V' ⊆ V ∧
      PrincipalInv F g b (fun i ↦ q i 0) r V'

/-- **The NEW leaf — Bézout / principality is BORN at the terminal node.** At a terminal state
(`S = L`, `J ≥ 1`; residual trivial), with `V` an OPEN neighbourhood of `0` (else FALSE, e.g.
`V = {u | 0 < u 0}`), the cleared pivot supplies `(F i₀∘g) = b·unit` with `unit 0 ≠ 0`
(`b_{k₀} = Σ (U⁻¹)_{1i}(V⁻¹)_{j1}·(∏C∘g)_ij`, pnp §c). On the open `V' = V ∩ {unit ≠ 0}` this inverts
to `b = (1/unit)·(F i₀∘g)`, upgrading `StepInv` (divisibility) to the terminal `PrincipalInv` (both).
Consistent with S3: the terminal `b = ∏u` vanishes at `0` (`J ≥ 1`), so the entry `b·unit` vanishes
at `0` while `unit 0 ≠ 0` — no tension. `unit⁻¹` continuity is `ContinuousOn.inv₀` (named lemma, elder
D2), NOT an assumption. Region-quantified (shrinks to the open `V' ∋ 0`). -/
@[blueprint]
theorem terminal_bezout : TerminalBezout := by
  -- map: B-terminal-bezout (cleared-pivot entry = b·unit, unit 0 ≠ 0 ⇒ invert to Bézout on {unit≠0})
  sorry

end DLNFibre.Core.Aoyagi
