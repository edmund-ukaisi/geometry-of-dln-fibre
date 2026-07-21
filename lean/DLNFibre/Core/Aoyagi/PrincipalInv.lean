import DLNFibre.Core.Aoyagi.OriginBlowup
import Meta.Cordon

/-!
# `Core.Aoyagi.PrincipalInv` — the path invariant + the algebraic recursion leaves

**BLUEPRINT (aoyagi-engine rung C; RESHAPED per the pnp-case1 verdict, thread 34).** The network-free
algebraic spine of the coupled product-ideal resolution monument (charter §1.B). Universalized over a
general ambient dimension `Fin D` and a general generator family `F` (statement gate (iii); the DLN
driver instantiates `D := flatDim d`, `F := coreGen d e`).

## Two invariants: the interior `StepInv` (divisibility only) vs the terminal `PrincipalInv` (both)

The pnp-case1 verdict (thread 34; decorrelated Codex + an independent impossibility proof + 3
batteries) established that a per-step invariant CANNOT bundle divisibility **and** Bézout:

* **Divisibility (D)** — `⟨(∏C)∘g⟩ ⊆ ⟨b₁⟩`, each entry `= b₁·q` with `q` continuous — IS a genuine
  per-step invariant (`StepInv`).
* **Bézout / principality (B)** — `b₁ ∈ ⟨(∏C)∘g⟩` — is **FALSE at the root and every interior state**:
  at layer `S < L` the pending tail `∏_{s>S}C` vanishes at the deepest point, so every quotient
  `q_ij(0) = 0`, and a Bézout representation would force `0 = 1` by continuity. Principality is **BORN
  at the terminal state** (`S = L`, `J ≥ 1`) by the cleared pivot (`terminal_bezout`). In-tree
  corroboration: thread-28 cert line 73 ("intermediate charts CAN be non-principal"), worked.tex:659
  ("the chain is a TERMINAL-chart invariant").

So a per-step `PrincipalInv`-preservation statement would be a FALSE frontier statement. The reshape:

* `StepInv F g b resid q V` — the **interior** invariant, **divisibility only** (statement gate (ii):
  an interior/mid-recursion/coupled instance IS this shape). Region-quantified (condition (1)): the
  quotient `q` is `ContinuousOn V` and the factorization holds `∀ u ∈ V` (`Set.EqOn`, NOT a germ).
* `PrincipalInv F g b q r V` — the **terminal** invariant, BOTH divisibility `q` and Bézout `r`, the
  M'=1 compression (`⟨(∏C)∘g⟩ = ⟨b₁⟩`; the full `diag(b₁,…,b_M)` of the path ledger collapses to the
  single dominant `⟨b₁⟩` — thread-31's closed form, condition (4)). Consumed by
  `principalInv_regionRepresents` (L1) to make the two `Chart` ideal fields.

## The intended matrix realization of `StepInv` (named, not silent — pnp §c, §d)

At the geometric state `(g, b, resid, V)` of a `ConState` node `(S, J)`, the pnp's faithful `StepInv`
is the matrix factorization, on an open `nbhd ∋ 0` (NOT a germ), with `ContinuousOn` cofactors `U, V`,
`U 0 = V 0 = I`:

  `(∏C)∘g = U · (diag b · [[E_J, 0],[0, D_J]] · ∏_{s>S}C) · V`   (i),   `∀ i, b_{k₀} ∣ b_i`   (ii),

plus divisibility-only (iii). The family-level `StepInv` below is that factorization read entrywise:
`resid` are the `D_J · ∏_{s>S}C` block entries; `q` the `U`-cofactor divided by `b`; and each
`(Fᵢ∘g) = ∑ⱼ qᵢⱼ·(b·residⱼ) = b·(∑ⱼ qᵢⱼ·residⱼ)` gives (iii). The `U 0 = V 0 = I` cofactor-at-0
nondegeneracy and the structural chain (ii) at all `L` are pnp §d **named residual assumptions**,
carried in the `StepInv` witness (the recursion's construction supplies them); the pivot-ordering
rendering of `k₀` is likewise a §d note. These are the honest gaps, named here, not hidden.
-/

open MeasureTheory Set Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

variable {M D : ℕ}

/-! ## The two invariants -/

/-- **The interior step invariant** — DIVISIBILITY ONLY (pnp-case1: Bézout is NOT per-step
preservable). On the region `V` the pulled-back family factors through the residual block:
`(Fᵢ∘g) u = ∑ⱼ qᵢⱼ u · (b u · residⱼ u)` — so every entry is divisible by the dominant monomial `b`
(quotient `∑ⱼ qᵢⱼ·residⱼ`), i.e. `⟨F∘g⟩ ⊆ ⟨b·resid⟩ ⊆ ⟨b⟩`, with `q` `ContinuousOn V`. This is the
entrywise reading of the matrix factorization (i)+(iii) (module docstring); `resid` are the residual
block entries `D_J·∏_{s>S}C`. Region-quantified, interior-expressible (`nR ≥ 2` coupled). NO Bézout
direction.

**FIDELITY (elder D4, verified against the page images).** Per-step, this IS the paper's INDUCTIVE
statement — the ideal identity WITH the pending tail `∏_{s>S}C` (Aoyagi p.15), NEVER principality;
principality appears only at the TERMINAL display (p.22; thread-28 cert line 73; worked.tex:659). The
projection cofactor `Q̂ = diag(b')·Q₁⁻¹·diag(b')⁻¹` (module §L3/L4) reproduces the paper's printed `P`
(pp.18/21) verbatim. The re-scope from a per-step `PrincipalInv` to this `StepInv` is a fidelity
CORRECTION toward the paper, not a weakening. -/
def StepInv (F : Fin M → (Fin D → ℝ) → ℝ) (g : (Fin D → ℝ) → (Fin D → ℝ))
    (b : (Fin D → ℝ) → ℝ) {nR : ℕ} (resid : Fin nR → (Fin D → ℝ) → ℝ)
    (q : Fin M → Fin nR → (Fin D → ℝ) → ℝ) (V : Set (Fin D → ℝ)) : Prop :=
  (∀ i j, ContinuousOn (q i j) V) ∧
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

/-! ## The path map — the composed shears ∘ blow-ups along a branch -/

/-- **The path map**: the composition of the per-step coordinate changes `σ` along a root→leaf branch.
Head = root (outermost, applied last); tail = deeper toward the leaf (innermost). `pathMap [] = id`;
`pathMap (σ :: rest) = σ ∘ pathMap rest`. Each `σ` is a unipotent shear ∘ monomial blow-up
(shear-pin certificate, thread 33): NOT a monomial map (from the second blow-up on, the
residual/next-layer coordinates are sheared), but the shears are Jacobian-exactly-1, so
`|det D(pathMap)|` is a pure blow-up monomial and the Jacobian `unit ≡ 1`. -/
def pathMap : List ((Fin D → ℝ) → (Fin D → ℝ)) → (Fin D → ℝ) → (Fin D → ℝ)
  | [] => id
  | σ :: rest => σ ∘ pathMap rest

@[simp] theorem pathMap_nil : pathMap ([] : List ((Fin D → ℝ) → (Fin D → ℝ))) = id := rfl

@[simp] theorem pathMap_cons (σ : (Fin D → ℝ) → (Fin D → ℝ))
    (rest : List ((Fin D → ℝ) → (Fin D → ℝ))) :
    pathMap (σ :: rest) = σ ∘ pathMap rest := rfl

/-! ## L1 — `PrincipalInv → RegionRepresents` (both directions) -/

/-- **L1 — the terminal principal invariant gives both region-ideal inclusions.** The divisibility
quotients `q` and Bézout coefficients `r` of `PrincipalInv` ARE the `RegionRepresents` witnesses for
the single dominant monomial family `fun _ : Fin 1 ↦ b` — exactly the `hideal_fwd` /`hideal_bwd`
`Chart` fields. Strike-able (the two representations are `q`/`r` repackaged through the `Fin 1` sum);
region-quantified throughout (condition (1)). -/
@[blueprint]
theorem principalInv_regionRepresents (F : Fin M → (Fin D → ℝ) → ℝ)
    (g : (Fin D → ℝ) → (Fin D → ℝ)) (b : (Fin D → ℝ) → ℝ) (q r : Fin M → (Fin D → ℝ) → ℝ)
    (V : Set (Fin D → ℝ)) (h : PrincipalInv F g b q r V) :
    RegionRepresents (fun i ↦ F i ∘ g) (fun _ : Fin 1 ↦ b) V ∧
      RegionRepresents (fun _ : Fin 1 ↦ b) (fun i ↦ F i ∘ g) V := by
  -- map: B-L1-principalInv-to-region (divisibility ⇒ fwd inclusion; Bézout ⇒ bwd inclusion)
  sorry

/-! ## L3 / L4 — one recursion step preserves the interior `StepInv`

Each step post-composes the path map with `σ = sh ∘ blowupMap p` (a monomial blow-up at pivot `p`
followed by a unipotent shear `sh`, shear-pin certificate). The shear is **Jacobian-exactly-1**
(`hsh_jac`), so `|det Dσ| = |det D(blowupMap p)|` is a pure monomial and the Jacobian `unit ≡ 1` —
this feeds L6's `hjac`. Both leaves preserve `StepInv` (divisibility only — the pnp-preservable part),
stated at an ARBITRARY interior state (statement gate (ii)). The witness law (pnp §c): the child
dominant `b'₁ = u^δ · φ*b₁` with `δ = [J=0]`; child quotients `q'_ij = (φ*q_ij)/u^δ` (the `/u` is
EXACT — polynomial, no localization); the right col-op `P` + Schur shear compose into `g`; the left
row-op `Q₁` stays the cofactor (row-scaled `Q̂ = diag(b')·Q₁⁻¹·diag(b')⁻¹`, unipotent, `= I` at `0`,
off-diagonal MAY vanish). -/

/-- **The pnp-cover inherited coherence condition** (thread 35 risk note; made EXPLICIT here, not
implicit): at a step the blow-up center is a COORDINATE BLOCK in the current (sheared) coordinates —
required at EVERY constructor (incl. join / pivot-zero) for the full cover and the pathwise fold.
Encoded as: the step map `σ = sh ∘ blowupMap p` is injective off the COORDINATE hyperplane
`{u_p = 0}` (its exceptional/center locus is that coordinate block). Feeds L6's a.e.-injectivity and
L7's cover. -/
def CenterCoordAligned {D : ℕ} (sh : (Fin D → ℝ) → (Fin D → ℝ)) (p : Fin D) : Prop :=
  Set.InjOn (fun u ↦ sh (blowupMap p u)) (Set.univ \ {w : Fin D → ℝ | w p = 0})

/-- **One recursion child** produced by a one-step preservation: the CONSTRUCTION supplies the step
map `σ = sh ∘ blowupMap p` (`p` the blow-up pivot, `sh` a unipotent shear — shear-pin certificate),
the child region — made EXPLICIT (elder D1) as the pullback of the parent region intersected with the
chart domain, `(σ ⁻¹' V) ∩ Vchart` (no implicit shrinking) — and the child `StepInv`. The shear is
Jacobian-exactly-1 (`∀ u, jacDet sh u = 1`, so `|det Dσ| = |det D(blowupMap p)|` is a pure monomial,
`unit ≡ 1` — feeds L6); `CenterCoordAligned sh p` is the pnp-cover coherence (explicit). The residual
may grow (case-2 append) or shrink (case-1 clear); termination is inherited from the built tree's
well-foundedness (the geometric fold follows a FINITE branch), NOT a residual measure. -/
def StepInvChild (F : Fin M → (Fin D → ℝ) → ℝ) (g : (Fin D → ℝ) → (Fin D → ℝ))
    (V : Set (Fin D → ℝ)) : Prop :=
  ∃ (p : Fin D) (sh : (Fin D → ℝ) → (Fin D → ℝ)) (Vchart : Set (Fin D → ℝ)) (b' : (Fin D → ℝ) → ℝ)
    (nR' : ℕ) (resid' : Fin nR' → (Fin D → ℝ) → ℝ) (q' : Fin M → Fin nR' → (Fin D → ℝ) → ℝ),
    AnalyticOnNhd ℝ sh Set.univ ∧ sh 0 = 0 ∧ (∀ u, jacDet sh u = 1) ∧ CenterCoordAligned sh p ∧
      IsOpen Vchart ∧ (0 : Fin D → ℝ) ∈ Vchart ∧
      StepInv F (fun u ↦ g (sh (blowupMap p u))) b' resid' q'
        ((fun u ↦ sh (blowupMap p u)) ⁻¹' V ∩ Vchart)

/-- **The case-2 one-step preservation obligation** (the Prop `case2_preserves_stepInv` proves; the
hypothesis the fold `leaf_stepInv_of_path` (L5) consumes). A case-2 (append) edge produces ONE
child. -/
def Case2Preservation : Prop :=
  ∀ {M D : ℕ} {F : Fin M → (Fin D → ℝ) → ℝ} {g : (Fin D → ℝ) → (Fin D → ℝ)}
    {b : (Fin D → ℝ) → ℝ} {nR : ℕ} {resid : Fin nR → (Fin D → ℝ) → ℝ}
    {q : Fin M → Fin nR → (Fin D → ℝ) → ℝ} {V : Set (Fin D → ℝ)},
    IsOpen V → (0 : Fin D → ℝ) ∈ V → StepInv F g b resid q V → StepInvChild F g V

/-- **The case-1 (coupled corank ≥ 2) one-step preservation obligation** (the Prop
`case1_preserves_stepInv` proves; the hypothesis L5 consumes). A case-1 step forks into the 1(1)
(merge) and 1(2) (split) child edges — the conclusion produces the child for EACH branch
(`branch : Bool`, `true` = 1(1) merge, `false` = 1(2) split; the witness law's `δ = [J=0]` differs
between them). -/
def Case1Preservation : Prop :=
  ∀ {M D : ℕ} {F : Fin M → (Fin D → ℝ) → ℝ} {g : (Fin D → ℝ) → (Fin D → ℝ)}
    {b : (Fin D → ℝ) → ℝ} {nR : ℕ} {resid : Fin nR → (Fin D → ℝ) → ℝ}
    {q : Fin M → Fin nR → (Fin D → ℝ) → ℝ} {V : Set (Fin D → ℝ)},
    IsOpen V → (0 : Fin D → ℝ) ∈ V → StepInv F g b resid q V → 2 ≤ nR →
    ∀ _branch : Bool, StepInvChild F g V

/-- **L3 — a case-2 step preserves the interior `StepInv` (the CLEAN regime, width ≤ 2).** The
residual telescopes; divisibility is carried by the witness law (module §L3/L4). Region-quantified;
interior-expressible; NO Bézout claim (that would be false interior — pnp-case1). -/
@[blueprint]
theorem case2_preserves_stepInv : Case2Preservation := by
  -- map: B-L3-case2-preserves-stepInv (telescoping divisibility; witness b'=u^δ·φ*b, q'=(φ*q)/u^δ)
  sorry

/-- **L4 — a case-1 (coupled corank ≥ 2) step preserves the interior `StepInv`. ⟨THE WALL⟩** The
frontier this expedition must build (charter §1.B — the coupled `diag(b)` recursion dodged for
multiple expeditions). Produces BOTH the 1(1) and 1(2) children with a STRICTLY SMALLER residual
(`nR' < nR` — the cleared pending pivot; recursion progress). The wall is the coupled DIVISIBILITY at
corank ≥ 2 (`2 ≤ nR`): the residual entries share divisors, and proving the coupled shear ∘ blow-up
keeps `⟨entries⟩ ⊆ ⟨b'⟩` with the EXACT `/u^δ` quotient is the genuine new proof-engineering. NO
Bézout (born only at the terminal, `terminal_bezout`). The pnp-case1 seat's certificate refines THIS
PROOF, not this statement. -/
@[blueprint]
theorem case1_preserves_stepInv : Case1Preservation := by
  -- map: B-L4-case1-coupled-preserves-stepInv ⟨THE WALL — coupled corank≥2 divisibility⟩
  sorry

/-! ## `terminal_bezout` — principality is BORN at the terminal node (the pnp-corrected leaf) -/

/-- **The terminal Bézout obligation** (the Prop `terminal_bezout` proves; L5 consumes it at each
leaf). See `terminal_bezout`. -/
def TerminalBezout : Prop :=
  ∀ {M D : ℕ} {F : Fin M → (Fin D → ℝ) → ℝ} {g : (Fin D → ℝ) → (Fin D → ℝ)}
    {b : (Fin D → ℝ) → ℝ} {q : Fin M → Fin 1 → (Fin D → ℝ) → ℝ} {V : Set (Fin D → ℝ)},
    StepInv F g b (fun _ : Fin 1 ↦ 1) q V →                         -- terminal: residual trivial
    ∀ (i₀ : Fin M) (unit : (Fin D → ℝ) → ℝ),
      ContinuousAt unit 0 → unit 0 ≠ 0 → (∀ u ∈ V, (F i₀ ∘ g) u = b u * unit u) →  -- cleared pivot
    ∃ (V' : Set (Fin D → ℝ)) (r : Fin M → (Fin D → ℝ) → ℝ),
      IsOpen V' ∧ (0 : Fin D → ℝ) ∈ V' ∧ V' ⊆ V ∧
      PrincipalInv F g b (fun i ↦ q i 0) r V'

/-- **The NEW leaf — the Bézout / principality is BORN at the terminal node.** At a terminal state
(`S = L`, `J ≥ 1`; residual trivial) the cleared pivot supplies an entry `(F i₀∘g) = b·unit` with
`unit 0 ≠ 0` (`b_{k₀} = Σ (U⁻¹)_{1i}(V⁻¹)_{j1}·(∏C∘g)_ij`, pnp §c). On the open `V' = V ∩ {unit ≠ 0}`
this inverts to the Bézout `b = (1/unit)·(F i₀∘g)`, upgrading the interior `StepInv` (divisibility) to
the terminal `PrincipalInv` (both). This is where principality comes from — it does NOT hold interior
(pnp-case1). Region-quantified (the region shrinks to `V'`, still open `∋ 0`).

**(elder D2)** The `unit⁻¹` continuity is the NAMED STANDARD LEMMA `ContinuousAt.inv₀` (a continuous
function nonzero at a point has a continuous reciprocal there — the scalar case of the continuous
inverse of a nonsingular continuous matrix `U, V` on a region), NOT an assumption: `V'` is the open
set where `unit ≠ 0` and `(1/unit)` is continuous there by that lemma. -/
@[blueprint]
theorem terminal_bezout : TerminalBezout := by
  -- map: B-terminal-bezout (cleared-pivot entry = b·unit, unit 0 ≠ 0 ⇒ invert to Bézout on {unit≠0})
  sorry

end DLNFibre.Core.Aoyagi
