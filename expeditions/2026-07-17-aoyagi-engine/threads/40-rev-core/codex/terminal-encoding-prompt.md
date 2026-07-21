<task>
You are a decorrelated fidelity/soundness reviewer for a Lean 4 formalisation of Aoyagi's
resolution-of-singularities machinery for deep linear networks. Audit whether TWO Lean theorems
faithfully encode an informal certificate and whether either is unsound or vacuous. This is pen-and-paper
math review — you do NOT have the repo; reason from the definitions I paste.

DEFINITIONS (verbatim). All functions are ℝ-valued on the ambient (Fin D → ℝ). `∘` is function comp.

  StepInv F g b resid q V :=
    (∀ i j, ContinuousOn (q i j) V) ∧
    (∀ i, (F i ∘ g) 0 = 0) ∧
    (∀ u ∈ V, ∀ i, (F i ∘ g) u = ∑ j, q i j u * (b u * resid j u))
  -- F : Fin M → (Fin D→ℝ)→ℝ ; g : (Fin D→ℝ)→(Fin D→ℝ) ; b : (Fin D→ℝ)→ℝ ;
  -- resid : Fin nR → (Fin D→ℝ)→ℝ ; q : Fin M → Fin nR → (Fin D→ℝ)→ℝ ; V : Set (Fin D→ℝ)

  PrincipalInv F g b q r V :=
    (∀ i, ContinuousOn (q i) V) ∧ (∀ i, ContinuousOn (r i) V) ∧
    (∀ u ∈ V, ∀ i, (F i ∘ g) u = q i u * b u) ∧            -- divisibility (⟨F∘g⟩ ⊆ ⟨b⟩)
    (∀ u ∈ V, b u = ∑ i, r i u * (F i ∘ g) u)              -- Bézout      (⟨b⟩ ⊆ ⟨F∘g⟩)
  -- q r : Fin M → (Fin D→ℝ)→ℝ

  RegionRepresents G F V :=  -- "each G_i ∈ ideal⟨F⟩ on V", i.e. ⟨G⟩ ⊆ ⟨F⟩ on V
    ∃ a, (∀ i j, ContinuousOn (a i j) V) ∧ (∀ u ∈ V, ∀ i, G i u = ∑ j, a i j u * F j u)

THEOREM 1 (terminal_bezout):
  For all M D F g b (q : Fin M → Fin 1 → (Fin D→ℝ)→ℝ) V:
    IsOpen V → (0:Fin D→ℝ) ∈ V →
    StepInv F g b (fun _:Fin 1 ↦ 1) q V →                  -- residual is the single constant-1 entry
    ∀ (i₀ : Fin M) (unit : (Fin D→ℝ)→ℝ),
      ContinuousOn unit V → unit 0 ≠ 0 →
      (∀ u ∈ V, (F i₀ ∘ g) u = b u * unit u) →             -- the "cleared pivot" factorization
    ∃ V' r, IsOpen V' ∧ (0:Fin D→ℝ) ∈ V' ∧ V' ⊆ V ∧
      PrincipalInv F g b (fun i ↦ q i 0) r V'
  PROOF SKETCH: V' := V ∩ {unit ≠ 0} (open, ∋0 since unit 0≠0). r i := if i=i₀ then unit⁻¹ else 0.
  Divisibility transported from StepInv (resid≡1, Fin 1 sum collapses: (F i∘g)=q i 0·b).
  Bézout: b = unit⁻¹·(F i₀∘g) = unit⁻¹·(b·unit) = b on {unit≠0}.

THEOREM 2 (principalInv_regionRepresents):
  PrincipalInv F g b q r V →
    RegionRepresents (fun i↦F i∘g) (fun _:Fin 1↦b) V ∧
    RegionRepresents (fun _:Fin 1↦b) (fun i↦F i∘g) V
  PROOF: witness the ∃ cofactors with q (fwd, Fin 1 collapse) and r (bwd).

THE INFORMAL CERTIFICATE these must match (thread-34 split):
  - The terminal state of the resolution recursion is "S=L ∧ J≥1": S=L means the residual block is
    exhausted (trivial, single ≡1 entry); J≥1 means a "cleared pivot" produced a BARE diagonal entry
    b·unit with unit(0)≠0.
  - Divisibility (⟨F∘g⟩⊆⟨b⟩) holds at every interior state (StepInv), but Bézout/principality
    (⟨b⟩⊆⟨F∘g⟩) is FALSE at the root and every interior state and is BORN ONLY terminally.
  - PrincipalInv (both inclusions) is a TERMINAL theorem; L1 (Theorem 2) then converts it to the two
    RegionRepresents inclusions, feeding the chart-geometry leaf unchanged.
  - Consumer of Theorem 1 (call it L5): a fold along a root→leaf tree branch must, at the leaf, supply
    (a) StepInv with the Fin-1 resid≡1 terminal residual, and (b) the cleared-pivot factorization with
    unit(0)≠0; it then sets the chart region := terminal_bezout's shrunk V'.
</task>

<output_contract>
Answer these five questions, each as a short labelled block. Be terse and concrete; a counterexample
beats an adjective.

Q1 TERMINAL-ENCODING FIDELITY: Does "StepInv with resid = (fun _:Fin 1↦1)" + the cleared-pivot
   hypothesis faithfully encode "S=L ∧ J≥1"? Is anything encoded weaker or stronger than the informal
   terminal state? (Note StepInv also carries (F i∘g) 0 = 0 for all i.)

Q2 SOUNDNESS: Is Theorem 1 true as stated? Is Theorem 2 true as stated? Any missing/spurious hypothesis
   that makes either false, or vacuous? Check specifically: (i) does StepInv's (F i₀∘g) 0=0 combined
   with the cleared-pivot at u=0 and unit 0≠0 force b 0=0, and is that a problem? (ii) is the openness
   of V genuinely required for the CONCLUSION (existence of open V'⊆V ∋0), or only for this proof?

Q3 VACUITY / TRIVIAL-SATISFIABILITY: Can PrincipalInv or terminal_bezout be satisfied trivially/vacuously
   anywhere (e.g. b≡0 on V, empty V', degenerate D=1 or M=1)? Distinguish "sound but degenerate sub-case"
   from "vacuous theorem".

Q4 CIRCULARITY: Is RegionRepresents a definitional re-packaging (rfl-alias) of PrincipalInv, making
   Theorem 2 content-free? Argue from the two definitions.

Q5 CONSUMER-FIT: Are Theorem 1's hypothesis shapes (StepInv resid≡1 Fin 1; cleared-pivot unit 0≠0)
   ACTUALLY suppliable by the described L5 fold at a leaf, and does the region-shrink (chart region = V')
   compose correctly? Name any shape mismatch that would block the wiring.
</output_contract>

<grounding_rules>
Reason only from the pasted definitions. Mark each claim as [PROVEN from the defs] or [INFERENCE].
If a question is under-specified by what I pasted, say so rather than guessing. Do not invent Lean lemma
names. A "looks fine" with no argument is worthless — show the collapse/counterexample.
</grounding_rules>
