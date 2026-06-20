<task>
You are an independent fidelity reviewer of a Lean 4 + Mathlib formalisation. The build is green and
axiom-clean ([propext, Classical.choice, Quot.sound]) on all five new headlines; sorries = 0. Do NOT
re-derive the proofs. Judge ONLY whether the THEOREM NAMES + STATEMENTS + DOCSTRING GLOSSES match what is
actually proven — overclaim/underclaim hunting (precision discipline).

Context (paper: Lehalleur–Rimányi 2024, "Geometry of the fibers of the multiplication map of deep linear
neural networks"). The combinatorial codimension form is `codimForm N m = Σ_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} m_{uv}`
(paper Cor 3.5). `cCodim d r h := inf' over kostantPartitions d r of codimForm N (extendℤ m)` — the paper's C.

New module `Core/CThetaGeometric.lean` records (over `[Field k] [IsAlgClosed k] [CharZero k]`):

DELIVERABLE 1 — `codimRepCanonical_orbitRankLocus_eq_codimForm`:
  `((codimRepCanonical (orbitRankLocus (intervalDirectSum L))).toNat : ℤ) = codimForm N (multiplicityArray L)`
  where:
   - `orbitRankLocus M := {A | ∀ i≤j, rankPattern A i j ≤ rankPattern M i j}` — the determinantal RANK LOCUS,
     BY DEFINITION. The identity `orbitRankLocus M = closure of G_d-orbit of M` (paper Thm 3.8) is PROVED
     elsewhere in the engine (`Core/OrbitClosure.lean`), not in this module.
   - `codimRepCanonical Z := Ideal.height (vanishingIdeal (canonicalCoord '' Z))` — height of the vanishing
     ideal at the canonical one-variable-per-matrix-entry linear flattening. The catenary bridge
     `height + KrullDim(R/I) = ambient` is proved (`NullstellensatzCodim.lean`), so this is the genuine
     affine geometric codimension.
   - Proof feeds the discharged Voigt lemma `codimRep_orbitRankLocus_eq_orbitLinearCodim`
     (`codimRepCanonical (orbitRankLocus M) = (orbitLinearCodim M : ℕ∞)`, a FINITE ℕ cast) into a conditional
     headline + a `rfl` bridge `codimForm_multiplicityArray`.
  Docstring gloss: "the combinatorial codimension form IS the geometric orbit-closure codimension."

  Companion ℕ∞ form `codimRepCanonical_orbitRankLocus_eq_orbitLinearCodim`:
    `codimRepCanonical (orbitRankLocus (intervalDirectSum L)) = (orbitLinearCodim (intervalDirectSum L) : ℕ∞)`.

DELIVERABLE 2 — `cCodim_eq_inf_geomCodim`:
  `cCodim d r h = (kostantPartitions d r).inf' h (fun m ↦ ((codimRepCanonical (orbitRankLocus
     (intervalDirectSum (listOfPartition m)))).toNat : ℤ))`
  where `listOfPartition m` is an interval list with `multiplicityArray (listOfPartition m) = extendℤ m`
  (proved as full function equality, `multiplicityArray_listOfPartition`). Same `kostantPartitions d r` + same `h`
  as `cCodim`'s own def. Gloss: "C = min over Kostant partitions of the genuine GEOMETRIC orbit-closure codimension."

EXPLICITLY ROADMAPPED-OPEN (not claimed): the `Σ^r`-AGGREGATE reading — that cCodim/numTop are the geometric
codim / top-component-count of the WHOLE rank-r product locus Σ^r (a union of orbit closures). Σ^r is not
defined as a variety anywhere. numTop's geometric component-count reading is flagged OPEN.

Specific worries to adjudicate:
1. `.toNat` on an ℕ∞: if the height were ⊤, `.toNat = 0` would silently make D1 hold at a wrong value. Is the
   companion ℕ∞ form (`= (orbitLinearCodim : ℕ∞)`, finite) enough to certify `.toNat` is faithful here? (I claim yes.)
2. Is "the combinatorial form IS the geometric codimension" honest given Thm 3.8 is built into the DEFINITION of
   `orbitRankLocus` (the theorem is literally about the rank locus; the rank-locus = orbit-closure identity is
   proved separately)? Is the docstring's "(the rank locus, Thm 3.8 cited)" an overclaim or underclaim?
3. Does D2's `inf'` glossed as "min over Kostant partitions of the geometric codim" overclaim, given each summand
   reads `m` through `listOfPartition m` and the geometric codim is of `intervalDirectSum (listOfPartition m)`?
   Is the codimension a function of the multiplicity array alone (so "the orbit with multiplicities m" is well-defined)?
4. Any place where the [IsAlgClosed k][CharZero k] scope is silently dropped or where a codimension result is
   mis-named as RLCT / ½·codim.
</task>

<output_contract>
For each of the 4 worries: a one-line VERDICT (sound / overclaim / underclaim / cannot-tell-without-source) then
≤3 lines of reasoning. Then a final one-line OVERALL verdict: does the naming+gloss match the proven content?
Be terse. Flag any worry you cannot adjudicate from the description alone.
</output_contract>

<grounding_rules>
You have only this description, not the source. Mark every claim as INFERENCE (from the description) vs
FACT-YOU-CANNOT-VERIFY. Do not invent Mathlib lemma behaviour; if `.toNat`/`ENat` semantics matter, state the
standard semantics and flag if you're unsure of the Mathlib v4.29 specifics.
</grounding_rules>
