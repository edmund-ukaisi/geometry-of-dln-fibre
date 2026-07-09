**1. VERDICT**

[INFERENCE] I mostly concur: on FACTS 1-7, the L&R material looks like an import-closure leak, not a value/proof dependency. The strongest point is FACT 5: both capstone consumers use only `exists_submatrix_det_ne_zero_of_le_rank`, and FACT 4 says that lemma lives in the Mathlib-only half. But this is not fully established by source grep alone; Lean elaboration and transitive proof bodies can introduce dependencies invisible in source text.

**2. HOLES**

[FACT-CHECK of my input] A Lean source proof can depend on declarations whose names do not appear literally in the source: typeclass resolution, coercions, notation expansion, `simp` lemmas, default instances, attributes, elaborator-selected theorem variants, and generated recursors can all insert constants.

[RECOMMENDED CHECK] Source grep does not rule this out. Check the elaborated/kernel dependencies of `aoyagi_learning_coefficient_gen`, not just source names. Use a Lean environment script that recursively traverses the theorem’s proof expression and reports all constants, then filter for `DLNFibre.Core.*`, `codim`, `Orbit`, `Gabriel`, `Tuple`, etc.

[FACT-CHECK of my input] A theorem can also depend transitively on another theorem’s proof without that theorem’s dependencies appearing in the headline source. If FACT 2 lists only direct constants in the headline proof term, it does not rule out L&R use inside, say, `d1ge_deepestPoint_via_explicit_core_genL_wired`.

[RECOMMENDED CHECK] Run the same recursive dependency collection on every direct proof symbol in FACT 2, especially the bridge lemmas involving `core`, `frontPivot`, and `reg_shift_add_core_eq_aoyagiLambda`.

[INFERENCE] The value `aoyagiLambda` being Mathlib-only is enough to establish definitional value-independence from codim, assuming FACT 1 is exact. A lemma proving `aoyagiLambda = codimFormula / 2` would not contaminate the definition unless used in the headline proof path.

[RECOMMENDED CHECK] Confirm no theorem in the recursive proof dependency closure mentions `ClosedForm`, `codimFormula`, `cCodim`, `cValue`, or L&R orbit modules. Your grep is strong evidence but not a kernel-level check.

[FACT-CHECK of my input] `#print axioms` is relevant but insufficient. It detects axioms/trust assumptions, not ordinary theorem dependencies such as codim lemmas.

[RECOMMENDED CHECK] Still run `#print axioms aoyagi_learning_coefficient_gen` to document whether the headline relies only on expected axioms, but do not treat it as an independence proof.

**3. MINIMAL-FIX CRITIQUE**

[INFERENCE] The split is sound if lines ~42-150 truly import only Mathlib concepts and compile without Core imports. Moving `exists_submatrix_det_ne_zero_of_le_rank` and its prerequisite rank lemmas into a new pure module is the right structural fix.

[RECOMMENDED CHECK] Compile the pure module with only Mathlib imports, then update `D1HChartRank` and `CommonPivotL2` to import it directly. Run `lake env lean` on those modules and recompute the capstone import closure.

[INFERENCE] A cheaper alternative is to duplicate just `exists_submatrix_det_ne_zero_of_le_rank` locally, but that is less safe long-term: it hides the boundary instead of enforcing it. The split gives a durable audit boundary.

[RECOMMENDED CHECK] After the split, verify `RankLocusClosed` orbit-half imports the pure module, not vice versa, and that the capstone closure has zero `Core.Orbit*`, `Core.Gabriel`, `Core.*Codim`, `Core.DeformationExt`, `Core.GenericTuple`, and `Core.Submult` modules.