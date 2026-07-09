<task>
Independence audit of a Lean 4 formalisation. A "hero" theorem must be built INDEPENDENT
of a rival paper (Lehalleur-Rimanyi, "L&R"): the brief forbids any use of L&R's quiver /
orbit / Kostant machinery and their "Core-engine" CODIMENSION results on the path to the
headline. The headline is `aoyagi_learning_coefficient_gen` in
lean/DLNFibre/DLN/RLCT/Validate/HeadlineGenAssembly.lean.

I traced the transitive import DAG (317 DLNFibre modules) and the by-name symbol usage.
Findings (all are observed facts from grep/DAG, stated so you can challenge the INFERENCE):

FACT 1 (value): the headline's value `aoyagiLambda H r` and `lambdaCore` are defined in
lean/DLNFibre/DLN/RLCT/Foundations/Lambda.lean, which imports ONLY Mathlib
(Finset/Fintype/BigOperators/Rat/Real). Defined purely by a finite minimisation
`½·min_{T∈Adm} Mval(T)` over an admissible cone. No Core / quiver / codim import.

FACT 2 (proof symbols): the headline's proof term references only:
headline_frontRowColPivot_exists, deepest_regular_core_reduces_frontPivot_front,
d1ge_deepestPoint_via_explicit_core_genL_wired, d1ge_hAtV_explicit_close_gen,
aoyagi_learning_coefficient_frontPivot_front, deepestPoint, optimalSet, rlctAt, dlnLoss,
rlctAtOn, nRegGen, dlnLoss_deepest_core_ae_ne_zero, deepestPoint_isDeep,
reg_shift_add_core_eq_aoyagiLambda. None is a codim/quiver decl.

FACT 3 (the leak): the transitive closure DOES contain L&R engine modules:
Core.Orbit, Core.Gabriel, Core.OrbitVariety, Core.OrbitCodim, Core.OrbitLinearCodim,
Core.NullstellensatzCodim, Core.DeformationExt, Core.IntervalModule, Core.RankPattern,
Core.Barcode, Core.Submult, Core.GenericTuple. They all enter through a UNIQUE gateway:
the module Core.RankLocusClosed, which `import`s Core.OrbitVariety + Core.Orbit + Core.GenericTuple.

FACT 4 (mixed module): Core.RankLocusClosed.lean is MIXED. Lines ~42-150 are pure Mathlib
matrix/rank lemmas (rank_submatrix_le_rank, det_eq_zero_of_rank_lt,
exists_injective_linearIndependent_rows, exists_submatrix_det_ne_zero_of_le_rank,
rank_le_iff_forall_submatrix_det_eq_zero) using ONLY Mathlib. Lines ~152+ are the L&R orbit
content (eval_submult_genericTuple, rankMinorSet, image_orbitRankLocus_eq_zeroLocus,
isZariskiClosed_orbitRankLocus) using the L&R `Tuple`/`submult`/orbit machinery, which is why
the orbit imports are there.

FACT 5 (consumers): the ONLY capstone-path modules that import RankLocusClosed are
DLN.RLCT.Validate.D1HChartRank (direct) and Core.CommonPivotL2. BOTH reference exactly ONE
RankLocusClosed symbol: `exists_submatrix_det_ne_zero_of_le_rank` (a pure rank lemma, lines
110-135, Mathlib-only body). Neither references any orbit-half symbol.

FACT 6: a repo-wide grep of the capstone closure for codimFormula / cCodim / cValue /
cited_aoyagi_dln / addlongest / "C/2" / codimForm = ZERO hits. The only "Kostant" hits are
inside Core.RankPattern / Core.DeformationExt (the import-only orbit modules). All "Tuple.sort"
hits are Mathlib's Fin.Tuple.Sort, not L&R `Tuple`. "submult" hits are "submultiplicativity".

FACT 7: the separately-flagged module lean/DLNFibre/DLN/Aoyagi/ClosedForm.lean (which DOES
import Core.CThetaArbitrary + Core.FibreCodimFinal and proves 2λ=codimFormula) is imported by
NO module in the repo — it is an orphan, off every headline path.

MY INFERRED VERDICT (challenge it): the headline is content-independent in both VALUE and PROOF;
the L&R codim/quiver appearing in the transitive closure is a COSMETIC import-only leak caused by
a pure rank lemma being co-located in the mixed module RankLocusClosed with orbit content. The
minimal fix: split RankLocusClosed at ~line 151 into (a) a pure Mathlib rank-lemma module
(imports no Core), used by CommonPivotL2 + D1HChartRank, and (b) an orbit-content module (keeps
the OrbitVariety/Orbit/GenericTuple imports, imports (a)) that is off the capstone path. This
removes the entire orbit subtree from the closure.
</task>

<output_contract>
1. VERDICT: do you concur the entanglement is import-only (cosmetic), or is there a hole in the
   reasoning that would make it a genuine content dependency? One paragraph.
2. HOLES: list every way FACTS 1-7 could FAIL to establish independence that I have not ruled out
   — specifically: (i) can a Lean proof depend on a decl WITHOUT its module symbol appearing by
   name in the source (e.g. instance resolution, `open ... in`, notation, default instances,
   simp-set lemmas from an imported orbit module, or a def whose *definitional unfolding* pulls
   orbit content)? (ii) could the VALUE `aoyagiLambda` secretly route through codim via a lemma
   used to PROVE it equals something, even if its definition is Mathlib-only? (iii) `#print axioms`
   considerations. For each, say whether my grep/DAG evidence rules it out or whether a further
   check is needed, and name the exact check.
3. MINIMAL-FIX CRITIQUE: is the RankLocusClosed split at ~line 151 sound, and is there a cheaper
   or safer alternative? Flag any risk that the pure half secretly depends on the orbit half.
4. Keep it under ~450 words. Mark each claim [FACT-CHECK of my input] vs [INFERENCE] vs
   [RECOMMENDED CHECK].
</output_contract>

<grounding_rules>
You do NOT have the repo loaded; reason from the facts I gave. Do NOT invent Lean API. If a
claim needs the source to confirm, mark it [RECOMMENDED CHECK] and name the grep/command. Flag
inference vs fact explicitly. The value of your answer is finding a hole in my independence
argument that pure name-grep + import-DAG would miss.
</grounding_rules>
