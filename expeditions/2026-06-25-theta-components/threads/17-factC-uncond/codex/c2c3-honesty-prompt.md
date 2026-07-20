<task>
I am a reviewer auditing the FIDELITY of two Lean 4 + Mathlib modules in a research
project on the geometry of a "DLN fibre". The math is commutative algebra / algebraic
geometry. I need a decorrelated second opinion on ONE thing: is the reduction to a
"single open geometric input" honest, or is it (a) smuggling the conclusion into a
hypothesis, (b) vacuous (hypothesis never satisfiable), or (c) circular?

Background claim ("fact C"): the reduced fibre variety is generically smooth. The team
claims to have discharged all commutative-algebra sub-walls UNCONDITIONALLY, leaving a
single named GEOMETRIC fact (called "C2(a)") deferred.

The three landed Lean theorems (exact statements, paraphrased to plain math):

C1 (pure comm-alg, claimed fully proved):
  For a reduced Noetherian k-algebra R and a minimal prime I (a top component's generic
  point), and given a k-algebra iso e : (R ⧸ I) ≃ₐ[k] D where D is a finitely-presented
  k-algebra DOMAIN that is IsSmoothAt k m at SOME prime m, conclude R is IsSmoothAt k I.
  Mechanism: D smooth somewhere ⟹ D smooth at its generic point ⊥ (domain + open smooth
  locus); transport ⊥ across e to ⊥ of R⧸I; localizing reduced R at I kills the kernel I
  (because ⋂ minimal primes = nilradical = ⊥ in a reduced ring, and the OTHER minimal
  primes' intersection is not ≤ I by incomparability), so Loc(R, I) ≃ₐ Loc(R⧸I, ⊥); then
  FormallySmooth.iff_of_equiv transfers IsSmoothAt.

C2 (the conditional, the lemma under audit):
  theorem isSmoothAt_sweepFibre_of_component_orbitSmooth :
    [IsAlgClosed k] (d : Fin (N+2) → ℕ) (r : ℕ) (hp hq : ...)
    (I : Ideal (sweepFibreRing k d r hp hq)) [I.IsPrime]
    (hImin : I ∈ minimalPrimes (sweepFibreRing ...))
    {d' : Fin (N+1) → ℕ}  (M : Tuple d')   -- d' is a FREE implicit, unrelated to d
    (e : (sweepFibreRing k d r hp hq ⧸ I) ≃ₐ[k] orbitRing M) :
    Algebra.IsSmoothAt k I
  Proof is just: apply C1 with D := orbitRing M, which is known (separately proved,
  unconditional) to be a finitely-presented domain that is IsSmoothAt at its normal-form
  point. So C2's ENTIRE content beyond C1 is: "given the iso e, done."
  The team flags `e` (existence of M and e for the intended fibre component) as the single
  DEFERRED geometric input "C2(a)", explicitly NOT proved.

C3 (transport to a chart, claimed proved given IsSmoothAt of sweepFibreRing):
  Given IsSmoothAt k q of sweepFibreRing at a top-component prime q, produces a chart
  element h with the source pivot chart `Away (chartDsig ...)` IsSmoothAt at every chart
  prime not containing h. Chain: a prior thread gives g∉q with Smooth(SchurLoc ⊗_k Away g);
  an iso SchurLoc ⊗ Away g ≃ Away(1⊗g) (localization-of-base-change); a BANKED chart iso
  `Away(chartDsig) ≃ₐ[k] SchurLoc ⊗_k sweepFibreRing`; abstract Smooth(Away ·) transport;
  basic-open bridge.

Questions:

Q1 (smuggling). Does the hypothesis `e : (R⧸I) ≃ₐ[k] orbitRing M` by itself logically
entail the conclusion `IsSmoothAt k I`? I.e., is the iso doing the work that should be
deferred, OR is the smoothness genuinely coming from the SEPARATE fact that orbitRing M is
smooth (a domain smooth somewhere)? If orbitRing M were an arbitrary domain with NO known
smooth point, would C2 still go through? Pin down precisely what `e` contributes vs what the
unconditional orbit-smoothness contributes.

Q2 (vacuity / non-vacuity). The hypothesis `e` could in principle be unsatisfiable for the
INTENDED I (the actual top components of the actual fibre). If no such (M, e) exists, C2 is
vacuously true and the "single open input" framing would be misleading. From the math: is it
PLAUSIBLE that a top-dim component of this rank-r product-locus fibre is isomorphic (as a
k-algebra / as a variety) to an orbit-closure coordinate ring? Or is there a structural
reason to doubt it? (I do NOT have the geometric theory; I want your prior on whether the
deferred fact is the RIGHT shape — a believable theorem — vs a fig leaf.)

Q3 (circularity in C3). C3 derives chart-smoothness FROM IsSmoothAt(sweepFibreRing) via a
banked chart iso `Away(chartDsig) ≃ SchurLoc ⊗ sweepFibreRing`. Is there any way this is
circular — e.g. could the chart iso secretly already encode the smoothness it's supposed to
transport? Or is "Smooth is preserved by ⊗ of smooth factors + localization + algebra iso"
a clean, non-circular transport?

Q4 (the d' free variable). In C2, `d'` (the orbit's dimension vector) is a free implicit,
totally unconstrained by the fibre data `d, r`. Is that a fidelity red flag (the theorem
quantifies over an orbit with NO relation to the fibre), or is it correct that the relation
is exactly what `e` is supposed to supply (so leaving d' free is honest)?
</task>

<output_contract>
Four sections Q1..Q4. Each: a one-word verdict (for Q1: SMUGGLING / HONEST; Q2: PLAUSIBLE /
DOUBTFUL / CANNOT-TELL; Q3: CIRCULAR / CLEAN; Q4: RED-FLAG / HONEST) then 2-5 sentences of
reasoning. Be terse and precise. End with a one-line overall: is calling C2(a) the "single
open geometric input" an honest characterization?
</output_contract>

<grounding_rules>
You do NOT have the Lean source or the geometric theory. Distinguish explicitly what you can
conclude from the stated math (FACT) vs what is your prior/inference (INFERENCE). Do not
invent Mathlib lemma behavior. For Q2 especially, your geometric prior is what I want, clearly
labeled as INFERENCE.
</grounding_rules>
