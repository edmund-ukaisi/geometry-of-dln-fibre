<task>
I am formalising in Lean 4 / Mathlib (v4.29) the orbit-stratification of the rank-r product locus of
deep linear networks (Le Halleur–Rimányi 2024, Cor 4.4 / the paper's stratification
`Σ̄^r = ⋃_M Ō_M`). I need a SECOND OPINION on the cleanest INDEX FORM for the set-level equality, so
that a later thread (G3) can consume it to characterise irreducible components = maximal `Ō_M`.

Landed Lean objects (all `Set (Tuple d)` for a fixed dimension vector `d : Fin (N+1) → ℕ`, `Tuple d`
= composable matrix tuples over a field `k`):
- `mult d A : Matrix … k`  — the ordered product `A_N ⋯ A_1`.
- `productRankLocusLE d r := {A | (mult d A).rank ≤ r}`  — the closed locus `Σ̄^r`.
- `orbitRankLocus M := {A | ∀ i j (h:i≤j), rankPattern d A i j h ≤ rankPattern d M i j h}` — the orbit
  closure `Ō_M` (Abeasis–Del Fra Thm 3.8, proved). Depends only on `rankPattern M`.
- `rankPattern d A i j h := (submult d A i j h).rank`; the corner entry
  `rankPattern d A 0 (last N) = (mult d A).rank` (G1, a one-liner via `mult_eq_submult`).
- `self_mem_orbitRankLocus M : M ∈ orbitRankLocus M`.
- Gabriel: `rankPattern_eq_iff_orbit A B : (∀ i j h, rankPattern A = rankPattern B) ↔ ∃ P, P • A = B`;
  `baseChange_normalForm A` gives a normal-form tuple `N₀` with `P • A = N₀` (so equal rank patterns).

Key observation: for the SET equality `Σ̄^r = ⋃_{corner(M) ≤ r} Ō_M`, the `⊆` direction is trivial by
taking `M := A` itself (`A ∈ orbitRankLocus A` and `corner(A) = (mult A).rank ≤ r`). The Gabriel
normal-form machinery is NOT logically required for the bare set equality with this index. It IS the
honest content of "every tuple is in the closure of its own Gabriel orbit", and it pins the union to a
finite/canonical family.

Candidate index forms for the headline:
  (A) `productRankLocusLE d r = ⋃ (M : Tuple d) (_ : (mult d M).rank ≤ r), orbitRankLocus M`
      — union over ALL corner-≤r tuples; `⊆` trivial via `M:=A`.
  (B) membership iff: `A ∈ productRankLocusLE d r ↔ ∃ M, (mult d M).rank ≤ r ∧ A ∈ orbitRankLocus M`.
  (C) a union indexed by a CANONICAL finite family (Gabriel normal forms / Kostant partitions with
      corner ≤ r), so the RHS is manifestly a finite union of distinct orbit closures.

G3's goal: irreducible components of `Σ̄^r` = the MAXIMAL `Ō_M` (entrywise rank-pattern order). It will
use Mathlib `irreducibleComponents`, `mem_of_subset_sUnion_irreducibleComponents` (a component inside a
finite union of irreducible closeds is one of them), and the fact `orbitRankLocus M` is irreducible +
closed. Crucially `orbitRankLocus M` depends only on `rankPattern M`, so the "all M" union (A) collapses
to a finite family of distinct closed sets.
</task>

<output_contract>
1. Recommend ONE headline index form (A/B/C or a hybrid) for the G2 set equality, and say which
   auxiliary forms to also export. 2–4 sentences of reasoning each.
2. State whether G3 (components = maximal Ō_M via the Mathlib finite-union API) is better served by the
   "all M" union (A) or a canonical finite index (C) — i.e. where the finiteness/maximality bookkeeping
   should live: in G2's statement, or deferred to G3.
3. Flag any TRAP in taking `M := A` for the `⊆` direction (e.g. does it make the statement vacuous or
   harder for G3 to consume? does it hide the Gabriel content the brief wants delivered?).
4. One paragraph: should the Gabriel-membership lemma be delivered as a SEPARATE named brick even if the
   bare set equality doesn't need it? (The brief flags it as a deliverable.)
Keep it under ~400 words. Mark inference vs. fact explicitly.
</output_contract>

<grounding_rules>
You may reason from the Lean/Mathlib facts stated above as given. Do not assume any Mathlib lemma exists
beyond those named; if your recommendation needs another, flag it as "needs verification". Distinguish
"this is forced by the math" from "this is a Lean-ergonomics judgement".
</grounding_rules>
