<task>
I am formalising in Lean 4 an order-isomorphism between two finite posets. I need an EXPLICIT,
closed-form encoding map (and its inverse) at a Lean-implementable level of precision. A prior
certificate proved the iso EXISTS via a generic poset backtracker, but did NOT give an explicit
transcribable formula for the map. Your job is to design the explicit map + inverse + the both-
directions monotonicity argument.

SETUP (Aoyagi's DLN learning-coefficient combinatorics).
Fix M = (M^1, ..., M^{L+1}) a tuple of positive integers (0-indexed M[0..L]).
A "profile" is T = (t^1, ..., t^L) ∈ ℕ^L. Set t^0 := M^1 (= M[0]). Admissible profiles ("Adm M"):
  - weakly decreasing: t^1 ≥ t^2 ≥ ... ≥ t^L,
  - last is zero: t^L = 0,
  - per-coord bound: t^j ≤ admBound(j) where admBound(0)=min(M[0],M[1]), admBound(j)=M[j+1] for j≥1.
The "value" of a profile (Aoyagi p.22):
  Mval(T) = (M^1 - t^1)(M^2 - t^1) + Σ_{j=2}^{L} (t^{j-1} - t^j)(M^{j+1} - t^j)   [over ℤ].
Let minAdm = min over Adm of Mval. The DOMAIN poset is
  bindingSet = { T ∈ Adm M : Mval(T) = minAdm },  ordered by COORDINATEWISE ≤ on ℕ^L.

The CODOMAIN poset is BoxPart(ℓ,a) = { antitone f : Fin a → ℕ with f i ≤ ℓ - a }, ordered
coordinatewise. Here (ℓ,a) are Aoyagi's Def-3 selectors on M: ℓ = qipM(sorted M) (the active-set
size), a = the residue (0 < a ≤ ℓ). |BoxPart(ℓ,a)| = C(ℓ,a), chainHeight = a(ℓ-a)+1.

VERIFIED FACT (numerics + Lean): bindingSet ≃o BoxPart(ℓ,a) as posets (117/117 sweep + trap cores).
|bindingSet| = C(ℓ,a). The naive rank = Σ t^j FAILS (it is not graded — a cover can jump Σ by 2 —
and it sends incomparable profiles to the same box). So the map must use the box/inversion rank, NOT
the coordinate sum.

THE RECIPE from the certificate (prose, needs to be made precise):
"From T, form increments e_j = t^{j-1} - t^j ≥ 0 (Σ e_j = M^1). The binding constraint forces
exactly a of the ℓ 'Lemma-4 steps' to be the large (M) step and ℓ-a the small (M-1) step [M here =
Aoyagi's ceiling ceil(activeSum/ℓ)]. Let A(T) ⊆ {1..ℓ}, |A|=a, be the positions of the M-steps.
Then the Young diagram is λ_i = #{(M-1)-steps before the i-th M-step}, an antitone f ∈ BoxPart(ℓ,a).
Canonical Birkhoff form: enc(T) = { j ∈ J(P) : j ≤ T }, join-irreducibles ↔ the a×(ℓ-a) cell grid."

WORKED DATA (to pin conventions):
- M=[2,2,2,2,2] (L=4): ℓ=4, a=2, M^1=2. The 6 minimisers T (as (t^1..t^4)) and increments e=(e_1..e_4):
  (1,0,0,0) e=(1,1,0,0);  (1,1,0,0) e=(1,0,1,0);  (1,1,1,0) e=(1,0,0,1);
  (2,1,0,0) e=(0,1,1,0);  (2,1,1,0) e=(0,1,0,1);  (2,2,1,0) e=(0,0,1,1).
  Here e_j ∈ {0,1}, exactly a=2 ones; A = positions of the ones; box via λ_i = p_i - i works. This case
  has ℓ = L = 4, so "ℓ steps" = the L increments. CLEAN.
- M=[1,1,2,1] (L=3): ℓ=2, a=1, M^1=1. The 2 minimisers: (0,0,0) e=(1,0,0); (1,1,0) e=(0,0,1).
  Here the single M-step (nonzero increment) sits at profile-position 1 vs 3, and must map to active-slot
  1 vs 2 of ℓ=2. So the profile-position → active-slot(1..ℓ) map is NON-TRIVIAL and M-dependent (L=3≠ℓ=2).
  This is the crux I need nailed.

The hard part: L (profile length) ≠ ℓ (active size) in general. The "ℓ Lemma-4 steps" are a REGROUPING
of the L increments into ℓ active steps of size (ceilingM) or (ceilingM-1). I need the EXACT regrouping.
</task>

<output_contract>
Four sections, concise:
1. EXPLICIT enc(T): a closed-form function bindingSet → (Fin a → ℕ). Give the precise definition of
   A(T) ⊆ {1..ℓ} (the M-step positions) from T — including EXACTLY how the L increments regroup into
   the ℓ active steps and how ceilingM is used — verified against BOTH worked examples above. Then the
   λ_i formula. State it at a level I could transcribe into Lean directly.
2. EXPLICIT inverse dec(f): (Fin a → ℕ) → bindingSet. Closed form.
3. Both-directions monotonicity: why T ≤ T' (coordinatewise) ⟺ enc(T) ≤ enc(T') (coordinatewise). Which
   direction is the hazard and why it holds.
4. Lean formalisation recommendation: the cleanest way to build this ≃o in Lean 4 / Mathlib — whether to
   go via an explicit Equiv + map_rel_iff', or via a Finset bijection + OrderIso.ofBijective-style, or a
   direct construction. Flag any step likely to be painful (e.g. the sorted-M vs unsorted-M coupling: the
   domain Adm uses M unsorted but ℓ,a come from sorted M).
</output_contract>

<grounding_rules>
Distinguish clearly: (a) what you can DERIVE and VERIFY against the two worked examples (state the check),
vs (b) what is an educated guess about the general regrouping. If the M-step regrouping for L≠ℓ is
ambiguous from the data I gave, say so and specify the minimal extra data/example you'd need. Do not invent
a formula that fails either worked example — check both before presenting.
</grounding_rules>
