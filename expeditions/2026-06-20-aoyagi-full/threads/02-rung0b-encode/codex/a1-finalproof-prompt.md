<task>
I am formalising in Lean 4 (Mathlib v4.29) the LAST sorry of a theorem `lambdaCore_eq_clean`.
The mathematics is fully verified numerically; I need the cleanest DECOMPOSITION/proof-architecture,
not Lean syntax. Diagnose the cleanest route for two hard sub-pieces and flag any design gap.

SETUP (all ℕ/ℤ, no analysis). Fix M : Fin (L+1) → ℕ, L ≥ 1. Let a = M sorted ascending,
S_n = a_0+...+a_n (prefix sums of sorted M). Define:
- balancedSplit P m : Fin m → ℕ := fun i => if i < P%m then P/m+1 else P/m   (the balanced m-split of P).
- Achiever c* = the LARGEST c ∈ {1,...,L} with `good c := ∀ 1≤i≤c, i·a_i ≤ S_i + i − 1`
  (equivalently a_i ≤ ⌈S_i/i⌉). c=1 is always good, so c* exists. (Verified: lambdaCore M =
  cleanCore c* (c*+1 smallest widths), 0 fails over all L≤4.)
- Target multiset Y (length L) = balancedSplit(S_{c*}, c*)  ⊕  {a_{c*+1}, ..., a_L}  (the L−c* largest).
  Note max(balancedSplit) ≤ a_{c*+1} ≤ each tail entry, so sort(Y) = sort(balancedSplit) ++ tail.

GOAL: lambdaCore M = ¼(∑Y² − ∑M²) and = cleanCore c* (sortedSmallest M c*). lambdaCore M = ½·min_{T∈Adm M} Mval(M,T).

The "edge transform" (ALREADY PROVEN in-file): for T ∈ Adm M (admissible cone: weak-decrease
t¹≥...≥tᴸ=0, bounds), with level seq u (u_0=M⁰, u_{i+1}=Tⁱ, u_L=0) and edgeQ_j = M^{j+1}+u_j−u_{j+1}
(j∈range L, an ℤ vector of length L):
  2·Mval(M,T) = ∑_{j<L} edgeQ_j² − ∑_{i<L+1} (M^i)²   [edge_identity, PROVEN]
ALSO PROVEN engines (use as given):
- sq_sum_le_of_sorted_prefix (n) (q Y : Fin n → ℤ): if ∑q=∑Y and ∀k≤n, prefix_k(srt q) ≤ prefix_k(srt Y)
  then ∑Y² ≤ ∑q². [srt = ascending sort as ℕ→ℤ padded 0; prefix_k(srt q) = sum of k smallest of q]
- smallestK_le_subset (n k) (hk:k≤n) (q:Fin n→ℤ) (A:Finset (Fin n)) (hA:A.card=k):
  prefix_k(srt q) ≤ ∑_{j∈A} q j.   [k-smallest ≤ any k-subset sum]
- balancedSplit_min, balancedSplit_sq_int (∑(balancedSplit P m)² = m·(P/m)² + (P%m)(2(P/m)+1)),
  cleanCore_perm (cleanCore depends only on the width multiset).
- QFeasible corridor facts derivable from Adm: u antitone, 0 ≤ u_i ≤ M^i, and the POSITIONAL prefix
  bound ∑_{j<n} edgeQ_j = S'_n − M⁰ + (M⁰ − u_n) where S'_n=∑_{i<n+1} M^i, giving ∑_{j<n} edgeQ ≤ S'_n
  (since u_n ≥ 0) and ≥ S'_n − u_n... [I have prefix_edgeQ telescoping identity proven.]

TWO HARD PIECES I need the cleanest architecture for:

PIECE 1 — THE LOWER BOUND (the gate, #45). Need: ∀ T∈Adm M, ∑Y² ≤ ∑_{j<L} edgeQ(M,T,j)².
Plan: feed sq_sum_le_of_sorted_prefix with q = edgeQ. Need (a) ∑edgeQ = ∑Y (both = ∑M; trivial via
telescope) and (b) ∀k≤L, prefix_k(srt edgeQ) ≤ prefix_k(srt Y). For (b) the plan splits by regime at
k vs c*:
  - k > c*: prefix_k(srt Y) = S_k (the k smallest of Y, since Y = c* balanced-split values
    averaging ≈S_{c*}/c* PLUS the tail; actually need to verify prefix_k(srt Y) = S_k for k>c*).
    And prefix_k(srt edgeQ) ≤ ∑_{first k POSITIONS} edgeQ ≤ S_k (positional corridor — but corridor
    gives ≤ S'_k = sum of first k+1 ORIGINAL M entries, NOT sorted S_k. PROBLEM: original vs sorted!).
  - k ≤ c*: prefix_k(srt Y) = prefix_k(srt balancedSplit(S_{c*},c*)); bound prefix_k(srt edgeQ) ≤ it
    via smallestK_le_subset (subset=first c* positions, card c*) + corridor (prefix_{c*} ≤ S'_{c*}) +
    STEP B (balanced maximises k-smallest).
QUESTION 1a: The corridor bounds edgeQ prefixes by ORIGINAL-order S'_n (sum of first n+1 entries of
the UNSORTED M), but Y's sorted prefixes are S_k (sorted prefix sums). For unsorted M these differ.
Does the regime argument actually go through on unsorted M, or must I FIRST reduce to sorted M
(prove lambdaCore M = lambdaCore (sort M))? [Numerically the final domination ∀k prefix_k(srt edgeQ)
≤ prefix_k(srt Y) holds 0-fail on UNSORTED M directly — but I need the right intermediate that's
provable. Is there a subset choice avoiding the original-vs-sorted mismatch?]

PIECE 2 — STEP B (balanced maximises k-smallest, verified 0/11219): for q:Fin m→ℕ with ∑q ≤ P, k≤m:
  prefix_k(srt (balancedSplit P m)) ≥ prefix_k(srt q).
Equivalently smallestK k (balancedSplit P m) ≥ smallestK k q. The avg bound m·smallestK ≤ k·∑
UNDERSHOOTS (balanced is needed exactly). Need cleanest elementary proof via the explicit form
(⌈P/m⌉ for P%m parts, ⌊P/m⌋ rest). QUESTION 2: what is the cleanest induction/argument? (e.g.
prefix_k(srt balancedSplit) = k·(P/m) + min(k, P%m) closed form, and prefix_k(srt q) ≤ that?)

PIECE 3 — THE ACHIEVER (#46). Need explicit T* ∈ Adm M with Mval(M,T*) = ½(∑Y²−∑M²), i.e. its
edgeQ multiset = Y. For UNSORTED M this is delicate (the smallest widths aren't at the front).
QUESTION 3: cleanest construction of T* on unsorted M + cleanest admissibility proof? OR is it
cleaner to prove `lambdaCore M = lambdaCore (M∘σ)` for the sorting σ first (keystone said this is
hard, no Mval-preserving bijection)? Is there a way to get the UPPER bound lambdaCore ≤ ¼(∑Y²−∑M²)
WITHOUT an explicit unsorted-M T* — e.g. is the inf'_le achievable by a T* defined via a clean
prefix-of-sorted formula that I can prove admissible directly?
</task>

<output_contract>
Three sections, one per PIECE. For each: (i) the SINGLE cleanest decomposition (named intermediate
lemmas + their statements), (ii) the key inequality/identity that makes it go, (iii) the ONE place it
could fail (the design gap to watch). For Q1a, Q3 give a definite recommendation (sorted-reduction
YES/NO, explicit-T* YES/NO). Be concrete and brief. Flag any step where my numeric claim might mask a
real design gap. End with a 1-line GO/NO-GO on whether this is pure Lean execution or has a design hole.
</output_contract>

<grounding_rules>
Distinguish what FOLLOWS from the proven engines vs what you INFER should work. If you claim an
identity (e.g. prefix_k(srt Y)=S_k for k>c*, or the closed form for prefix_k(srt balancedSplit)),
mark it as "needs check" unless it is forced. Do not invent Mathlib lemma names. The mathematics is
verified; focus on whether the ROUTE composes without a hidden gap.
</grounding_rules>
