<task>
I am formalising (Lean 4 / Mathlib) a blow-up "monomialisation" construction from Aoyagi 2023 for
deep-linear-network singularities. I need a decorrelated math check on ONE identity + its required
auxiliary fact, before I grind the Lean proof. Pure combinatorics/algebra — no Lean knowledge needed.

DEFINITIONS (all over ℕ, values cast to ℤ where signed):
- Widths: M : {0,...,L} → ℕ (call M_0,...,M_L). A "layer" is an index `layer` with 0 ≤ layer < L.
- A "profile" is T : {0,...,L-1} → ℕ. Its clearing level  τ(T) := min_j T_j  ("tildeOf").
- tPrev(T)_j := (j=0 ? M_0 : T_{j-1}).
- Mval(T) := Σ_{j=0}^{L-1} (tPrev(T)_j − T_j) · (M_{j+1} − T_j)   [over ℤ].
- setTail(layer, J, T)_p := (p ≥ layer ? J : T_p)   [writes the constant J to coords p ≥ layer;
  leaves the head p < layer as T_p].

CONSTRUCTION FACTS I have available as invariants at a "case-1" step (all proven separately):
- WEAK-DECREASE: T is weakly decreasing (T_i ≥ T_j for i ≤ j) — holds for every divisor profile.
- FLAT-TAIL: for every divisor, T is CONSTANT on coords p ≥ layer (the current layer).
- Under weak-decrease + flat-tail, the min τ(T) equals the tail value, so T_p = τ(T) for all p ≥ layer.
- The case-1 step fires on a divisor f that is ELIGIBLE: τ(T_f) = J + runLen with runLen ≥ 1, where
  J = current "cleared" count (so f is "pending": τ(T_f) > J).
- resCols := M_{layer+1} − J.
- The step emits a new/updated divisor with profile T' = setTail(layer, J, T_f) and exponent
  (old exponent) + runLen·resCols, where old exponent = Mval(T_f) (the coherence invariant MvalCoh:
  divExp = Mval(divProfile) for every divisor).
- To preserve MvalCoh I must prove:  Mval(setTail(layer, J, T_f)) = Mval(T_f) + runLen · resCols.

MY DERIVATION (please verify):
Because Mval(setTail(layer,J,T)) and Mval(T) share IDENTICAL head terms (j < layer, since setTail
leaves the head and tPrev_j = T_{j-1} for j ≤ layer−1 depends only on head), the delta is only in
j ≥ layer:
  delta = [survivor of setTail at j=layer] − [Mval(T) terms at j ≥ layer].
With p := T_f(layer−1) (the coord just below the current layer; for layer=0 read p := M_0):
  - setTail term at j=layer: (p − J)(M_{layer+1} − J)   [tPrev'_layer = T'_{layer−1} = T_f(layer−1)=p;
    T'_layer = J].  Terms j>layer are 0 (T'=tPrev'=J).
  - Mval(T_f) term at j=layer: (p − τ)(M_{layer+1} − τ)  where τ = τ(T_f) = J+runLen.
    Terms j>layer are 0 (T_f=τ=tPrev on the flat tail).
  => delta = (p−J)(M_{l+1}−J) − (p−τ)(M_{l+1}−τ) = (τ−J)·(p + M_{l+1} − τ − J).
The EMITTED delta is runLen·resCols = (τ−J)(M_{l+1}−J).
These are EQUAL iff (since τ>J) p + M_{l+1} − τ − J = M_{l+1} − J, i.e. p = τ, i.e. T_f(layer−1) = τ(T_f).

So the identity holds IFF the eligible divisor satisfies T_f(layer−1) = τ(T_f) (flat also at layer−1).

MY ARGUMENT for T_f(layer−1) = τ: A pending divisor (τ > J) must have been created at a STRICTLY
EARLIER layer ℓ0 < layer. (A divisor created at the current layer has τ = J_at_creation ≤ current J,
so it is NOT pending.) At creation its tail-write set coords ≥ ℓ0 to J_at_creation = τ, and it is
never touched afterwards except a merge that only lowers τ; rollovers don't change the profile. Since
ℓ0 < layer, coord layer−1 ≥ ℓ0, so T_f(layer−1) = τ.

Since "creation layer" is NOT stored in my state, I plan to add an INVARIANT instead:
  PendingFlat:  ∀ divisor k, (J < τ(T_k)) → ∀ p ≥ layer−1, T_k(p) = τ(T_k).
maintained across transitions:
  - rollover (layer→layer+1, J→0): new (layer−1) = old layer; the OLD FlatTail (flat on ≥ old layer)
    supplies it directly.
  - case-2 / case-1(2) append (new pivot at current layer): new pivot has τ = J (not pending), vacuous;
    old divisors: profile & layer unchanged, J increases, so still pending ones keep PendingFlat.
  - case-1(1) merge: target drops to τ ≤ J (not pending after); others unchanged.
</task>

<output_contract>
1. VERDICT on the delta algebra: is delta = (τ−J)(p+M_{l+1}−τ−J), and does matching runLen·resCols
   REQUIRE exactly p = τ? (yes/no + any correction).
2. VERDICT on "pending ⟹ T_f(layer−1) = τ": correct? any edge cases (layer=0; a merge that RAISES a
   divisor; a divisor created at current layer that could be pending)?
3. VERDICT on PendingFlat as stated + its 4 maintenance cases. Flag any case that does NOT go through,
   especially the layer−1 (ℕ truncation) issue when layer=0, and whether the invariant statement
   should use `layer ≤ p+1` or a Fin-safe form instead of `p ≥ layer−1`.
4. Is there a CLEANER auxiliary fact or formulation that avoids PendingFlat entirely (e.g. proving the
   delta directly from weak-decrease + flat-tail + eligibility without a new invariant)? Rank options.
Keep each section tight. Flag inference vs certainty.
</output_contract>

<grounding_rules>
This is a self-contained math problem; reason from the definitions given. If you must assume something
about the construction not stated, flag it explicitly as an assumption.
</grounding_rules>
