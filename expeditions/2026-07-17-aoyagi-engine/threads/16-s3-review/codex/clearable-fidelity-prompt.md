<task>
Adversarial FIDELITY review of a combinatorial predicate. Judge ONE equivalence and one
faithfulness question. Do NOT trust my framing; hunt a counterexample.

SETTING. `M = (M^1, ..., M^{L+1})` positive integers (widths, 1-indexed). Running min
`r_S := min(M^1, ..., M^S)` (non-increasing in S). A profile `a = (a^1, ..., a^L)` is
ADMISSIBLE (`a ∈ Adm`) iff: (i) weakly decreasing `a^1 ≥ ... ≥ a^L`, (ii) `a^L = 0`, and
(iii) per-coord bound `a^i ≤ r_{i+1}` for all i (equivalently `a^i ≤ admBound`, from which
`a^i ≤ r_{i+1}` is derived). The "running-min envelope" value at coord i is `e_i := r_{i+1}`,
which is non-increasing in i.

Define the "birth layer" `b(a) = 1 + (length of the maximal prefix of a equal to the envelope)`;
i.e. coords 1..b-1 satisfy `a^i = e_i` and coord b is the first with `a^b < e_b` (or a is the
all-envelope profile, then b = clear). `clear(a) = 1 + max{i : a^i > 0}`.

TWO PREDICATES on `a ∈ Adm`:

  PRIMARY (the informal certificate's definition):
    Clearable_prim(a) := for every layer S with b(a) < S ≤ clear(a):
        a^S < a^{S-1}  ⟹  a^{S-1} < r_S.

  SATURATION (the Lean formalisation, 0-indexed there but I restate 1-indexed):
    Clearable_sat(a) := for every adjacent pair (S-1, S) with 2 ≤ S ≤ L:
        ( a^S < a^{S-1}  AND  a^{S-1} = r_S )
        ⟹  ( for every m with 1 ≤ m ≤ S-1:  a^m = e_m ).
    [i.e.: every strict descent whose upper coord SATURATES the running min forces the
     ENTIRE prefix 1..S-1 to equal the envelope.]

QUESTIONS (answer each with PROVED / COUNTEREXAMPLE-at-<M,a> / UNSURE):

Q1. Are Clearable_prim and Clearable_sat LOGICALLY EQUIVALENT for every `a ∈ Adm`?
    Prove both directions or exhibit a concrete (M, a) where they differ. Pay special
    attention to the boundary cases: b(a) = 1 (a^1 < e_1); the all-envelope profile
    (b = clear, no post-birth descent); a profile that touches the envelope, drops, then
    touches again; ties (a^{S-1} = a^S, not a strict descent); and the exact role of the
    saturation hypothesis `a^{S-1} = r_S` versus the Adm-forced `a^{S-1} ≤ r_S`.

Q2. Is the saturation hypothesis `a^{S-1} = r_S` in Clearable_sat REDUNDANT given `a ∈ Adm`
    and `a^S < a^{S-1}`? (I claim it is NOT redundant in general — a strict descent can start
    from BELOW the running min — but that when it FAILS, Clearable_sat is vacuously true at
    that S. Confirm or refute, with a concrete instance where `a^{S-1} < r_S`.)

Q3. FAITHFULNESS: the intended meaning is "a is realizable as a t̃=0 leaf divisor of a certain
    tree recursion" (a divisor at level ≥ r_S is invisible to the layer-S clearing step, whose
    reachable levels top out at r_S − 1, and r_S is non-increasing, so it can never reach 0).
    Given ONLY that intended meaning, does Clearable_sat (equivalently Clearable_prim) look like
    the CORRECT characterization, or is there a plausible profile it would mis-classify? You do
    not have the tree code; reason from the stranding mechanism as stated.

Ground every claim. Flag inference vs proof. Be terse; lead with the verdict per question.
</task>
