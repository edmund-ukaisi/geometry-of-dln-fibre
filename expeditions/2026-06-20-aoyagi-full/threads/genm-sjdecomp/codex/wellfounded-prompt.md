# Question: well-foundedness / termination of a recursive blow-up double induction

I am auditing the termination of a recursive resolution-of-singularities argument (a double
induction) and want an independent read on whether it is well-founded and whether any step is
under-specified. Please reason from the construction below on its own terms. Do NOT assume my
conclusion — I am withholding it.

## Setup (Aoyagi 2023, "learning efficiency of deep linear networks", proof of main theorem)

We resolve the singularities of `f = ‖∏_{s=1}^L C^{(s)}‖²` (squared Frobenius norm) at the origin,
where `C^{(s)}` is an `M^{(s)} × M^{(s+1)}` matrix of independent variables (all entries free), by a
sequence of monomial blow-ups along smooth submanifolds. The goal is a normal-crossing form
`⟨diag(b_1, …, b_{M(L+1)})⟩` where each `b_i` is a monomial in blow-up coordinates `u_{s,k}`.

Define `M(S) = min{ M^{(s)} : 1 ≤ s ≤ S }`.

### The inductive invariant at state (S, J), with 0 ≤ S and 0 ≤ J:

    ⟨∏_{s=1}^L C^{(s)}⟩ = ⟨ diag(b_1,…,b_{M(S)}) · [ E_J  O ; O  D_J ] · ∏_{s=S+1}^L C^{(s)} ⟩

where:
- `E_J` is the `J×J` identity;
- `D_J = (d_{ij})` is an `(M(S)−J) × (M^{(S+1)}−J)` matrix of fresh free variables `d_{ij}`
  (indices `J+1 ≤ i ≤ M(S)`, `J+1 ≤ j ≤ M^{(S+1)}`);
- `b_0 = 1`, `b_i = ∏_{ \tilde t_{s,k} = i−1 } u_{s,k} · b_{i−1}` for `i = 1,…,M(S)` (each `b_i` is a
  monomial in the blow-up coordinates `u_{s,k}`);
- the accumulated change-of-variables Jacobian is a monomial `∏_{s,k} u_{s,k}^{M_{s,k}−1}` (times the
  fresh `dd_{ij}`, `dc^{(s)}` of the still-free variables);
- a total-comparability invariant holds among the introduced label-vectors `T_{s,k}`:
  for all pairs, `T_{s,k} ≤ T_{s',k'}` or `T_{s,k} ≥ T_{s',k'}`.

Each `u_{s,k}` carries an integer label vector `T_{s,k} = (t^{(1)}_{s,k},…,t^{(L)}_{s,k})` and a scalar
`\tilde t_{s,k}` (a running-minimum of the label, roughly "which diagonal slot this coordinate feeds").
The base state is `S=0, J=0` (trivial: `D_0 = ∏ C^{(s)}`, `b=(1,…,1)`).

### The induction STEP at (S, J). Look at the diagonal entries starting at b_{J+1}. Two cases:

**Case 1:** there is a run `b_{J+1} = b_{J+2} = … = b_{J+J_1}` with `b_{J+J_1+1} ≠ b_{J+J_1}`
(equivalently `{ \tilde t_{s,k} = i } = ∅` for `i = J+1,…,J+J_1−1`). Fix a `u_{s,k}` with
`\tilde t_{s,k} = J+J_1`. Construct the blow-up along the submanifold
`{ d_{ij} = 0 (i = J+1,…,J+J_1, j = J+1,…,M^{(S+1)}), u_{s,k} = 0 }`. Two sub-cases:
  - **Case 1(1):** the dominant chart is one where an existing `d`-entry is divided by the existing
    `u_{s,k}` (`d_{ij} = u_{s,k} d'_{ij}`). Outcome: "the inductive statement holds with the number of
    elements in `{ u_{s',k'} : \tilde t_{s',k'} = J+J_1 }` decreased by one." (S, J unchanged.)
  - **Case 1(2):** a NEW blow-up coordinate `u_{S,J+1}` is introduced (`u_{s,k} = u_{S,J+1} u'_{s,k}`,
    and one `d`-entry becomes the pivot `= 1`). Outcome: the inductive statement with `J` increased by
    one — UNLESS `J+1 > M(S+1) = min{M(S), M^{(S+1)}}`, in which case `S` increases by one.

**Case 2:** `b_{J+1} = b_{J+2} = … = b_{M(S)}` (ALL remaining diagonal entries equal;
`{ \tilde t_{s,k} = i } = ∅` for `i = J+1,…,M(S)−1`). Construct the blow-up along
`{ d_{ij} = 0, i = J+1,…,M(S), j = J+1,…,M^{(S+1)} }` (the WHOLE residual block). Introduces a new
`u_{S,J+1}` and advances `S` by one (the residual block is fully resolved into the next `C^{(S+1)}`).

The induction terminates at `S = L+1`, where the invariant reads
`⟨∏ C^{(s)}⟩ = ⟨diag(b_1,…,b_{M(L+1)})⟩` — fully diagonal, normal-crossing.

## My questions (please answer each; reason independently; flag anything under-specified)

**Q1 (well-founded measure).** Is there a single explicit well-founded measure (or a lexicographic
tuple) on the state that strictly decreases at every step — Case 1(1), Case 1(2), Case 2? The three
outcomes move different coordinates: 1(1) decreases a *count of unresolved u's at a fixed diagonal
slot* (S,J fixed); 1(2) increases J (or S); Case 2 increases S. Since J and S INCREASE, the naive
measure is not (S,J). What decreases? Propose the measure and verify it strictly decreases on each of
the three branches. Is `S ≤ L+1` and `J ≤ M(S+1)` enough to bound the increasing coordinates?

**Q2 (Case 1(1) inner termination).** Case 1(1) keeps (S,J) fixed and only decreases the count of
`u`'s at slot `J+J_1`. What is the initial value of that count, and is it finite / bounded a priori?
Could Case 1(1) fire unboundedly (a genuine sub-recursion that might not terminate), or is it clearly
finite? Where does the bound come from?

**Q3 (case exhaustiveness + the J_1 = 1 edge).** Is the Case 1 / Case 2 dichotomy exhaustive at every
(S,J)? Case 1 needs a run that BREAKS (`b_{J+J_1+1} ≠ b_{J+J_1}`); Case 2 needs all remaining equal.
What happens when the run has length 1 (`J_1 = 1`)? When `J = M(S)` already (no residual)? Are there
states falling through both cases?

**Q4 (the comparability invariant).** The total-order property `T_{s,k} ≤ T_{s',k'} or ≥` among label
vectors is claimed maintained. Is it needed for TERMINATION, or only later for reading off the RLCT as
a min over labels? If a step could break comparability, does the recursion still terminate (just with a
worse read-off), or does the whole construction stall?

**Q5 (under-specified steps).** Which step, if any, is stated too tersely to reconstruct rigorously?
In particular: (a) in Case 1, the choice of which `u_{s,k}` to fix (existence + the effect of the
choice on the invariant); (b) the claim that after Case 2 the residual block "becomes the next
`C^{(S+1)}`" of the right dimensions `M^{(S+1)} × M^{(S+2)}`; (c) whether the Jacobian-monomial and the
`b_i`-monomial forms are automatically preserved by each blow-up chart or require a separate check.

**Q6 (a known Case-2 print discrepancy).** The Case-2 divisor exponent is printed as a residual-block
codimension in ACTUAL widths `(M(S)−J)(M^{(S+1)}−J)`, but a faithful running-minimum ("prefix-min")
form would read `(μ_S − J)(M^{(S+1)} − J)` where `μ_S` is a running minimum that can be `< M(S)` on
chains where widths are not monotone. Does this discrepancy affect (i) termination, (ii) the final
normal-crossing structure, or (iii) only the numeric exponent value / the RLCT read-off? Under what
width patterns do the two forms diverge?

Please be concrete and adversarial. If a measure works, give it explicitly; if a step is genuinely
under-determined, say so and say what extra data closes it.
