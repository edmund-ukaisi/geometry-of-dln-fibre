1. Delta algebra — YES, with one caveat

Let \(m=M_{\mathrm{layer}+1}\) and \(p=\operatorname{tPrev}(T)_{\mathrm{layer}}\), so \(p=M_0\) when \(\mathrm{layer}=0\). Then

\[
\Delta=(p-J)(m-J)-(p-\tau)(m-\tau)
      =(\tau-J)(p+m-\tau-J).
\]

Since \(\tau-J=\mathrm{runLen}>0\),

\[
\Delta-\mathrm{runLen}\,\mathrm{resCols}
=(\tau-J)(p-\tau).
\]

Thus the emitted delta agrees exactly iff

\[
p=\tau,
\qquad\text{i.e.}\qquad
\operatorname{tPrev}(T)_{\mathrm{layer}}=\tau(T).
\]

For positive layers this is \(T_{\mathrm{layer}-1}=\tau\); at layer \(0\) it is \(M_0=\tau\).

Caveat: if `resCols` uses truncated natural subtraction, this conclusion also requires \(J\le M_{\mathrm{layer}+1}\). Otherwise its cast is not the signed difference \(m-J\).

2. Pending implies predecessor-flat — conditional

This does not follow from weak decrease, flat tail, and eligibility alone. For example, at layer \(1\),

\[
T=(3,2),\quad \tau=2,\quad J=1,\quad M_2=5
\]

satisfies all three conditions, but \(T_0=3\ne2\); the actual and emitted deltas are \(5\) and \(4\).

As a reachable-state property, your claim is correct provided:

- \(J\) never decreases within a layer;
- a current-layer creation has \(\tau\le J\);
- no merge produces a new \(\tau>J\) without also establishing predecessor-flatness;
- the initial state satisfies the corresponding base case.

Merely saying that a merge “lowers \(\tau\)” is not enough for the provenance argument: lowering the tail can change \(\tau\) while leaving an earlier coordinate above the new \(\tau\). Your transition-by-transition invariant argument repairs this gap.

Edge cases:

- Layer \(0\): the needed fact is \(M_0=\tau\), not \(T_0=\tau\). Nothing stated currently supplies it.
- A merge raising \(\tau\) above \(J\) can create a pending divisor and breaks the argument unless it establishes the boundary equality. Raising while remaining \(\le J\) is harmless.
- A current-layer divisor cannot later be pending if \(J\) is nondecreasing and its creation level is \(\le J\).

3. `PendingFlat` — maintainable, but insufficient at layer 0

For positive layers it works and is stronger than necessary. Its maintenance cases go through under the transition assumptions above:

- Rollover: yes. New predecessor index is the old layer, and old `FlatTail` applies to every divisor, including divisors made newly pending by resetting \(J\) to \(0\).
- Case-2 append: yes; the new pivot is nonpending, and increasing \(J\) only shrinks the set of pending old divisors.
- Case-1(2) append: same reasoning.
- Case-1(1) merge: yes if the target’s post-merge \(\tau\le J\), other profiles are unchanged, and \(J\) does not decrease.

With natural subtraction, `layer - 1` becomes \(0\) at layer \(0\). Consequently `PendingFlat` says \(T_p=\tau\) for all profile coordinates—but still says nothing about \(M_0=\tau\). Replacing the comparison by

\[
\mathrm{layer}\le p+1
\]

is Fin-friendlier but has exactly the same layer-\(0\) limitation.

4. Cleaner formulation — ranked

1. Best: maintain only the exact boundary invariant

   \[
   J<\tau(T_k)\;\Longrightarrow\;
   \operatorname{tPrev}(T_k)_{\mathrm{layer}}=\tau(T_k).
   \]

   It is subtraction-free, Fin-safe, handles both layer branches uniformly, and its rollover proof follows immediately from old `FlatTail`. It still requires a separate layer-\(0\) base proof \(M_0=\tau\), or proof that no divisor is pending there.

2. Use a piecewise boundary invariant: \(T_{\mathrm{layer}-1}=\tau\) for positive layers, with a separate \(M_0=\tau\) clause at layer \(0\).

3. Keep `PendingFlat`; it is valid but stronger and more cumbersome than needed.

4. Derive the result directly from weak decrease + flat tail + eligibility: impossible, as the counterexample above shows. Some additional reachable-state fact is genuinely required.