1. **VERDICT:** **CANONICAL-PIN** is more faithful to Aoyagi’s argument, because her invariant and \(b_i/M_{s,k}\) ledger are maintained only after normalization to the canonical diagonal frame—not across a fan of arbitrary pivot choices. **Confidence: high.**

2. **THE PAPER EVIDENCE:** From the supplied structure, it is a **fact** that:

   - Theorem 3 explicitly normalizes the regular part to the canonical top-left matrix \(\begin{psmallmatrix}E_r&0\\0&0\end{psmallmatrix}\).
   - Every fresh divisor is indexed by the canonical diagonal coordinate \(u_{S,J+1}\), including the Case 2 exponent
     \[
     M'_{S,J+1}=(M(S)-J)(M^{(S+1)}-J).
     \]
   - After each blow-up, regular \(Q,P\) transformations restore
     \[
     D_J''\longmapsto
     \begin{pmatrix}1&0\\0&D_{J+1}\end{pmatrix},
     \]
     so the next recursion again starts in the canonical frame.
   - Lemma 2 treats these regular transformations as local analytic isomorphisms with unit Jacobian.

   Thus Aoyagi’s published ledger does not genuinely carry a per-branch stored-pivot/diagonal-pivot distinction. The Lean fan is additional cover machinery. It would therefore be paper-unfaithful to enlarge Aoyagi’s invariant merely to accommodate that implementation device.

3. **THE TRANSPORT SOUNDNESS:** This is **plausible but not established by the stated paper structure**.

   If the fan-free chart is literally obtained from the canonical chart by a permutation preserving the blow-up centre, then transport is clean: the exceptional coordinate and exponent vector are permuted together, and units remain units. The monomial exponents are preserved up to relabeling—not at the original fixed coordinate names.

   The hidden difficulty is that Aoyagi’s \(Q,P\) operations may be parameter-dependent unipotent block eliminations, not the permutation exchanging two blow-up charts. Lemma 2 proves analytic/RLCT equivalence, but does not by itself prove:

   - that every fan-free chart is isomorphic to the canonical chart;
   - that the isomorphism lifts through the relevant blow-up centre;
   - that it respects earlier cleared coordinates and subsequent recursion;
   - or that the pulled-back generator has exactly the required labeled monomial exponent rather than merely the same RLCT.

   Consequently, CANONICAL-PIN is the paper-fidelity ruling, but its proposed per-chart transport needs an independent Lean lemma about blow-up-chart equivariance.

4. **THE ONE DISCRIMINATING CHECK:** Take the smallest fresh-clear state whose residual block has two eligible below-diagonal columns. Compute one blow-up using the diagonal pivot \(u_{S,J+1}\) and one using the other eligible pivot. Explicitly swap those two columns and verify that the resulting chart maps satisfy
   \[
   \mathrm{coreGen}\circ\mathrm{chart}_{\mathrm{fan}}
   =
   (\mathrm{coreGen}\circ\mathrm{chart}_{\mathrm{can}})\circ\sigma
   \]
   up to a unit, with \(\sigma\) also carrying the exceptional coordinate and all previously cleared data correctly. Failure of this identity refutes the claimed clean transport; success strongly confirms CANONICAL-PIN.