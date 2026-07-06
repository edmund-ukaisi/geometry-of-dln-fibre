Line references below are from `pdftotext -layout ... | nl -ba` on the local PDF.

**1. Argument Structure**
- [FACT-from-source] **(a)** After normalizing the target product to `diag(E_r,0)` (lines 961-974), Lemma 2 gives an explicit block elimination for one matrix with a regular `r×r` corner (lines 861-883, 900-958). Theorem 3 iterates that through the product and produces
  `P1 (∏_s A^(s)) P2 = diag(C1, ∏_s C^(s))`
  with `P1,P2` regular (Theorem 3, lines 982-999; proof, 1012-1223). Section 5 then writes the transformed difference matrix and concludes
  `λ = [-r^2 + r(H^(1)+H^(L+1))]/2 + λ⟨∏_s C^(s)⟩`
  (lines 1226-1267).
- [INFERENCE] The additive first term is exactly the RLCT of the regular/transverse coordinates `(C1-E_r, F2, F3)`, i.e. the smooth block peeled off by Theorem 3.

- [FACT-from-source] **(b)** Theorem 4 is a homogeneity comparison: for homogeneous `F_i`, the RLCT at the point with the homogeneous coordinates set to `0` is `≤` the RLCT at an arbitrary nearby point (lines 1282-1297). The next sentence applies it immediately: “By Theorem 4, we can set `r(s)=r` for `s=1,…,L`, without loss of generality” (lines 1307-1308).
- [INFERENCE] Yes: this is the reduction to the deepest singular point of the reduced problem, i.e. to the origin in the `C^(s)`-coordinates.

- [FACT-from-source] **(c)** Yes. Section 5 explicitly says it uses a “recursive blow-up process” along submanifolds (lines 1321-1333). The inductive statement specifies the chart data `b_i, D_J, u_{s,k}, t_{s,k}, M_{s,k}` and the Jacobian factor (lines 1382-1454). Case 1 blows up along `{d_ij=0, u_{s,k}=0}` (lines 1496-1503); Case 2 along `{d_ij=0}` (lines 1999-2005). The subcases then give explicit coordinate substitutions and explicit regular matrices `Q,P` (lines 1527-1580, 1601-1900, 2033-2295). The induction ends with
  `⟨∏_s C^(s)⟩ = ⟨diag(b1,…,b_{M^(L+1)})⟩`
  (lines 2334-2339).
- [INFERENCE] That is an explicit monomialization / normal-crossing form of the reduced ideal.

**2. Does The Lower Bound Come Directly From The Monomial Exponents?**
- [FACT-from-source] After termination, Section 5 says the “candidates” for the log canonical threshold on a chart are read off from the exponents `M_{s,k}` (lines 2342-2360). Lemma 3 is then an arithmetic minimization of those candidates (lines 2596-2631), and the paper immediately derives the closed formula for `2 λ_O(||∏_s C^(s)||^2)` from Lemma 3 (lines 2637-2667).
- [INFERENCE] Yes. For the reduced deepest-point problem, the RLCT is extracted directly from the monomial/Jacobian exponents, i.e. exactly the kind of `min_j (h_j+1)/(2k_j)` step your `S2 = monomial_rlct` supplies.
- [INFERENCE] For the full DLN statement, the only extra ingredients are Theorem 3’s exact additive splitting and Theorem 4’s reduction to the deepest point.

**3. Any Hidden Need For Non-Constructive Resolution / Morse-Bott / IFT-With-Parameters?**
- [FACT-from-source] No such step appears in Section 5. What Section 5 explicitly uses is: Lemma 2 / Theorem 3 (linear-algebra block reduction, lines 861-883, 982-1223), Theorem 4 (homogeneity comparison, lines 1282-1308), and explicit blow-ups along named submanifolds (lines 1496-1503, 1999-2005) leading to a diagonal monomial ideal (lines 2334-2339).
- [FACT-from-source] The Hironaka citation is earlier, in Section 2 (lines 437-480), not in Section 5.
- [INFERENCE] The only external analytic ingredient inside Section 5 is Theorem 4. That is not a general resolution theorem or a Morse-Bott/constant-rank splitting theorem; it is a separate homogeneity comparison lemma.

**4. Formalization Sizing**
- [INFERENCE] Closer to **A**, not **B**.
- [FACT-from-source] The substantive content Section 5 actually builds is explicit: the recursive blow-up induction, explicit Jacobian bookkeeping, and the arithmetic minimization via Lemma 3 (lines 1321-1454, 1496-2339, 2596-2667).
- [INFERENCE] Residual pieces, under your assumptions, are:
  - the explicit blow-up combinatorics / induction on `(S,J)` and the ordered vectors `T_{s,k}`;
  - Jacobian bookkeeping producing the exponents `M_{s,k}-1`;
  - the terminal monomialization `⟨∏ C^(s)⟩ = ⟨diag(b_i)⟩`;
  - Lemma 3’s minimization;
  - plus, if not already available, Theorem 4 or an equivalent homogeneity-comparison lemma.
- [INFERENCE] That last item is the only extra analytic lemma beyond `S2 + linear algebra`; it is not a hidden existence theorem.

**VERDICT**
- [INFERENCE] The DLN RLCT lower-bound proof in Section 5 is a **bounded explicit-blow-up build**, not a hidden appeal to general Hironaka/Morse-Bott/constant-rank machinery.
- [FACT-from-source] It proceeds by explicit block reduction (Lemma 2 + Theorem 3), explicit deepest-point reduction via Theorem 4, and explicit recursive blow-ups to a monomial ideal, followed by arithmetic minimization (lines 982-1267, 1282-1308, 1321-1454, 1496-2339, 2596-2667).
- [INFERENCE] So: **not literally only `S2 + elementary linear algebra`**, because Section 5 does use Theorem 4. But there is **no wall** from missing general resolution or Morse-Bott/IFT infrastructure. The residual build is the blow-up combinatorics + Jacobian bookkeeping + Lemma 3 arithmetic, with at most one additional homogeneity-comparison lemma.