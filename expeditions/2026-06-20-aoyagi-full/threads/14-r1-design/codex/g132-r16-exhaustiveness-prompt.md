<task>
Adjudicate two structural questions about a recursive resolution of singularities used in a
deep-linear-network RLCT (real log canonical threshold) computation. Be adversarial: look for the
failure mode before confirming.

SETUP.
- A "matrix-chain core" is F = ‖C_L · C_{L-1} · … · C_1‖²_F, the squared Frobenius norm of a product of
  L real matrix factors C_s of shapes M_s × M_{s+1}, evaluated as a polynomial on the entries, at the
  origin (all C_s = 0). Its zero-set {F=0} = {∏ C_s = 0} is the singular locus.
- The RLCT target is rlctAtOn(F) at the origin = sup of exponents c for which |F|^{-c} is locally
  integrable.
- The resolution is RECURSIVE (Aoyagi-style recursive blow-ups), realized as a TREE of coordinate charts:
  * At each node, blow up the rank-defect center of the "active" factor. This is an affine chart cover
    (one chart per nonzero homogeneous pivot coordinate). In each chart the pivot coordinate x is
    normalized to a HARD unit (= 1), so F = x²·(reduced core), and |det Dφ| = x^{(|center|-1)}.
  * Within each chart, a Schur-complement step decouples: F factors (up to a two-sided squeeze
    c₁·Φ ≤ F ≤ c₂·Φ, c₁,c₂>0) as Φ = (Σ regular squares) + ‖S·(reduced factor)‖², where S = Schur
    complement and the second term is again a matrix-chain core of strictly smaller total width
    ΣM' < ΣM. Recurse on it.
  * Base case: L = 1 (a single factor), where F = ‖C_1‖² is a pure sum of squares (smooth block), RLCT
    = (number of squares)/2.
- The leaves give monomial RLCT thresholds min_j (h_j+1)/(2 k_j); the whole-tree value is
  ⨅ over charts of (the leaf thresholds), the standard min-over-a-cover for RLCT.

THE TWO QUESTIONS.
(a) EXHAUSTIVENESS: does this chart TREE cover a neighbourhood of (origin ∩ {F=0}), so that
    ⨅ over the atlas EQUALS rlctAtOn(F) at the origin (the genuine RLCT), rather than merely bounding
    it from above (which a partial/incomplete chart family would give)? In particular, can the atlas
    inf UNDERSHOOT the true value (a spurious chart/divisor with ratio below the codim-minimum)?
(b) WELL-FOUNDEDNESS / TERMINATION: does the recursion terminate? Is ΣM = Σ_s M_s a sound termination
    measure (does every nonterminal node strictly decrease it)? Can a node be STUCK (still singular,
    but no resolvable pivot, so ΣM does not drop)?
</task>

<output_contract>
1. (a1) Local cover: is the per-node affine chart cover (charts = nonzero pivot coordinate) exhaustive
   of the center's complement? Is the composite TREE exhaustive of {F=0} near the origin (does every
   rank-stratum / branch get reached)?
2. (a2) No-undershoot: the danger is a divisor where F vanishes to high order (like x^k, k≥2, giving
   rlct 1/(2k) < 1/2, or (x²+y²)² giving 1/2 < 1). Does the recursion's "blow up a rank-defect center,
   F = x²·(reduced)" guarantee every exceptional divisor has vanishing-order multiplicity k_E = 1
   (regular sequence)? Or can the Schur reduced core ‖S·A2red‖² acquire a higher-multiplicity divisor?
3. (b) Termination: is ΣM strictly decreasing at every nonterminal node? Identify any STUCK-node failure
   mode (singular but Σ drop = 0). Is the L=1 / rank-0 leaf the correct base?
4. Overall: is this a complete resolution (route exists) or is there an obstruction? If a route, name
   the load-bearing facts; if an obstruction, name where it bites.
</output_contract>

<grounding_rules>
- Reason structurally / by exact algebra; do not rely on numerics for the load-bearing claims.
- A "complete resolution" means the chart images cover {F=0} near the origin AND the monomial-threshold
  min over the cover equals the RLCT (Hironaka/Watanabe theory).
- Distinguish the multiplicity (vanishing order k_E) of an exceptional divisor from the codimension of
  its center — the RLCT lower bound needs the former, not just the latter.
- Be adversarial: actively try to construct a stuck node or an undershoot divisor before concluding.
</grounding_rules>
