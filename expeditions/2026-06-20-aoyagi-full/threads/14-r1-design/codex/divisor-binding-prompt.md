<task>
I am stress-testing one load-bearing step in a resolution-of-singularities RLCT (real log-canonical threshold) computation for deep linear networks (Aoyagi/Watanabe-style). I need an independent check on whether a particular "exceptional divisor" can ever BIND (dominate) the threshold in a way that breaks a per-node descent recursion.

SETUP (exact, pen-and-paper, no Lean needed):
- A "matrix chain" has a dimension vector M = (M^1, M^2, ..., M^{L+1}) of nonneg integers (widths of L layers; layer s is an M^s x M^{s+1} real matrix C^(s)).
- The loss is F = ||C^(1) C^(2) ... C^(L)||_F^2 (squared Frobenius norm of the product), resolved at the ORIGIN (zero-product locus, all C^(s) generic near 0).
- Aoyagi's candidate value for the RLCT-core at the origin is
    lambdaCore(M) = (1/2) * min over admissible T of Mval(M,T),
  where T = (t^1,...,t^L) ranges over admissible exponent vectors:
    admissibility: t^1 >= t^2 >= ... >= t^L, t^L = 0, and 0 <= t^j <= admBound(M,j) with admBound = min(M^1,M^2) for j=1 else M^{j+1},
  and the candidate value is
    Mval(M,T) = sum_{j=1..L} (t^{j-1} - t^j)(M^{j+1} - t^j),   with t^0 := M^1.
- The resolution is a tree of blow-ups of coordinate-subspace centers = nested-rank strata S(t). A blow-up of a center of CODIMENSION c produces an exceptional divisor with monomial data (k,h) = (1, c-1), contributing a per-axis "threshold ratio" (h+1)/(2k) = c/2. The S2 normal-crossing fact gives: the chart threshold = min over all exceptional axes of (h_j+1)/(2 k_j), so the global RLCT-core = (1/2) * min over admissible strata of Mval (each admissible stratum S(t) has codim = Mval(M,T)).

THE SPECIFIC CLAIM I am stress-testing (a PER-NODE descent the whole binding rides on):
"When you blow up the DEEPEST layer first (peel one layer, codim c0 = the deepest stratum's codim), the resulting exceptional divisor NEVER binds below lambdaCore(M); equivalently lambdaCore(M) = (regular shift)/2 + lambdaCore(reduced chain), and the per-node divisor c0/2 is always >= the eventual minimum."

THE RISK: the descent was numerically verified only on ~6 small nodes (e.g. M=(2,2,2): lambdaCore 3/2; M=(3,2,3): 5/2) where the first-layer exceptional divisor is NON-BINDING (its ratio is dominated by a DEEPER stratum's smaller Mval). If there is an M where the FIRST blow-up's exceptional divisor (the deepest-layer center, codim c0) has c0/2 STRICTLY LESS than min over the OTHER admissible strata, then that divisor binds and the descent value could be wrong / the principle fails.

QUESTIONS:
1. Is there a known closed form or monotonicity for min_T Mval(M,T)? In particular, is the minimizing stratum always an "interior/deep" one, never the trivial first-layer-only blow-up?
2. Can you find (by reasoning or small search) a dimension vector M (L = 1..3, widths up to ~5) where the codim of the FIRST/deepest single-layer blow-up center, c0, satisfies c0/2 < min over all OTHER admissible T of (1/2)Mval(M,T)? I.e. where the first exceptional divisor would be the UNIQUE binding one and strictly smaller than everything downstream.
3. Width-spikes (e.g. M=(1,5,1), M=(2,5,2), M=(1,1,5,1,1)), odd widths, and deep narrow chains are especially of interest — where might c0/2 dip below the rest?
</task>

<output_contract>
- State whether you find a binding-first-divisor witness (give the explicit M, c0, and the competing min) OR an argument that the first divisor is never the strict unique binder.
- Distinguish clearly FACT (computed Mval values, an exhibited M) from INFERENCE (a monotonicity claim).
- Keep Mval/admissibility arithmetic explicit; show the T that achieves the min.
</output_contract>

<grounding_rules>
- Mval is over the integers; factors can be signed. Use t^0 := M^1.
- Admissible T must satisfy ALL THREE conditions (weak decrease, last=0, block bounds).
- "codim of stratum S(t)" = Mval(M,T) for that T (this is the project's convention).
- Do not assume the answer; compute.
</grounding_rules>
