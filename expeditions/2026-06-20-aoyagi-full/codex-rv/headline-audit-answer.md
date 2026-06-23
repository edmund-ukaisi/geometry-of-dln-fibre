**Q1 NON-CIRCULARITY**

OBSERVED-FROM-CODE: `aoyagiLambda` depends only on rational arithmetic, `lambdaCore`, `Adm`, `admPred`, `admBound`, `Mval`, and `tPrev`.  
OBSERVED-FROM-CODE: `lambdaCore` is a finite `inf'` over `(Fin L → ℕ)` candidates filtered by admissibility, with objective `Mval : ℤ`.  
OBSERVED-FROM-CODE: no pasted dependency path mentions `rlctAt`, `dlnLoss`, `optimalSet`, or the headline theorem.  
INFERENCE: assuming the stated import boundary is accurate, this is a genuine combinatorial closed form, not circularly defined from the RLCT result.  
Verdict: non-circular.

**Q2 INFIMUM-KEYING**

OBSERVED-FROM-CODE: the headline uses `⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w`, so it is an infimum over all fibre points, not a single-point local quantity.  
OBSERVED-FROM-CODE: `optimalSet H B` is exactly `{ A | prod H A = B }`, while `dlnLoss` is the sum of squared entries of `prod H A - B`.  
INFERENCE: over real matrices, the zero set of `dlnLoss H B` should coincide with `optimalSet H B`.  
INFERENCE: given the paper convention `rlct_x = ∞` off the zero set, restricting the global infimum to `optimalSet` is faithful to `inf_x rlct_x(F)`.  
Verdict: the headline is keyed as the global learning coefficient over the fibre, not weakened to one point.

**Q3 ANY SMUGGLED WEAKNESS**

OBSERVED-FROM-CODE, high severity: `ENNReal.ofReal (aoyagiLambda H r)` would clamp any negative rational value to `0`; if the combinatorial formula were accidentally negative, the statement could hide that sign error.  
OBSERVED-FROM-CODE, medium severity: `⨅ w ∈ optimalSet H B, ...` becomes `⊤` if `optimalSet H B` is empty; nonemptiness is not a hypothesis, so the proof must derive factorisation from `B.rank = r`, `hr`, and `hL`.  
OBSERVED-FROM-CODE, low severity: `H s - r` is Nat subtraction, but in the theorem `hr : ∀ s, r ≤ H s` prevents truncation; boundary cases with reduced width `0` are intentional-looking and not automatically invalid.  
OBSERVED-FROM-CODE, low severity: `inf'` relies on `Adm_nonempty M`, whose proof is not pasted, so I cannot audit whether it is constructive/ordinary or an axiom.  
INFERENCE: the largest remaining unaudited risk is arithmetic fidelity of `admPred`/`Mval`/`lambdaCore` to Aoyagi’s codimension formula, not circularity or infimum-keying.