## 1. VERDICT

ADMITS — structure permits the per-shell deeper-cut descent. Confidence: 99%.

## 2. Q1 (multi-j IH instantiation)

**FACT:** The IH universally quantifies over every one-shorter chain and every admissible decoration; each `redChain (t★ + j) M` has the required arity.  
**INFERENCE:** The IH may therefore be instantiated independently for every `j`; the recursion imposes no single-chain or linear-use restriction.

## 3. Q2 (outer shell subadditivity — disintegration or not)

**FACT:** Banked fact 2 gives exhaustive finite-shell subadditivity without shell measurability. Pulling the shells back along `A' ↦ prod(tailChain M) A'` remains an exhaustive cover.  
**INFERENCE:** This is ordinary domain monotonicity and finite subadditivity, not disintegration or integration over singular values.

## 4. Q3 (shared deep-tail — Tonelli product vs genuine disintegration)

**FACT:** Fact 6 identifies both parameter spaces as ordinary matrix-box products sharing `Params(M2,…)`.  
**INFERENCE:** Standard nonnegative Tonelli/Fubini after this product factorisation is enough to compare the corresponding fibres and then integrate over the shared factor. No conditional measures along fibres of the product map are needed.

## 5. Q4 (is any unbanked measure-disintegration theorem required)

No. Keep the shell restriction in the original tail parameters, use fact 2 for the cover, fact 6 plus ordinary product Tonelli, facts 3–5 for domination and threshold control, and instantiate the IH separately on each comparator. Nothing requires pushing the measure to `Z`, conditioning on `Z`, or constructing Rokhlin conditional measures.

## 6. The single most likely thing that would FLIP your verdict

The verdict would flip if the claimed per-shell domination existed only after pushing tail measure forward to `Z` and required fibrewise conditional measures, rather than an inequality established in the original product coordinates supplied by fact 6.