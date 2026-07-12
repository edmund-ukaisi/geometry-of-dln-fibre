1. **FACT:** With fixed \(Z\), \(\Gamma\mapsto\Gamma Z\) is linear, while \((B,C)\mapsto BC\) is bilinear in two independently varying factors. **FACT:** `genuineCarrier` retains both factors’ parameter spaces, whereas the clause exposes only one free block and no remainder carrying the other factor. **JUDGEMENT:** Thus the clause is unsatisfiable at an intermediate arity, except in degenerate cases where a factor is fixed.

2. **FACT:** At arity one, the product is the single free matrix \(A_0\). Taking \(\Gamma=A_0\), \(Z=I\), and \(Dt=n\) gives \(\Gamma Z=A_0\), with \(ZZ^{\mathsf T}=I\). **JUDGEMENT:** Subject to the stated indexing, domain, and dimension bounds, the clause is satisfiable at the base.

3. **FACT:** A downward induction must establish the invariant at every intermediate arity, not merely at its endpoint. **JUDGEMENT:** A clause false at intermediate levels cannot be preserved by the inductive step, even if it becomes true at the base. The minimal generalization is \(D.Z\simeq \Gamma\times R\) with residuals \(\Gamma\,Z(r)\), where \(r\in R\) contains the remaining matrices and \(Z(r)\) is their product; at the base \(R\) is trivial and \(Z=I\).

CLAUSE-AT-INTERMEDIATE: unsatisfiable — two freely varying factors cannot be represented by one free block times one fixed matrix.

FIX: Split \(D.Z\) as free block × remainder and allow \(Z\) to depend on the remainder.