**Q1. Route**

Yes, route (a) proves it, with the realizability caveat from FACT 4.

Logical chain:

1. **FACT:** `T*` is an admissible achiever, so by definition/attainment  
   `minAdm(M) = Mval(M,T*)`.

2. **FACT 1:** for every admissible `T`,  
   `Mval(M,T) = multSum(diff(r(M,T)))`.  
   Therefore, evaluating at `T*`,  
   `minAdm(M) = multSum(diff(r(M,T*)))`.

3. **FACT 4:** if `diff(r(M,T*)) ≥ 0`, equivalently the candidate is realizable/Kostant, then  
   `multSum(diff(r(M,T*)))` has the geometric meaning `codim Ō_{diff(r(M,T*))}`.

4. **Therefore, INFERENCE:** on the realizable/width-monotone scope,  
   `minAdm(M) = geometric codim of the achiever orbit`.

5. **FACT 2 plus definition:**  
   `lambdaCore(M) = 1/2 · minAdm(M)` and  
   `lambdaCore(M) = cleanCore(c*, sortedSmallest M c*)`,  
   hence by exact rational arithmetic,  
   `minAdm(M) = 2 · cleanCore(c*, sortedSmallest M c*)`.

So yes: #136 can route through A1’s existing closed-form tie. No fresh quadruple-sum-equals-single-sum proof is logically required for the target `minAdm = geometric codim`.

**Q2. multSum vs cleanCore**

They are not given as a direct per-stratum identity.

- **FACT 1:** per-stratum identity is  
  `multSum(diff(r(M,T))) = Mval(M,T)`.

- **FACT 2/3:** closed-form identity is about the optimum value:  
  `minAdm(M) = 2 · cleanCore(c*, sortedSmallest M c*)` for the genuine achiever’s `c*`.

So the equality

`multSum(diff(r(M,T*))) = 2 · cleanCore(c*, sortedSmallest M c*)`

is an **INFERENCE at the minimizer**, via

`multSum(T*) = Mval(T*) = minAdm = 2·cleanCore`.

It is a value-coincidence at the achiever, not a direct reduction of the quadruple sum to the single-sum formula for arbitrary strata.

**Q3. Cheapest Lean route**

Ranking:

1. **Cheapest:** `(a)` compose FACT 1 + FACT 2 at an attaining `T*`.  
   FACT 1 is a ring/per-stratum identity; FACT 2 is already a green theorem. This avoids proving a new closed-form reconciliation.

2. **More expensive:** `(b)` prove `multSum = cleanCore` directly.  
   This would require a fresh quadruple-sum to balanced-square single-sum reduction, and from Q2 it would need to be stated carefully because the cleanCore formula is only tied to the genuine achiever, not a naive minimization over `c`.

3. **Other:** only needed if the target also requires constructing/proving realizability of the achiever orbit. That is separate from the value identity and governed by FACT 4.

**Q4. Obstruction**

No obstruction from not knowing `T*` explicitly.

You only need:

- existence of an admissible achiever `T*`;
- `Mval(M,T*) = minAdm(M)`;
- FACT 1 for all admissible `T`;
- realizability `diff(r(M,T*)) ≥ 0` if you want the word “geometric codim”.

Then instantiate the universal identity at `T*`.

So the Lean proof does not need an explicit formula for `T*`. It can use an existential witness/argmin package:

`∃ T*, admissible T* ∧ Mval M T* = minAdm M`

and then specialize FACT 1 to that `T*`.