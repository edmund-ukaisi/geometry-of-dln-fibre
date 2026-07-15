1. OK  
Verified rewrite chain: `toNat(cCodim d r) → toNat(cCodim (d−r) 0) → toNat(↑minAdm) → minAdm → minAdmRec`.  
The final rewrite yields `↑minAdmRec = ↑minAdmRec`; `Int.toNat_natCast` loses nothing.

2. OK  
`hN` excludes the genuinely problematic zero-matrix chain; `hr` is precisely the paper’s admissible shifted-width range.  
Both endpoints are included. A trivial extension beyond `hr` may exist, but is outside that intended range.

3. OK  
The geometric lemma already identifies the height with a finite natural coercion, excluding `⊤`.  
If `d−r` has a zero entry, induction on the recursion exhibits a zero summand, so `minAdmRec = 0`, matching whole-space codimension.

4. OK  
The theorem proves exactly the algebraically closed characteristic-zero claim, including `ℂ`.  
Named residual: transferring this codimension statement to the real parameter space. No analytic, RLCT, or half-codimension assertion appears.

5. OK  
For positive widths the zero-product locus is proper; zero-width degeneracies do not make the theorem vacuous.  
For `(2,2,2)`, the recursion gives `min {4,3,4} = 3`, hence the expected nonzero codimension.

Overall: FAITHFUL