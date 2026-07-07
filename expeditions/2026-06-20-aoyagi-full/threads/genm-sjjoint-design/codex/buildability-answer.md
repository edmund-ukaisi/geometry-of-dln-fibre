**Q1 Verdict: B**

R-ATOM’s outer brick is not reducible to the listed banked pieces. The elementary parts are buildable: Cauchy-Binet, `det (Q_b Q_bᵀ) = ‖∧^q Q_b‖²`, exterior-power bookkeeping, bounded-unit estimates, and monomial endpoint integrals.

The missing step is the decisive one: principalising the maximal-minor/Gram ideal of a **matrix product** together with the shared “core” ideal. At corank ≥ 2, the issue is not just that `det(Q_b Q_bᵀ)` vanishes; it is that one must know which exceptional coordinates are shared by which generators. That sharing changes the RLCT/integrability exponent, as in your example where superficially similar widths give different values. A pivot chart, LDL, sqrt, spectral theorem, or singular-value list does not give coordinates valid on the rank-drop locus, and Mathlib has no determinantal-resolution or multi-ideal principalisation machinery.

So: Cauchy-Binet is an elementary missing lemma; the outer R-ATOM brick is a resolution-of-singularities/determinantal-variety problem in disguise.

**Q2**

Yes, R-BLOWUP avoids the Gram-determinant principalisation. The hard object `det(Q_b Q_bᵀ)^{-p/2}` never forms, because the corank block is not integrated out against a degenerating `Q_b`.

R-BLOWUP looks buildable from the stated banked pieces. The corank ≥ 2 mechanism is sequential: each pivot blow-up introduces one radial variable `u` for the whole current corank block, charges that radial variable by the full block codimension, normalises the top-left/pivot part, then recurses on the reduced block and downstream product. After several pivots, the shared support is not something to discover by resolving a Gram ideal; it is explicitly recorded as products of the introduced radial variables `b_i = ∏ u_j`.

So the distinction is:

- R-ATOM asks Lean to prove that a singular ideal secretly has normal crossings.
- R-BLOWUP constructs the normal-crossing coordinates inductively.

The general-L step is still serious, but it is chart algebra: finite chart cover, coordinate maps, Jacobian powers, recursive loss identity, bounded units, and exponent inequalities. That is large formalisation work, not general RoS.

**Q3**

Recommended route: **R-BLOWUP**.

The single hardest sub-brick is the **general `(L,S,J)` single-radial blow-up chart lemma**: construct the recursive charts, prove the transformed loss has the reduced-chain form with explicit monomial radial factors, and compute the Jacobian/exponent bookkeeping uniformly. Once that is banked, the radial estimates and final monomial endpoint are within the existing runway.