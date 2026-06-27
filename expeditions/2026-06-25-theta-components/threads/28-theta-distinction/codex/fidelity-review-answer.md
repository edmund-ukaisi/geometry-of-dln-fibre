**Q1**

Verified for `(2,2,2,2,2), r=0`: for constant width, `qipM = 4`, `S = 10`, nearest round is `3`, so signed `δ = 10 - 4*3 = -2`, hence `|δ| = 2`. Aoyagi ceiling `M = ceil(10/4)=3`, residue `a = 10 - (3-1)*4 = 2`. Thus `min(a, ell-a)=min(2,2)=2=|δ|`.

For `a ≤ ell`, `min a (ell-a) ≤ 1` iff `a ≤ 1` or `ell-a ≤ 1`, i.e. `a ∈ {0,1,ell-1,ell}` with small-`ell` duplicates. In the constant-width/residue setup, `min(a,m-a)=|δ|`, so this is faithful. Caveat: this bridge uses `ell=m` and `a` being the residue modulo the same `m`; the pure Lean iff does not itself prove that network-data bridge in general.

**Q2**

Verified small cases:

`ell=4`: `choose = [1,4,6,4,1]`, `a(ell-a)+1 = [1,4,5,4,1]`; only `a=2` fails, with `min=2`.

`ell=5`: `choose = [1,5,10,10,5,1]`, `theta = [1,5,7,7,5,1]`; failures `a=2,3`.

`ell=6`: `choose = [1,6,15,20,15,6,1]`, `theta = [1,6,9,10,9,6,1]`; failures `a=2,3,4`.

Forward direction is true. If `b=a ≥ 2` and `c=ell-a ≥ 2`, then
`choose ell a = 1 + bc + choose b 2 * choose c 2 + ... > bc + 1 = a(ell-a)+1`.
No counterexample.

**Q3**

Names alone do not fully enforce the distinction: both values are `ℕ`, and `aoyagiTheta` still contains the overloaded word `theta`. The name gives provenance, not semantics. The clearer enforcement is from `numTop`/`cTheta` for component count, docstrings saying `aoyagiTheta` is pole order, and mismatch theorems. A safer primary name would be `aoyagiPoleOrder` or `aoyagiThetaOrder`.

**VERDICT**

With caveat: mathematically faithful for the constant-width distinction and the pure binomial iff; I could not verify the named capstone module itself because `ThetaOrderDistinction.lean` is absent in this checkout.