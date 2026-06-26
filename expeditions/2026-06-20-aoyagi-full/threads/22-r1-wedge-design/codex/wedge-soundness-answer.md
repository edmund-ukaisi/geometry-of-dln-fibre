**Q1 Verdict:** Sound in principle, but only if the wedge is a genuine positive-measure horn with a uniform flat-coordinate bound on every slice.

Load-bearing reason: For the lower bound, no resolution chart is logically required. It is enough to exhibit measurable, essentially disjoint slices `T_s ⊂ [-ε,ε]^N` with

```text
F(x) ≤ C s^a   for all x ∈ T_s,
vol(T_s) ≳ s^b,
```

and `b - a c' ≤ -1` at `c' = minAdm(M)/2`. Then Fubini gives

```text
∫ |F|^{-c'} ≥ const · ∫_0^δ s^{b-a c'} ds = ⊤.
```

So yes, a wedge can honestly certify divergence and avoids proving a triangular Jacobian tower.

Most likely failure mode: proving only `F(γ(s)) ≤ C s^a` on the curve. That is useless for the integral unless the same upper bound persists on a positive-measure tube. Transverse directions often introduce lower-order terms in `F`, making `F` much larger on almost all nearby points. The wedge also needs measurable/disjoint slicing or a controlled parametrisation so the volume factor is real, not double-counted heuristic mass.

**Q2 Verdict:** Corank coupling helps or is neutral for the lower bound, provided the tube is chosen inside the coupled vanishing regime.

Load-bearing reason: Since the integrand is `F^{-c'}`, smaller `F` only makes the lower-bound integral larger. Extra equations/couplings can make the product vanish to higher order along the achiever, which helps pointwise.

The trap: “vanishes faster on the curve” may come with a much thinner tube. The threshold is controlled by the tradeoff

```text
volume exponent - c' · vanishing exponent.
```

If maintaining the stronger vanishing forces the tube volume to shrink too fast, the lower bound may fail. So corank does not hurt pointwise, but it can hurt the measure bookkeeping. The theorem needed is not “corank helps”; it is a uniform horn estimate with the right exponent balance.

**Q3 Verdict:** The upper bound is corank-sensitive; expect to need the full coupled chart/completeness structure, or something morally equivalent.

Load-bearing reason: Upper bounds must control all points near the fibre, not just one favourable horn. You need a covering up to null sets and estimates preventing worse-than-allowed singular behaviour on every stratum. That is exactly where corank-2 residual coupling matters: uncoupled rank-1 local factorisations can miss residual blocks like the `Δ`/`S` interaction in `(3,3,4)`.

Most likely failure mode: proving estimates on recursively chosen “nice” charts but not showing they cover the box up to null, or using a per-node rank-1 model that underestimates singularity in corank strata. Lower divergence can be certified by one well-built wedge; upper finiteness generally needs the full resolution-like atlas or an equivalent stratified integrability argument.