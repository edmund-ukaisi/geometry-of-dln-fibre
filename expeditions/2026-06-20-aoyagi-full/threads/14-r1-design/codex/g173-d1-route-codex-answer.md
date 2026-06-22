
3. **Cleanest L2-at-general-v statement**

Do **not** state it as “maximal `n_v/2` plus the same core.” That is the fragile version.

The clean version is:

```text
For every v ∈ optimalSet, after choosing an r-dimensional transmitted chain through v
and local block coordinates, the germ of

  ‖C_1 ... C_L - B‖²

at v is RLCT-equivalent to

  ‖Z‖² + ‖D_1 ... D_L‖²,

where Z is a regular block of constant dimension

  N_active = H_1 H_{L+1} - (H_1-r)(H_{L+1}-r),

and the D_s are the induced maps on quotient dimensions H_s-r.
The base point D(v) lies in the zero fibre of the homogeneous core:

  D_1 ... D_L = 0.
```

Then

```text
rlctAt(loss, v)
  = N_active/2 + rlctAt(F0_{H-r}, D(v)).
```

At the deepest point, `D(v)=0`, so

```text
rlctAt(loss, deepest)
  = N_active/2 + rlctAt(F0_{H-r}, 0).
```

Now core-P1 applies directly:

```text
rlctAt(F0_{H-r}, 0) ≤ rlctAt(F0_{H-r}, D(v)).
```

Therefore

```text
rlctAt(loss, deepest) ≤ rlctAt(loss, v).
```

This also handles `r=0`: then `N_active = 0`, and the statement reduces exactly to core-P1.

4. **Why deepest is minimal RLCT**

Mechanism:

```text
deepest = minimal layer ranks = fewest linear residual directions
        = origin of the remaining homogeneous zero-target core
        = worst point of that core by core-P1.
```

At a non-rank-exact minimiser, extra rank creates extra first-order residual equations inside the core. Those are regular Morse directions and make the singularity milder, or leave it tied in special cases like your `(2,2,2)` example.

So yes: deepest is minimal because it has the fewest regular directions **after the constant rank-r active part is peeled off**, and the remaining core is evaluated at its origin.

5. **Most likely flaw in R-chart**

The dangerous mistake is using the **maximal** Morse split at every `v` and assuming:

```text
rlctAt(loss, v) = n_v/2 + rlctAt(same core, v_core)
```

with `n_v` constant.

That is false. `n_v` jumps, and after maximal splitting the residual core is stratum-dependent, sometimes trivial. The safe bridge is the constant active-block split plus core-P1 on the unsplit homogeneous core. Only after that may you optionally describe extra Morse directions inside the core stratum-by-stratum.
