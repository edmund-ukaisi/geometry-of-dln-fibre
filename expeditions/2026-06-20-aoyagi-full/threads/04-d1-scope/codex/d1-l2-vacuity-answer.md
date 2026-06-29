**1. CIRCULARITY / SOUNDNESS AUDIT**

PASS, with one audit caveat.

[Fact] `hchart` is strong, but it assumes only an RLCT transfer to the post-chart function `F`; it does not state `rlctAt deepest ≤ rlctAt v` or `m/2 + rlctAtOn R ≤ rlctAt v`. [Inference] It is non-circular if later proved from raw local-diffeomorphism/bounded-Jacobian data, not from the D1 conclusion.

[Fact] `hF`, `hQ0`, `hR`, `hRne`, `hcmp` are exactly the quasi-split engine premises. They imply `hAtV` only through `rlct_quasiSplit_ge`; they do not contain `hAtV`.

[Fact] `hcoreDeepest : coreDeepest = rlctAtOn core₀ t0` is not `hCore`. [Fact] `hRform` plus the bounded-unit residual diffeo implies `rlctAtOn R (t0,g0) = rlctAtOn core₀ t0` via `hCore_slice_residual_eq`; hence `hCore` follows by equality. [Inference] This is intended geometric content, not a covert RLCT inequality assumption.

`m = nReg`: PASS if the wrapper fixes `m` definitionally as `r * (H 0 + H 2 - r)`. The low-level theorem is parametrically sound for arbitrary `m`, but a free/wrong `m` would make only a different conditional theorem. It would not prove a false unconditional result, but it could make the wrapper semantically vacuous/mislabelled unless pinned.

**2. VACUITY RISK**

[Inference] The fields are jointly satisfiable in principle for the intended nonterminal L=2 situation. The G1 form
`Φ(T,g)=((T1,(I+G(g))·T2),g)` and `R=‖T1(I+G)T2‖²` is exactly the kind of witness compatible with `hRform`.

No basepoint contradiction: `hRne` is a.e.-nonzero near the basepoint, not nonzero at the basepoint. So `R(t0,g0)=0` from `hRform`/core loss is compatible.

Concrete edge-case: if the reduced core is identically zero, then `hRform` forces `R≡0`, contradicting `hRne`. So this interface excludes terminal/direct-Morse cases; those need a separate constructor/route. For nonzero reduced DLN core, no inconsistency seen among `hRne`, `hRform`, and `hcmp`.

**3. BEST NON-VACUITY WITNESS**

Rank:

1. **(a) Best:** add `GeneralVChartL2.ofExactGerm`. Shape: assume an actual chart/germ for the real loss
   `dlnLoss ∘ chartSymm =ᶠ ∑ s_i^2 + core₀ t`, set `Q(s,t,g)=core₀ t`, `R(t,g)=core₀ t`, `Φ=id`, `C=1`, and build `hchart` by the same germ-to-RLCT-transfer pattern as `DeepestGaugeChart.ofExactGerm`. Take `hRne` as a premise or derive it from core a.e.-nonvanishing plus a finite positive gauge neighborhood.

2. **(b) Concrete tiny instance:** cheapest smoke test is degenerate `r=0`, `B=0`, `v=deepest=0`, e.g. `H=(1,1,1)`, with `m=0` and identity residual. Honest, but it does not test the positive-rank regular split. Cheapest nondegenerate positive-rank test is likely `H=(2,2,2)`, `r=1`, `B=diag(1,0)`, `v=deepest`, but proving `hchart` is basically the chart construction.

3. **(c) Documentation only:** acceptable as research bookkeeping, not as Lean non-vacuity. It explains consistency but does not meet the repo’s “show the witness” bedrock standard.