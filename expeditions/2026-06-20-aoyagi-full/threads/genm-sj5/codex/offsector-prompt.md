<task>
Audit the RIGOR of a proposed cover-and-recursion argument for finiteness of an integral over a
neighbourhood of a rank-drop locus. The worry: naively "deleting the measure-zero rank-drop locus" is
illegitimate (its shrinking neighbourhoods can carry an infinite integral). I want your independent
check that the proposed cover genuinely controls the neighbourhood. Reasoning only.

## Setup
`Z = A₂·A₃···A_L` is a product of matrices (`M₁×M_L`), a smooth function of parameters. We must show
`∫_{{σ_min(Z) < ε}} H(param)^{−c'} dλ < ∞` for `c' < ½·minAdm(M)`, where `H` is a coupled-corner loss
that DEGENERATES as `Z` loses rank (a "unit" in `H` vanishes on the rank-drop). The value `minAdm(M)`
is a fixed positive integer (a codimension). The proposed argument:

1. COVER `{σ_min(Z) < ε}` by the finitely many corank strata `S_q = {corank(Z) = q}`, `q = 1,…,r`
   (`r` = full rank). Each `S_q` is locally closed (a minor-ideal / rank locus).
2. On the GENERIC part of `S_q` — where the `q` collapsing singular values vanish to FIRST order
   (`σ²  ≍ dist²`, "m=1") — introduce adapted tube coordinates: the `q` ordered collapsing singular
   values `s_1 ≥ … ≥ s_q ∈ (0,κ)`, with the pushforward joint density `dμ ≍ ∏_j s_j^{(D_j−D_{j−1})−1}`
   (`D_j = codim{rank ≤ r−j}`, the geometric tube codims). The loss majorant is `H ≳ ∏_j s_j^{α_j}`.
   The nested-simplex integral `∫_{0<s_q<…<s_1<κ} (∏ s_j^{α_j})^{−c'} dμ` is finite at threshold
   `½(M₀·ρ + min(M₀·q, D_q))` (`ρ = r−q`), and `min_q` of these `= ½·minAdm(M)` (a known identity).
3. The DEEPER-corank sublocus `{corank(Z) ≥ q+1}` inside `S_q`'s closure (where `m` may exceed 1, or
   the structure degenerates further) is handled by RECURSING to the next stratum `S_{q+1}, S_{q+2},…`.
4. Termination: `corank` strictly increases along the recursion and is bounded by `r`, so finitely
   many levels; each level's threshold `≥ ½·minAdm(M)`.

<questions>
State FACT vs JUDGEMENT. Be a skeptic — hunt for where "neighbourhood not controlled" could hide.
1. Does the finite union `⊔_q S_q` plus the per-stratum tube neighbourhoods GENUINELY cover a full
   neighbourhood `{σ_min(Z) < ε}` (positive measure), or can points escape all the adapted tubes
   (e.g. near the seams `s_{ρ+1} → κ`, or where several singular values are comparable and the
   ordering `s_1 ≥ … ≥ s_q` degenerates)? What must be checked so no positive-measure subset is left
   uncovered / silently deleted?
2. The generic-stratum estimate assumes `m = 1` (first-order vanishing). At the deeper sublocus
   `{corank ≥ q+1}`, could a genuine `m > 1` (higher-order vanishing) direction make the SAME
   stratum's tube integral diverge BEFORE the recursion catches it — i.e. is the split "generic `S_q`
   (m=1) + recurse on `{corank≥q+1}`" clean, or can a higher-order locus sit inside the generic
   stratum's tube and be missed? How should the tube be defined so the `m>1` mass is provably inside
   the recursed sublocus, not the current tube?
3. Given finitely many strata each with a finite tube integral `≥ ½minAdm`, does the TOTAL integral
   over `{σ_min(Z)<ε}` follow (subadditivity over a finite measurable cover), or is there a
   double-counting / overlap subtlety at the stratum boundaries that could break the bound? Is the
   recursion's well-foundedness (corank ↑, bounded by `r`) sufficient for a finite total, and does
   each recursion level genuinely reduce to the SAME kind of integral (so the induction closes)?
</questions>
</task>

<output_contract>
Three numbered answers, 4-7 sentences each, FACT/JUDGEMENT tagged. End with a one-line
"COVER-AIRTIGHT:" verdict (airtight | needs-condition-X | gap-at-Y) naming the single most important
thing that must be checked to make the neighbourhood control rigorous.
</output_contract>

<grounding_rules>
Ground in the setup. Facts permitted: a rank locus is closed and its complement's rank strata are
locally closed; the coarea/pushforward density of the singular-value map on the generic (reduced,
m=1) stratum has the stated codim powers; `∫₀^κ s^{p} ds < ∞ ⟺ p > −1`. Do not assume the cover
works — find what makes it work or where it fails.
</grounding_rules>
