# Statement card — `hdiv_achiever` (achiever-path box-integral divergence)

Thread `21-hdiv-achiever` (formalisation tide). Module:
`lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean`. Base commit `7482066c` (branch
`fm-r1-hdiv-achiever`, off `expedition/aoyagi-full`; uncommitted — controller integrates).

---

## The wiring (sorry-free)

> **Claim.** For the layer atlas of `M` (non-degenerate `1 ≤ minAdm M`), the cover's existential
> threshold premise `(∃ leaf i, monomialThreshold(i) ≤ c')` is equivalent to `½·minAdm M ≤ c'`, and
> the achiever-only box divergence discharges the `routeMLayerCover_of_atoms` `hdiv` field.
>
> - **Lean:** `DLNFibre.DLN.RLCT.layerCover_exists_thresholdLe_iff_half_le`,
>   `DLNFibre.DLN.RLCT.layerCover_thresholdGe_half_minAdm`,
>   `DLNFibre.DLN.RLCT.layerCover_hdiv`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean` @ `7482066c`)
> - **Gloss.** Every layer leaf's monomial RLCT threshold is `≥ ½·minAdm M`, and the achiever leaf
>   attains `= ½·minAdm M`; hence "some leaf is below `c'`" iff "`½·minAdm M ≤ c'`". So the divergence
>   need only be established on the single minimum-threshold (achiever) leaf to discharge the cover's
>   `hdiv` field (which is `∃`-quantified over leaves). `layerCover_hdiv M hpos` plugs directly into
>   `routeMLayerCover_of_atoms M hfin _` (type-checked: no adaptation).
> - **Proved.** The minimality (`threshold_ge`), the achiever realiser (`achiever`), the
>   premise-reduction iff, and the `hdiv`-field discharge from the analytic atom — all sorry-free.
> - **Assumed.** `1 ≤ minAdm M` (non-degeneracy; the value lane's standing hypothesis).
> - **Cited.** `monomial_rlct` (S2 normal-crossing monomial RLCT), flowing in via the value lane's
>   `IsResolutionAtlas` (`routeLayerAtlas_isResolutionAtlas`). The single authorized citation.
> - **Deferred.** none (this is the wiring; the analytic content is the separate atom below).
> - **Status.** sorry-free.

## The analytic atom (the ONE honest `sorry`)

> **Claim.** For `c'` with `½·minAdm M ≤ (c':ℝ≥0∞)` and `ε > 0`,
> `∫⁻ x in cubeBox (routeMAmbient M) ε, ENNReal.ofReal (|routeMCore M x| ^ (-(c':ℝ))) = ⊤`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMCore_box_diverges_achiever`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean` @ `7482066c`)
> - **Gloss.** In the flat ambient coordinates, the threshold density `|routeMCore M|^{−c'}` of the
>   DLN square-Frobenius loss (at the deepest/all-zero point) is non-integrable over every cube
>   `[−ε,ε]^N` once `c'` reaches the achiever threshold `½·minAdm M`. This yields the lower bound
>   `rlctAtOn (routeMCore M) 0 ≤ ½·minAdm M`.
> - **Proved.** nothing — `sorry`. The STATEMENT is at full fidelity (correct, non-degenerate).
> - **Assumed.** `1 ≤ minAdm M`.
> - **Cited.** none in the atom statement itself (the atom carries only `sorryAx`; `monomial_rlct`
>   does not appear in its axiom set).
> - **Deferred (the precise sub-blocker).** The general-`M` achiever **geometric chart / wedge**: a
>   map `φ : box → flat` with a measure change-of-variables and a pullback UPPER bound
>   `|routeMCore M ∘ φ| ≤ C · (achiever monomial)` on a positive-measure box (so the sharp monomial
>   divergence `monomialIntegrand_lintegral_box_eq_top` transcribes to `F`). The banked squeeze
>   (`rlctAtOn_squeeze`, `schur_recursion_step_squeeze`) gives only the POINT-RLCT upper bound
>   `rlctAtOn (routeMCore M) 0 ≤ ½·minAdm M`, which is STRICTLY WEAKER than this boundary
>   box-divergence (an `sSup` bound constrains only `c' > t`; the boundary `c' = t` is sharp). The
>   `(2,2,2)` chart `phiUnit` is a depth-2 miracle that does not generalise; the layer atlas is purely
>   combinatorial (no chart map).
> - **Status.** honest `sorry` (correct statement). Axioms: `[propext, sorryAx, Classical.choice,
>   Quot.sound]`.

---

## Adjudication note (does achiever-only suffice?)

YES — verified at the Lean level. `routeMLayerCover_of_atoms`'s `hdiv` field (and the banked
`routeM_coverGeDiv_of_boxDiverges` it rides) takes the premise `(∃ leaf i, threshold(i) ≤ c')` — an
EXISTENTIAL over leaves. Because the achiever leaf attains the minimum threshold, any leaf below `c'`
forces `½·minAdm M ≤ c'`, and the achiever is the one leaf whose divergence we need. So divergence on
the single achiever leaf discharges the whole field. The banked discharge does NOT require divergence
on more than the achiever leaf — confirming the cert's claim; the atom is unchanged.

## Decorrelated consult

`local-codex-consult` (gpt-5.5, xhigh, 2026-06-24; prompt+answer under
`threads/21-hdiv-achiever/codex/`). Independently reached: (Q1) `rlctAtOn ≤ t` does NOT imply the
boundary box-divergence (sSup logic); (Q2) the atom REQUIRES a geometric chart / wedge — the squeeze
equates only point RLCTs; (Q4) the exact soundness trap is asserting `=⊤` from the point bound. No
rubber stamp — Codex constructed the boundary/sSup argument and the `|F∘φ| ≤ C·monomial` direction
unprompted.
