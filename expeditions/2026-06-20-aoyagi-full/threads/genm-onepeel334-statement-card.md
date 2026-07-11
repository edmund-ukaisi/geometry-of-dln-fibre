# Statement card — `(3,3,3,4)` `t=1` ONE-PEEL finiteness (genm-onepeel334)

Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJOnePeel334.lean` (349 LoC).
Base commit `d517b162` (`expedition/aoyagi-full`, = `4f596c28` corner334 + the UPDATE-880 docs commit);
file delivered uncommitted for the controller to bank. NOT wired into the aggregator / `AxCheck`.
Axioms: clean three `[propext, Classical.choice, Quot.sound]` on every headline (forced `#print axioms`,
olean deleted first — no stale mask). Zero `sorry`/`axiom`/`native_decide`/`#exit`. Builds in isolation;
coexists with the full `DLNFibre` aggregator (no sibling name clash — verified by dual-import elaboration).
Design spec: `expeditions/2026-06-20-aoyagi-full/threads/genm-vsastruct/onepeel-tonelli-cert.md`.

---

> **Claim.** The `(3,3,3,4)`, binding-cut `t=1`, **one-peel** integral — the `corner334` fixed-slice
> corner loss `(u₀²·U₀ + u₁²·U₁)^{−c'}·|u₀|³|u₁|²` **integrated over the deep data**, with the units cast
> as squared Euclidean norms `U₀ = ‖X‖² = ∑X_i²` (deep block `X ∈ [−T,T]^{d₀}`, `d₀ = 8`) and
> `U₁ = ‖Z‖² = ∑Z_i²` (deep block `Z ∈ [−T,T]^{d₁}`, `d₁ = 4`) — is finite (`< ⊤`) for every
> `c' < 7/2 = ½·minAdm(3,3,3,4)`. The `A₂`-rank-drop tube `{U_k → 0}` that DIVERGES on the `corner334`
> fixed slice is here RESCUED by codimension (the deep Morse integrals `∫(∑X²)^{−w₀c'}`,
> `∫(∑Z²)^{−w₁c'}` converge), NON-binding under the full-codim conditions `d₀ ≥ 4`, `d₁ ≥ 3`.

- **Lean (headlines):**
  - `DLNFibre.DLN.RLCT.onePeelIntegral_lt_top` — width-general: `onePeelIntegral h0 h1 m0 m1 T c' < ⊤`
    for `c' < (h₀+h₁+2)/2`, given `h₀ ≤ m₀`, `h₁ ≤ m₁`, `0 < T`, `0 ≤ c'`.
  - `DLNFibre.DLN.RLCT.onePeel334_lt_top` — the `(3,3,3,4)` instance `(h₀,h₁,m₀,m₁) = (3,2,7,3)`
    (i.e. `d₀ = 8`, `d₁ = 4`) at the branch threshold `c' < 7/2`.
  - `DLNFibre.DLN.RLCT.cornerSliceAtUnits_le` — the weighted-AM-GM slice bound (the codim-decoupling).
  - `DLNFibre.DLN.RLCT.cornerSlice334Integral_eq_atUnits` — bridge: the banked `cornerSlice334Integral A₂`
    IS `cornerSliceAtUnits 3 2 (cornerUnit0 A₂ …) (cornerUnit1 A₂ …)` (definitional).
  - `DLNFibre.DLN.RLCT.onePeel334_threshold_eq_half_minAdm` — `7/2 = ½·minAdm ![3,3,3,4]`.
  - (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJOnePeel334.lean` @ `d517b162`, file pending bank)

- **Gloss.**
  - `cornerSliceAtUnits h0 h1 U0 U1 c' := ∫⁻_{u∈unitBox 2} (u₀²U₀+u₁²U₁)^{−c'}·(|u₀|^{h0}|u₁|^{h1})` — the
    `corner334` slice with explicit real units and general Jacobian powers. At `(3,2)` and the concrete
    `cornerUnit_k A₂` it is `rfl`-equal to the banked `cornerSlice334Integral`
    (`cornerSlice334Integral_eq_atUnits`).
  - `onePeelIntegral h0 h1 m0 m1 T c' := ∫⁻_{X∈morseBox (m0+1) T} ∫⁻_{Z∈morseBox (m1+1) T}
    cornerSliceAtUnits h0 h1 (∑X²) (∑Z²) c'` — the corner slice integrated over the two deep blocks, with
    the units cast as `‖X‖²`, `‖Z‖²`.
  - `cornerSliceAtUnits_le`: for `A = ‖X‖², B = ‖Z‖² > 0` and weights `w₀+w₁ = 1` in `[0,1]`, the slice is
    `≤ ofReal(A^{−w₀c'})·ofReal(B^{−w₁c'})·∫_u ofReal(|u₀|^{h₀−2w₀c'}|u₁|^{h₁−2w₁c'})`. This is the
    pointwise weighted AM-GM `(u₀²A+u₁²B)^{−c'} ≤ (u₀²A)^{−w₀c'}(u₁²B)^{−w₁c'}` (a.e. on the open box),
    with the deep powers `A^{−w₀c'},B^{−w₁c'}` factored out as `u`-constants.
  - `onePeelIntegral_lt_top`: choosing the min-cut weights `w₀ = (h₀+1)/s`, `w₁ = (h₁+1)/s`,
    `s = h₀+h₁+2`, the joint integral factors (Tonelli) into the two `u`-marginals (finite ⟺ `c' < s/2`)
    and the two deep Morse integrals `∫(∑X²)^{−w₀c'}`, `∫(∑Z²)^{−w₁c'}` (banked `sumSqND_box_lt_top`,
    finite ⟺ `w_k c' < (m_k+1)/2`, guaranteed by `h_k ≤ m_k`). All four finite for `c' < s/2`.

- **Proved (unconditional).** (i) The bridge identity to the banked `corner334` slice. (ii) The
  weighted-AM-GM slice codim-decoupling `cornerSliceAtUnits_le`. (iii) The **one-peel finiteness**: the
  corner slice integrated over the deep `(X,Z)` blocks is `< ⊤` for `c' < (h₀+h₁+2)/2`, width-general
  under `h_k ≤ m_k`, and its `(3,3,3,4)` instance at `7/2 = ½·minAdm(3,3,3,4)` (banked charge
  `sjSlice334_minAdm_eq : minAdm ![3,3,3,4] = 7`). The `A₂`-rank-drop complement is closed HERE (not
  deferred): the tube `{X→0}` (resp. `{Z→0}`) is integrable because the deep Morse integral
  `∫(∑X²)^{−w₀c'}` converges near the origin — the codim rescue, explicit as `sumSqND_box_lt_top`'s
  finiteness condition. Non-vacuity witness in-file (`onePeelIntegral 3 2 7 3 1 3 < ⊤`, i.e. `T=1`, `c'=3`).

- **Assumed (hypotheses the claim also needs).** The deep data is posed **in the clean `(X,Z)`
  coordinates** — `X ⊥ Z` on disjoint Euclidean blocks, `U₀ = ‖X‖²`, `U₁ = ‖Z‖²`. Full-codim conditions
  `d₀ ≥ h₀+1 = 4`, `d₁ ≥ h₁+1 = 3` (cert: `d₀ = 8`, `d₁ = 4`, comfortably above). Bounded deep boxes
  `[−T,T]^{d_k}` (the singularity is at the origin; the box is the local chart). `0 ≤ c'`.

- **Cited.** none reproved here — S2-FREE (no `monomial_rlct`, no `cited_aoyagi_dln`). Box-finiteness at the
  branch threshold `7/2` only; the `rlct = ½·codim` reading stays Cited (Watanabe + Aoyagi).

- **Deferred (named, not omitted).**
  - **The `A₂`-matrix casting (unit-as-norm CoV).** The theorem integrates over the clean `(X,Z)`
    coordinates, NOT over a literal deep matrix `A₂` with `U_k = cornerUnit_k A₂`. For coordinate-aligned
    test directions (`v̄ = e₃`, `w₁ = e₁`, `w₂ = e₂` on a `3×4` `A₂`) the `(X,Z)` blocks ARE the row blocks
    of `A₂` and the casting is a no-op; for general generic directions it is an orthogonal
    (measure-preserving) rotation of the row space — a linear-CoV step (the matrix-space measure diamond,
    `lean/CLAUDE.md` Mathlib-gotchas) left as follow-on. The `cornerSlice334Integral_eq_atUnits` bridge
    connects the inner integrand to the banked `A₂` object; the outer deep integral over `A₂` needs the CoV.
  - **Corner334 row-count.** The banked `cornerSlice334Integral` uses `A₂ : Matrix (Fin 2) (Fin q)` (2
    rows), whose codim story does not reproduce the cert's `(d₀,d₁) = (8,4)` (which needs 3 rows). This
    module works in the honest clean coordinates instead, sidestepping the mismatch.
  - **The general recursion.** admissible class + decorated driver + `m > 2` (per cert §4 "Next" and
    `t4-merge` §5).

- **Structure & ideas observed (pen-and-paper, cert `onepeel-tonelli-cert.md`).** The joint integral closes
  at strict `c' < 7/2`; every rank-drop tube is non-binding (`{U₁=0}→c'<4`, `{U₀=0}→c'<11/2`, `{A₂=0}→c'<6`,
  all `> 7/2`); no hidden mixed/rank-2 threshold (decorrelated Codex, exact + MC). The binding `7/2` is the
  SECTOR slice endpoint; the complement is a **Morse codim-rescue, not a deeper peel** (refining the earlier
  "explicit deeper-stratum" framing).

- **Route (formaliser, this thread).** The cert's "sector + complement + rate-of-`S`" assembly is REPLACED
  by a single-mechanism route that needs NO corner-slice asymptotic rate: a pointwise **weighted AM-GM at
  the min-cut weights** `(4/7, 3/7)` decouples `(u₀²‖X‖²+u₁²‖Z‖²)^{−c'}` into a product of a `u`-monomial
  and the two deep norm-powers; Tonelli factors the joint integral into the two `u`-marginals (the binding
  `7/2`) and the two deep **Morse** integrals (the codim rescue, banked `sumSqND_box_lt_top`). The rank-drop
  complement is thereby closed by the Morse integrand's integrability near the origin, not by any rate bound
  — the same weighted-AM-GM the banked `Slice334`/`corner334` use, now coupling `u` to the deep norms.

- **Status.** sorry-free (awaiting reviewer fidelity check).
