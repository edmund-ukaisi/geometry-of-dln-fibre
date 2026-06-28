# O2 adjudication — the Sc-core pushforward density inequality (the N4 general-corank recursion gate)

**Seat:** `pen-and-paper` (`witness`/`obstruction` adjudication, no Lean). **Date:** 2026-06-28.
**Thread:** `28-hfin-recStep-spec`. **Task:** #103 (the BLOCKED-paper O1/O2 gate).
**Question (controller):** on the minor-dominant chart, does the law of the Schur complement
`Sc(R) = M22 − M21·M11⁻¹·M12` dominate a free `(r−j)×(r−j)` box so the per-chart Sc-core integral is
controlled by the corank-`(r−j)` IH with constants INDEPENDENT of the spectator (non-Sc) entries — or
does it concentrate / the constant blow up (the recursion plan breaks)?
**Method:** exact sympy (Jacobian, box containment, frobSq homogeneity) on corank-3 (`r=3, j=1`, the
first corank where the recursion genuinely fires) + corank-4 (`r=4, j=2`) + decorrelated Codex (xhigh,
independent). Scripts in `scripts/` (the `o2_*` family); Codex `codex/n4-o2-{prompt,answer}.md`.

---

## VERDICT: O2 **HOLDS** (WITNESS — the recursion's pushforward step is SOUND, spectator-uniform).
## The general-corank N4 recursion's O2 gate does NOT break the plan. The (A) premise survives.

> **The one-line resolution.** O2's framing ("pushforward density `dR ≽ ρ·dSc`") is the wrong lens —
> the recursion does NOT change variables `R → Sc`. It holds `R`, sandwiches the integrand (N2b), and
> the R-integral of the Sc-core splits as `R = (spectators M12,M21 ; M22)`. At FIXED spectators, the
> map `M22 ↦ Sc = M22 − M21·M11⁻¹·M12` is a **pure translation (Jacobian ≡ 1)** whose image sits in a
> **fixed spectator-independent box** `[-2,2]^{(r-j)²}` (`[-(1+j),1+j]` for `j≥2`, via the proved
> Cramer shear bound). So the Sc-core R-integral is **upper-dominated by the free-box corank-`(r−j)`
> joint core** (the IH) times the spectator-box volume — a spectator-independent constant. The
> additive threshold `jp/2 + λ_{r−j,p}` is preserved (the top Morse block is integrated JOINTLY, not
> frozen). Decorrelated Codex (xhigh) independently reached the identical verdict via the identical
> mechanism.

---

## 0. The frame correction (read first — O2 as posed conflates two different recursions)

The team-lead's O2 asks for a **change-of-variables / pushforward density** `dR ≽ ρ·dSc` with `ρ`
admitting spectator-independent constants. **That is not the mechanism the recursion uses.** The
validated recursion (`L32a-cover-cert.md` §3, `RouteMSchurDepth2.lean` at `r=2`, thread 27
`Vzero-termination-cert.md`) is:

1. **N2b two-sided sandwich (PROVED, `schur_minorPivot_split`):** on the bounded complete-pivoting
   cell, `c₀·D(R,S) ≤ frobSq(R·S) ≤ c₁·D(R,S)` with `D = frobSq((R·S)_top) + frobSq(Sc·S_bot)` and
   `(c₀,c₁)` **uniform** (quantified before `∀ R,S`). The inverse-power flip
   (`schurSplit_integrand_le`) gives `frobSq(R·S)^{−c'} ≤ c₀^{−c'}·D^{−c'}` — **R stays the
   integration variable.**
2. **Fubini over S** at fixed R, into the disjoint groups `S_top` (top Morse block) ⊕ `S_bot`
   (Sc-core). The recursion descends on the **core integrand** `frobSq(Sc·S_bot)^{−c'}` as a function
   of `(Sc, S_bot)` with `Sc = Sc(R)` a fixed COEFFICIENT matrix per `R`.

So the recursion variable one level down is **`S_bot` (the free block), never `Sc` or `R`**. There is
**no `R → Sc` change of variables anywhere**. O2's real content is the *outer* `R`-integral of the
inner Sc-core integral, which is what §1–§3 below adjudicate. (Codex Q5, independently: "The right
viewpoint for finiteness is upper domination of the pushforward measure … A lower-density framing
`dR ≥ ρ dC` is not needed for this finiteness step.")

**Why corank-3 is where it first bites.** At `r=2`, `Sc` is a `1×1` scalar; the Sc-core threshold
`λ_{r−j,p} = λ_{1,p}` is dominated and the depth-2 proof legitimately **drops** the core via `W ≥ 0`
(`radial_morse_dominates_absZ_lt_top`) — the recursion never fires. At **`r=3, j=1`** the binding term
is `jp/2 + λ_{2,p}` with `λ_{2,p} > 0` NONZERO and binding (e.g. `(3,3,4)`: `2 + 2 = 4 = λ_{3,4}`,
vs the Morse-only `jp/2 = 2` which UNDERSHOOTS). So at corank-3 the Sc-core MUST be integrated, not
dropped — exactly the first place O2 has teeth. (`o2_addcheck.py`, `o2_disjsum.py`, exact.)

---

## 1. THE PUSHFORWARD IS A TRANSLATION (Jacobian ≡ 1) — Q1, exact + Codex-PROVEN

On the `M11`-dominant chart (`R[0,0]=1` pivot, `|R entries| ≤ 1`), split `j=1`: `M11 = R[0,0] = 1`,
`M12 = R[0,1:]` (spectator row), `M21 = R[1:,0]` (spectator col), `M22 = R[1:,1:]`. Then

    Sc[a,b]  =  M22[a,b] − (M21·M11⁻¹·M12)[a,b]  =  M22[a,b] − M21[a]·M12[b]    (M11 = 1).

The subtracted term depends **only on the spectators** (M12, M21), never on M22. Hence the map
`(M12, M21, M22) ↦ (M12, M21, Sc)` is **triangular**, and `M22 ↦ Sc` at fixed spectators is a pure
**translation**:

    d(Sc)/d(M22)  =  Identity,    det = 1.    (exact, `o2_corank3.py` j=1; `o2_jge2_clean.py` j=2.)

**Verified for `j=2, r=4` too** (`o2_jge2_clean.py`): `Sc = M22 − M21·M11⁻¹·M12`, `Sc − M22` contains
no M22 variable, `d(Sc)/d(M22) = I₄`, `det = 1`. The translation is **independent of `j`** — `Sc` is
always `M22` minus a spectator-only matrix.

**Image of the M22-box.** For fixed spectators, `M22 ∈ [-1,1]^{(r-j)²} ⟺ Sc ∈ [-1,1]^{(r-j)²} − shift`,
`shift = M21·M11⁻¹·M12`. With `|shift entries| ≤ 1` (`j=1`: `|M21[a]·M12[b]| ≤ 1`), the translated box
sits in the **fixed box `[-2,2]^{(r-j)²}`, independently of the spectators**. (`o2_exact_cert.py`.)

> **Codex (Q1) = PROVEN, independently:** "triangular in `(x,y,Z)`, with `C` depending on `Z` by
> translation. Hence its Jacobian determinant is `1`. … this translated box is contained in the fixed
> box `[-2,2]^{n²}`, independently of `x,y`."

---

## 2. THE SPECTATOR-UNIFORM DOMINATION — Q2, exact + Codex-PROVEN

For any `g ≥ 0` (here `g(Sc) =` the inner-S integral at fixed Sc), the translation + box containment
give, with **NO constant depending on the spectators**:

    ∫_{M22 ∈ [-1,1]^{(r-j)²}} g(Sc(M22, spec)) dM22
      = ∫_{Sc ∈ [-1,1]^{(r-j)²} − shift} g(Sc) dSc        [translation, Jac = 1]
      ≤ ∫_{Sc ∈ [-2,2]^{(r-j)²}} g(Sc) dSc =: G            [box ⊆ [-2,2], g ≥ 0].

`G` is a CONSTANT, independent of all spectators. Integrating over the spectator box:

    ∫_R [Sc-core](R) dR  =  ∫_{spec} ∫_{M22} g(Sc) dM22 d(spec)  ≤  G · vol(spectator box).

**`G` IS the free corank-`(r−j)` joint core** — the IH target — over the box `[-2,2]`. The side-4 box
is harmless: the frobSq degree-2 homogeneity gives `∫_{[-2,2]} g = 2^{(r-j)² − 2c'}·∫_{[-1,1]} g`, a
spectator-independent constant factor, SAME threshold (`o2_boxscale.py`, exact). So O2's required bound
holds with **K = vol(spectator box) · 2^{(r-j)²−2c'}** and the bound = the free-box corank-`(r−j)` core.

> **Codex (Q2) = PROVEN.** Reproduces the exact chain; the displayed bound `≤ 2^{2n}·∫_{C∈[-2,2]}…`,
> "`2^{2n}` is exactly the spectator-box volume."

---

## 3. THE ADDITIVE THRESHOLD `jp/2 + λ_{r−j,p}` SURVIVES — Q3, exact + Codex-PROVEN

The load-bearing soundness point. The recursion needs finiteness for `c' < jp/2 + λ_{r−j,p}` (the
disjoint SUM of the top Morse block and the Sc-core); the Morse-only bound `jp/2` UNDERSHOOTS when the
Sc-core binds (corank-3+, §0). The translation argument preserves the ADD because the top Morse block
is integrated **jointly with** the Sc-core, NOT frozen:

    ∫_R ∫_S D^{−c'}  ≤  K · ∫_{Sc ∈ [-2,2]^{(r-j)²}} ∫_{V} ∫_{W} (‖W‖² + ‖Sc·V‖²)^{−c'} dW dV dSc,

where `W = S_top + (shear)·S_bot` is the **measure-preserving shear-peel** of the top block into a free
`jp`-dim Morse block (the depth-2 `lintegral_translate_le_local` pattern; box enlarges to radius
`r·T`, a fixed factor), `V = S_bot`, and the RHS is the **free-box corank-`(r−j)` JOINT core**
(Morse ⊕ Sc-core), finite for `c' < jp/2 + λ_{r−j,p}` by the IH. The `(R·S)_top` block depends only on
(M11, M12) — NOT on M22 (`o2_topindep.py`, exact) — so the M22↦Sc translation leaves the Morse block
untouched, and the two disjoint groups separate cleanly.

> **Codex (Q3) = PROVEN.** "The `p/2` contribution enters through the integrated Morse variables `W`.
> We are not applying the corank-`(r−1)` estimate pointwise in `C`; we apply the free-box joint
> integral in `(W,V,C)` … finite for `c' < p/2 + λ_{r−1,p}`. If one froze `W = 0`, the estimate would
> indeed undershoot to the core threshold. **That is not the argument used here.**"

---

## 4. NO HIDDEN FAILURE MODES — Q4

- **`{det Sc = 0}` / `{Sc = 0}` inside the Sc-box:** these are measure-zero `Sc`-loci. The fixed-`Sc`
  inner-S integral can diverge there (e.g. `Sc = 0 ⟹ frobSq(0) = 0 ⟹ ∫ 0^{−c'} = ⊤`), but the
  **JOINT** `(Sc, S_bot)` integral is the relevant object, and its finiteness at `λ_{r−j,p}` IS the
  IH. **The free Sc-box core is structurally identical to the corank-`(r−j)` `‖Δ·S‖²` core** (Sc plays
  the role of the free residual `Δ`); so its finiteness is exactly the inductive hypothesis, proved by
  the SAME recursion one corank lower — **not a new obstruction** (`o2_q4.py`). The `{Sc near
  singular}` locus is the next radial-blow-up + Schur level (R4 re-pinning, `minorpivot-cert.md`).
- **`j ≥ 2`:** the `M22 ↦ Sc` translation Jac = 1 holds verbatim (verified `r=4, j=2`). The only
  `j`-dependence is the Sc-box SIZE: `|Sc[a,b]| ≤ 1 + |(M21·M11⁻¹·M12)[a,b]|`, and the shear term is
  bounded **spectator-uniformly** by the **already-PROVED Cramer minor-ratio bound** (N2a,
  `RouteMSchurShear.rowShear_entry_le_one`: `|M21·M11⁻¹ entry| ≤ 1`), giving `|shear entry| ≤ j`, so
  `Sc-box ⊆ [-(1+j),1+j]^{(r-j)²}` — a FIXED box (`o2_jge2_uniform.py`). The box side is a harmless
  constant per the rescale lemma. Codex's `j≥2` NEEDS-CARE ("sound if the chart gives uniform bounds
  on `M11⁻¹`") is precisely this Cramer bound — which is **proved, not assumed**.

> **Codex (Q4) = PROVEN `j=1`, NEEDS-CARE `j≥2` (closed here).** "the loci `det C = 0` and `C = 0` are
> … measure-zero `C`-loci. The joint `(C,S)`-integral is the relevant object and is finite below the
> IH threshold." For `j≥2`: "sound if the chart gives uniform bounds on `M11⁻¹`" — supplied by the
> proved Cramer shear bound.

---

## 5. O1 in passing (the minor-dominant cover machinery) — FEASIBLE, already designed

O1 (the controller's secondary ask) is the **nested minor-pivot cover** — covering the inner `R`-space
by `j×j`-minor-invertible OPEN neighbourhoods (`argmaxCellOn`/`Finset.exists_max_image` over the
`Finset` of `j×j` minors, pivot = max-modulus minor). This is fully designed in `minorpivot-cert.md`
(BUILD-READY for general `r`) with the four refinements (comparison-not-equality, the Cramer shear
`≤ 1`, a deterministic tie-break for disjointness, per-level re-pinning). It reuses the generic argmax
cover at the minor level — **no rank-minor bridge theorem needed**. The one not-yet-verbatim piece is
the minor-level `univ_ae_cover` analog (an `argmaxCellOn` over a `Finset` of minors with the
tie-break); Codex (minorpivot Q2) confirmed `exists_max_image` discharges it. O1 is a build cost
(index/permutation bookkeeping), **not a math wall**. O2 (this cert) is the priority and it HOLDS.

---

## 6. CLOSE (the discipline trio)

- **Firmest result (the witness certificate).** O2 HOLDS. The recursion's outer R-integral of the
  Sc-core is spectator-uniformly dominated by the free-box corank-`(r−j)` JOINT core (the IH), via the
  `M22 ↦ Sc` **translation (Jacobian ≡ 1)** + fixed-box containment (`[-2,2]`, `j=1`; `[-(1+j),1+j]`,
  `j≥2` via the proved Cramer bound). The additive threshold `jp/2 + λ_{r−j,p}` is preserved (the
  Morse block is integrated jointly, not frozen). EXACT for `r=3,j=1` and `r=4,j=2`; decorrelated
  Codex (xhigh) independently PROVEN-corroborated Q1–Q3, NEEDS-CARE-then-closed Q4. **The general-corank
  N4 recursion's O2 gate is sound; R1-UPPER ∀M N4 is bounded-after-machinery; the (A) premise survives.**
- **Most likely to break it (the fragile step, my read + Codex).** Not O2 itself but its Lean
  realization: the **joint free-box corank-`(r−j)` core as the clean IH statement** — i.e. the
  recursion carrier must be the JOINT `(W, V, Sc)` integral `∫(‖W‖² + ‖Sc·V‖²)^{−c'}` over free boxes,
  NOT the Sc-core alone, or the additive threshold is lost. The depth-2 proof drops the core (`r=2`
  scalar Sc, core non-binding); the corank-3 lift must KEEP both blocks and recurse on the JOINT core.
  This is a STATEMENT-shape requirement on the WellFounded recursion (measure = corank), exact-confirmed
  here, but it is where a naive "dominate by the Sc-core, recurse" Lean attempt would silently undershoot.
- **Next construction / consult to settle the open part.** Build the corank-3 instance (`(3,3,4)`,
  depth-2 → depth-... wait, corank-3 is the FIRST genuine recursion, depth ≤ 3) of the JOINT free-box
  core lemma: `∫_{Sc-box} ∫_V ∫_W (‖W‖² + frobSq(Sc·V))^{−c'} < ⊤ for c' < jp/2 + λ_{r-j,p}`, with the
  M22↦Sc translation (`lintegral_translate_le_local`, already in `RouteMSchurDepth2`) and the box
  containment. Then lift to general `r` via the WellFounded-on-corank carrier. The one Lean-shape
  consult worth firing: confirm the JOINT-core IH statement composes through `recStep` without the
  Morse-block freeze (the additive-threshold preservation, §3).

**Cross-ref:** refines `L32a-cover-cert.md` §3 (the rank recursion) and `minorpivot-cert.md` (O1);
answers the BLOCKED-paper gate on task #103. The Sc-pushforward concern is RESOLVED as a translation,
not a nonlinear CoV. Scripts: `scripts/o2_{corank3,mechanism,corank3_factor,decisive,exact_cert,
addcheck,disjsum,fulladd,topindep,jge2_clean,jge2_uniform,q4,boxscale}.py`. Codex:
`codex/n4-o2-{prompt,answer}.md`.
