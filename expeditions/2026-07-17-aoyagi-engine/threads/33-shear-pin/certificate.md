# Certificate — the shear pin: do the unipotent Q,P enter `g`, and what is `|det Dg|`?

Pen-and-paper `pnp-shearpin` (thread 33), 2026-07-21. Gate: the coupled-B monument's geometric leaves
(the `Chart` `g` / `jac` / `unit` / `hjac` / `hideal_fwd`/`_bwd` fields). All results exact (sympy;
symbolic Jacobian determinants). Decorrelated Codex `xhigh` consult ran on the construction BEFORE this
verdict was fixed (`./codex/shear-pin-{prompt,answer}.md`); it converged on every load-bearing point by
its own route (incl. an independent direct 20×20 / 21×21 symbolic `det Dg`) and **sharpened one point**
(the `c11=1` normalization is itself a blow-up contributing `|ρ|^8`), folded in below. Batteries under
this thread: `shear_334.py`, `shear_224.py`, `shear_roles.py`, `shear_222_clean.py`, `rho_check.py`
(all PASS/EXIT 0).

---

## VERDICT: **corrected-(a)** — the record's conclusion stands; its *reason* is wrong.

Neither of the brief's options (a) or (b) is literally right, and (c) is false. The exact situation:

- The unimodular `Q,P` play **BOTH** roles at once — some are genuine **source coordinate changes**
  (part of `g`), one is forced to remain the **ideal cofactor** — and *which* is which is **principled**,
  not a framing choice (§2).
- The coordinate-change part is **unipotent with Jacobian EXACTLY 1**, so `|det Dg|` **is** the pure
  exceptional monomial `jacWeight jac` and **unit ≡ 1** (`|unit| = 1`) — the certificate's `hjac`
  CONCLUSION is CORRECT (§3).
- So the v4.2 record needs **NO structural change**; only the thread-31 certificate's *prose*
  ("pure-monomial `g`; `Q,P` are not coordinate changes") is imprecise and must be corrected (§4).

**In one line:** `g = (unipotent shears) ∘ (monomial blow-ups)` — structurally NOT pure-monomial (the
shears are real source coordinate changes) — but the shears are Jacobian-exactly-1, so `|det Dg|` is a
pure monomial and `unit ≡ 1`. This is uniform across clean and coupled corank≥2 (§5); there is no
dichotomy.

---

## (1) The two roles, made precise — worked on (3,3,4), the corank-(2,2) frontier

Chart `c11 = 1`, `C1` 3×3, `C2` 3×4. Block-elim `Q1 C1 Q2 = diag(1, Δ)`, `Δ = C22 − C21·C12`, with
`Q1 = [[1,0],[−C21,E]]` (row op), `Q2 = [[1,−C12],[0,E]]` (col op), both unipotent. Then

    C1·C2 = Q1⁻¹ · diag(1,Δ) · Q2⁻¹·C2 = Q1⁻¹ · [ [T] , [Δ·S] ],   T = row0(Q2⁻¹C2), S = rows12(C2).

`||C1C2||² ≠ ||T||² + ||Δ·S||²` (Frobenius NOT preserved) — the load-bearing soundness fact (threads
27/28), so the RLCT identity rides the IDEAL identity, not a value identity.

The pin: trace *which* transforms rewrite the source coordinates `u` (the `C`-entries) and *which*
recombine the output family `{(∏C)_{ij}}`.

| transform | induced map on source coords | det | status (`shear_334.py`, `shear_roles.py`) |
|---|---|---|---|
| Schur `C22 ↦ Δ = C22 − C21·C12` | `(C12,C21,C22) ↦ (C12,C21,Δ)`, keep `C12,C21` | **1** | invertible **coordinate change** → part of `g` |
| `Q2⁻¹` absorbed into `C2` | `C2 ↦ Q2⁻¹C2` (row0 sheared by `C12`) | **1** | invertible **coordinate change** → part of `g` |
| combined shear (both) | 20-var map | **1** | Jacobian **EXACTLY 1** |
| `Q1` as a literal left op `C1 ↦ Q1·C1` | `(C12,C21,C22) ↦ (C12, 0, Δ)` (**clears `C21`**) | **0** | non-invertible **projection** → CANNOT be a coord change |

`Q1⁻¹` therefore **must** stay as the `RegionRepresents` cofactor: `C1C2 = Q1⁻¹·[T; Δ·S]` with
`Q1⁻¹ = [[1,0],[C21,E]]` unipotent, entries = source coords, `= I` at `0` (continuous, vanishing-of-
the-off-diagonal allowed). It recombines the OUTPUT rows (the `d_N` basis), not the source `u`.

## (2) Why the split is PRINCIPLED, not a framing choice

The discriminator is invertibility of the induced source map:

- `Q2` / Schur use **KEPT** coordinates (`C12`, `C21`) to shear a **DIFFERENT** coordinate (`C22`, or
  `C2`'s row0) → triangular with identity diagonal → **det 1, invertible** → legal coordinate change.
- `Q1` uses coordinate `C21` to **clear `C21` itself** → the induced map drops rank (`det 0`) → **not
  invertible** → cannot be a coordinate change; forced to be the ideal cofactor.

So it is *false* that "`Q,P` enter only as cofactors" (Schur & `Q2` are real coordinate changes) AND
*false* that "fold all `Q,P` into `g`" (`Q1` is a non-invertible projection — it cannot go into `g`).
Codex reached this exact table independently (`Q1`: det 0 clears `B`; `Q2`-literal: det 0 clears `A`;
`Q2⁻¹`-into-`C2`: det 1; Schur: det 1).

## (3) `|det Dg|` is a PURE monomial, `unit ≡ 1`

The coordinate-change shears (§1) have Jacobian exactly 1, so folding them into `g` contributes nothing;
the blow-ups contribute the monomial. Two independent computations agree:

- **Chain-rule (this thread, `shear_334.py`):** `|det Dg| = det(shear)=1 · (radial T: q³)(radial Δ: u³)(join E) = E⁷·α³`.
- **End-to-end direct determinant (`shear_224.py`):** for the (2,2,4) heart, the *full* chart map
  (radial blow-up + a folded unipotent Schur shear, an honest 12×12 Jacobian) has `|det Dg| = u³`
  DIRECTLY — the folded shear added nothing.
- **Codex, direct 20×20/21×21 symbolic det:** `det Dg_normalized = −E⁷α³` (sign = orientation only),
  `|det Dg| = E⁷α³`, "despite `g` itself containing the nonmonomial terms `BA` and `AS`."

**Structural reason it holds at all `L`/widths/coranks:** the exceptional coordinates `u_{s,k}`
(blow-up variables) are **never touched by later shears** — the shears mix only *residual* (Schur-
complement) and *next-layer* coordinates among themselves. So the blow-up monomial `∏ u_{s,k}^{M_{s,k}−1}`
survives intact, and every shear factor is `1`. The only transform in Aoyagi's machinery that carries a
non-1 unit Jacobian is **Theorem 3's regular-block peel** `A2 ↦ −A1⁻¹A2` (det `= (det A1)^{−#}`) — and
that is the rank-`r` peel, **trivial at the deepest point `r=0`** where the whole resolution lives
(no regular block; the invariant's `E_J` pivots are the identity, so every in-recursion Schur reduction
is unipotent, pivot-normalized to 1). This closes Codex's one stated caveat ("I did not verify no
non-unipotent rescaling is inserted elsewhere"): the primary text inserts exactly one, and it is off the
`r=0` path.

**Codex refinement (folded in).** The `c11=1` chart is itself a normalized blow-up coordinate, not an
original weight. Including the preceding radial blow-up of `C1` (`C1 = ρ·Ĉ1`, codim-9) adds `|ρ|^8`
(`rho_check.py`), so the *complete* map to original weights has

    |det Dg| = |ρ|^8 · |E|^7 · |α|^3     (first join chart)

— **still a pure monomial, still unit ≡ 1**. The often-quoted `E⁷α³` is relative to the normalized
chart; `ρ` is a non-binding divisor (not in `b₁`), so the rlct read-off (binding `E`, `h_E=7`, ratio
`(7+1)/2 = 4 = ½·Mval(1,0)`) is unchanged. The loss unit `F∘g = ρ²E²·||Q1⁻¹(τ; αD̂S)||²` is genuinely
`≢ 1` (`=1` at `0`) — this is the *loss* unit (RegionRepresents / Object A), NOT the *Jacobian* unit;
the two are distinct and the Jacobian unit is exactly 1.

## (4) The corrected per-chart claim (what the thread-31 certificate should say)

Replace thread-31 §a's "`g` = composition of monomial substitutions … `Q,P` … not as coordinate
changes … (fold `Q,P` into `g`; then `g`'s Jacobian carries the pivot-determinant unit)" with:

> `g` per leaf `= (unipotent shears) ∘ (monomial blow-up substitutions)`. The shears are the Schur
> reductions `D_J ↦ diag(1, D_{J+1})` and the column-op transfers `C^{(S+1)} ↦ Q₂⁻¹C^{(S+1)}` — genuine
> **invertible source coordinate changes** (each uses kept coords to shear other coords), **polynomial**
> (pivot normalized to 1, so no division; inverse `M = Δ + BA` polynomial), `g 0 = 0`. Their Jacobian is
> **exactly 1** (unipotent, block-triangular with identity diagonal). Hence `|det Dg| = jacWeight jac`
> (the pure blow-up monomial) with `unit ≡ 1` (`|unit| = 1`) — `hjac` on all `nbhd`. The **left**
> row-recombinations `Q₁⁻¹` (and their accumulation) are non-invertible as source maps (each clears the
> coordinate it is built from), so they are **forced** to remain the `RegionRepresents` cofactors of
> `hideal_fwd`/`_bwd` (continuous on `nbhd`, vanishing allowed) — this is exactly why the loss is not
> Frobenius-preserved and Object A is load-bearing.

**Record fields — NO structural change needed** (confirmed against `ProductResolution.lean` v4.2):
- `hjac : |jacDet g u| = jacWeight jac u * |unit u|` — satisfied with `unit ≡ 1` (constant), `|unit|=1`,
  continuous nonvanishing. (The record *also* accommodates a non-1 unit via `hunit_cont`/`hunit_ne`, so
  it is robust either way — but the truth is `unit ≡ 1`.)
- `hideal_fwd`/`hideal_bwd` (`RegionRepresents`, cofactors `ContinuousOn nbhd`) — carry the `Q₁`-type
  cofactors; the record already requires only `ContinuousOn`, not nonvanishing (the "trap the record
  avoids" note is correct and necessary — the surviving cofactors DO vanish off-diagonal).
- `g`, `hg_analytic`, `hg0`, `hg_inj`/`excep`/`hexcep_null` — unaffected: `g` is polynomial (shears +
  blow-ups), fixes 0, and is birational (shears bijective, blow-ups injective off the exceptional locus).

## (5) No clean/coupled dichotomy (option (c) is FALSE)

`shear_222_clean.py`: the clean (2,2,2) step (scalar Schur `w = m22 − c21·c12`, corank 1) has the
**identical** structure — Schur & `Q2⁻¹C2` are det-1 coordinate changes, `Q1`-literal is a det-0
projection. Codex confirms the block-triangular calc holds for arbitrary residual size `M ↦ M − BA`.
Corank ≥ 2 changes only the *size* of the Schur block, the *number* of exceptional variables, and the
*monomial exponents* — never whether the shears are coordinate changes nor whether they inject a
Jacobian unit. The formalise-seat's flag ("clean verified pure-monomial, coupled flags risk") was a
*worry*, not a finding: clean instances verified `|det Dg| = pure monomial`, which is TRUE and remains
TRUE coupled. The worry is closed.

## Implication for the monument's geometric leaves (what the formaliser should state)

- **Do NOT state/prove "`g` is a monomial map."** That statement is FALSE from the 2nd blow-up onward
  (the residual/next-layer coords are sheared). State `g` as `(unipotent shears) ∘ (monomial blow-ups)`,
  polynomial, `g 0 = 0`.
- **`hjac`: take `unit := 1`** and prove `|det Dg| = jacWeight jac` via the chain rule — each blow-up
  step contributes its monomial Jacobian, each shear step `det = 1` (prove: block-triangular unipotent,
  pivot 1). No nontrivial unit is needed or true. (A false `jac` cannot game the value: the CoV theorem
  weights by the ACTUAL `jacWeightFn = |det Dg|`, bridged to `jacWeight jac` only through `hjac` — so
  the honest exponent is forced.)
- **`hideal_fwd`/`_bwd`: the cofactors are the surviving `Q₁`-type left/right recombinations** — regular
  (continuous) on `nbhd = {pivots ≠ 0}`, allowed to vanish. Do not require nonvanishing (that would make
  the record unsound, cf. the blow-up `y∘g = v·u`). Reserve nonvanishing for the Jacobian `unit` only.
- **Uniform construction:** one recursion serves clean and coupled corank≥2; no corank branching in the
  chart/Jacobian/cofactor structure. The coupled case differs only in block sizes / exponent counts.

## Most likely thing to break it / next check

The result is Jacobian-robust (two independent exact routes + Codex's direct big determinant). The one
residual assumption, now argued but worth a Lean-level guard: **every in-recursion pivot is normalizable
to exactly 1** (so every Schur shear is unipotent). This holds because the invariant's already-cleared
block is the identity `E_J` and the blow-up sends the pivot direction to the exceptional coordinate; the
only non-unipotent rescaling in the paper (Thm 3's `A1⁻¹`) is off the `r=0` path. If a future coupled
instance somehow left a pivot as a unit `w ≠ 1` (not normalized), the *shear* Jacobian would still be 1
(a translation of the residual block), but the cofactors would acquire `w⁻¹` factors (still regular on
`nbhd = {w ≠ 0}`) — the record still holds, `hjac` still `unit ≡ 1`. Next check if contested: an
`L ≥ 4` coupled instance with two independent shared deep factors (thread-27's flagged kill-end),
recomputing `|det Dg|` end-to-end to confirm no pivot escapes normalization — but the structural
argument (exceptional coords untouched by shears; `E_J` pivots = identity) already covers it.

## ADDENDUM (elder-ordered, 2026-07-21) — the composition ORDER is corrected; load-bearing conclusions survive
This certificate's "g = (unipotent shears) ∘ (monomial blow-ups)" — shear OUTERMOST — is a BOUNDARY
ARTIFACT of the (3,3,4) trace: the INITIALIZATION Schur (a Theorem-3-stage setup elimination)
precedes the first blow-up in that trace, which grouped the composition shear-first. The recursion's
PER-STEP atom, adjudicated from the pages (pp.16–21: blow-up substitution THEN the Q-transforms on
the POST-blow-up primed d′-coordinates; substitutions compose in reverse of temporal order), is
**blockBlowupMap ∘ edgeShear — blow-up OUTERMOST** (thread-34's order). At r = 0 there is no
initialization elimination and every atom is B∘S. THE LOAD-BEARING CONCLUSIONS OF THIS CERTIFICATE
ARE ORDER-INDEPENDENT AND SURVIVE: the shears are Jacobian-exactly-1; unit ≡ 1 for the composed
Jacobian; exceptional coordinates are never touched by shears (now formalized as the TreeEdge
hshear_pivot field). Caught by seat-L4's wall checkpoint (the two certificates' order disagreement);
elder adjudication in the journal, 2026-07-21. A codex decorrelation on the narrow order question
runs as confirm-before-the-wall-consumes insurance.
