# Cert — the within-node ψ-mix: is the u-pivot load-bearing, and can one ψ factor the node?

*Seat: `pen-and-paper` (pnp-psi), commissioned to adjudicate T1/T2 + price the fold-lemma fix
(R-a vs R-b). Paper certificate only, NO Lean edits. Exact `sympy` / exact rational (`fractions`);
MC never used. Batteries alongside (`battery/*.py`, all exit-0). Decorrelated Codex leg
(`codex/psi-mix-{prompt,answer}.md`, xhigh, hypothesis withheld — the challenge itself came from a
Codex, so the leg was run as an INDEPENDENT derivation from Aoyagi's chart structure, not a
confirmation-read; both its witnesses were re-verified in my battery). Pinned to Aoyagi pp.15–18
(Case-1 center + charts `1(1)`/`1(2)`, `Q` p.17, `P` p.18) and the Lean lemma
`node_pivotCover_of_atom_sheared` (`ShearReconcile.lean:42–52`).*

---

## VERDICTS (one line each)

- **T1 = YES.** The Case-1 `u`-pivot chart (`1(1)`) is geometrically load-bearing: it is the unique
  cover chart of the `u`-max-modulus sector (positive measure, not just the axis); no `d`-pivot chart
  reaches it. The tick-113/162 escape "(i)" — *`1(1)` is a ledger-only extra, `localSub = id`* — is
  **FALSE**: `1(1)`'s `localSub` is the genuine `u`-blow-up `d_{ij} = u·d'_{ij}` (ψ=id, but β ≠ id).
- **T2 = NO.** No single per-node ψ factors all cover-family charts. Two independent obstructions:
  (a) `u`-edge needs ψ=id, `d`-edges need ψ=Schur — **frame-robust**; (b) distinct `d`-pivots carry
  distinct (conjugate, not equal) ambient Schur gauges — frame-dependent. The Codex "gap" claim is
  **CONFIRMED and sharpened**: modelling the mix as per-edge *target* displacement opens a
  **fundamental interior gap** (unfixable by enlarging domains). Diagnosis: the gap is an artifact of
  placing the det-1 gauge on the target/ambient side.
- **Route = R-b (source-reparameterization), decisively.** R-a (per-edge *target* ψ) inherits the
  interior gap and cannot reuse the banked pure atom. R-b keeps chart images = pure β images (tiles,
  no gap → the **pure** `node_pivotCover_of_atom` applies), absorbs each gauge into the source
  (`|det Dα|=1` ⇒ Jacobian + monomial exponents unchanged).

---

## T1 — the u-pivot is load-bearing (NOT a ledger-only extra)

`[Page-pinned]` Aoyagi pp.15–16 (verbatim, `page-pin-centers.md`): the Case-1 blow-up center is
`{d_{ij}=0 : i∈[J+1,J+J₁], j∈[J+1,M^{(S+1)}]} ∪ {u_{s,k}=0}`, codim `d_center = J₁·(M^{(S+1)}−J)+1`
(the `+1` **is** `u`). Charts: `1(1)` pivots on `u` (`d_{ij}=u·d'_{ij}` — a genuine substitution,
NOT id); `1(2)` pivots on a `d`-entry (corner → unit), then applies `Q`/`P`.

`[Proved — exact rational, `battery/t1-upivot-loadbearing.py`]` In the strict `u`-max sector
`{|d_{ij}| < |u|, u≠0}` (positive measure; the `u`-axis `{D=0, u≠0}` is its boundary), the max-modulus
coordinate is `u`, so **only the `u`-pivot chart covers it**; every `d`-pivot needs `|d_{pivot}| ≥ |u|`,
which fails. Dropping the `u`-pivot (the `d`-only family = the "(i)" escape) leaves a **real gap** at
every tested Case-1 node (`(J₁,cols) ∈ {(1,1),(1,2),(2,1),(2,2),(1,3),(3,1),(2,3),(3,2)}`; the grid
enumeration finds a `d`-only miss that the full family covers). Codex Q1 concurs independently.

`[Corroboration]` R2 Leg-1 (`hunt-cert-atlas-closure.md`) tested the FULL symmetric `d_center`
family — which, since `d_center` counts `u` as the `+1`, **includes the `u`-pivot** as one symmetric
max-modulus chart. Its "every `(d−1)`-subset misses its omitted pivot's axis `e_omit`" therefore
already contains the omit-`u` case → misses the `u`-axis. So Leg-1 corroborates T1 for the **pure-β**
family. It is **silent on the ψ-mix** (it tested ψ=id on all charts) — which is exactly T2.

**Precise correction to "(i)":** `1(1)` IS a genuine tree edge (Aoyagi recurses through it), but its
`localSub` is `β_u` (the `u`-blow-up), not `id`. It carries ψ=id (no gauge) yet β≠id (real geometry).
So the cover family is `{u-pivot (ψ=id)} ∪ {d-pivots (ψ=Schur)}` — a **genuinely mixed** node.

## T2 — no single ψ; the mixed union has a fundamental interior gap

**(a) No single ψ.** `[Proved — exact symbolic, `battery/t2a-gauge-and-nosingle.py`]` I re-derived
Aoyagi's `1(2)` gauge INDEPENDENTLY from `Q` (p.17) and `P` (p.18): on a `2×2` ratio block the normal
form is `D''' = [[1,0],[0, r_{11}−r_{10}r_{01}]]` — the Schur complement, `det = 1`, unipotent (matches
`cert-single-psi` by an independent route). The lemma `node_pivotCover_of_atom_sheared` demands one
common ψ with `localSub_e = ψ(q.symm(pivotChart_e))` (`hloc`, `ShearReconcile.lean:47`). Solving ψ per
edge: the `u`-edge forces `ψ = id`; a `d`-edge forces `ψ = Schur` (differs by `−a·b ≠ 0` on the shared
residual coordinate). No common ψ. Two obstruction layers:
- `u` vs `d`: **frame-robust** — ψ_u=id moves nothing; ψ_d moves a residual coord. Distinct in ANY frame.
- `d` vs `d`: `[Proved]` pivot `(1,1)` moves `d_{22}` by `−d_{12}d_{21}/d_{11}`, pivot `(1,2)` moves
  `d_{21}` by `−d_{11}d_{22}/d_{12}` — distinct ambient maps (conjugate, not equal). Frame-dependent
  (a ratio-frame ψ could unify these; it can NOT absorb the `u`-edge). Codex Q2 concurs; witness
  `D=[[½,¼],[¼,0]], u=½` sits in `S_u ∩ S_{11}` where id ≠ Schur (`G_{11}` sends `d_{22}: 0 ↦ −⅛`).

**(b) The gap — CONFIRMED and shown fundamental.** `[Battery-verified — exact rational,
`battery/t2b-gap.py`, `battery/t2b-interior-gap.py`]` At the smallest node where the actual gauge bites
(`2×2` d-block + `u`, `d_center=5`), model the mix as per-edge *target* displacement
`⋃_e ψ_e(β_e(D_e))` (ψ_u=id, ψ_d=Schur). Against the pure-β family (which tiles the cube, 0 misses):
- 176 cube-grid points are pure-covered but ψ-missed;
- **1176 strictly-interior points** (all `|coord| ≤ ½`) remain missed even with a **generous source
  domain `R=10`** — so the gap is **fundamental**, not the `R<2` scaling artifact of Leg-2.
- Codex Q3 gives the crisp interior witness `y=(⅓,⅓,⅓,⅓,⅙)` — re-verified in my battery: `y ∉ S_u`
  (`⅓>⅙`), and each `G_e^{-1}(y)` pushes its residual to `⅔ > ⅓` (breaks max-modulus), so `y` is in no
  `ψ_e(β_e(D_e))`; interior (all `<1`). The mechanism: the id-sector and the Schur-sectors do not tile;
  their boundary cannot be matched (id ≠ Schur there).

**Diagnosis (interpretation).** The gap is not a defect of Aoyagi's resolution — it is an artifact of
placing the det-1 gauge on the **target/ambient** side of the chart (as `node_pivotCover_of_atom_sheared`
does via `localSub_e = ψ ∘ β_e`). The single-ψ lemma is SOUND when a common ψ exists (its proof sets
`U = ψ''cube` and factors `⋃ψ∘β_e = ψ(⋃β_e) = ψ(cube)`); for a mixed node `hloc` is simply
**unsatisfiable**, so the lemma cannot be applied — it is not "wrong", it is inapplicable.

## Route pricing — R-a vs R-b (fold lemma `node_pivotCover_of_atom_sheared`)

**R-a — per-edge *target* ψ_e (`hloc`/`hdom` per edge).** Fold statement: replace the shared ψ by
per-edge ψ_e; the cover becomes `V ⊆ ⋃_e ψ_e(β_e(D_e))`. **Not viable as a cover:** (i) the proof's
factoring `U = ψ''cube` has no single ψ to define `U`; (ii) the target statement is **false** — the
interior gap (T2-b) is inside any full-slab `V` the RLCT neighbourhood integral needs; (iii) the banked
atom `iUnion_pivotChart_image_eq_cubeBox` is about pure β and does **not** transfer (the ψ_e break the
tiling). R-a is thus a rewrite whose central obligation is unprovable, not merely "more element-chase."

**R-b — per-edge *source* reparam `β̃_e = β_e ∘ α_e^{-1}` (recommended).** `[Battery-verified,
`battery/route-rb-verify.py`; Codex Q4]`
- **Carrier surface (the 4-part spec).** Re-factor `localSub_e = ψ_e ∘ β_e`  ⟶  `localSub_e = β̃_e =
  β_e ∘ α_e^{-1}`, with the det-1 gauge as a SOURCE homeomorphism `α_e` (field (3): `α_e` with
  `|det Dα_e|=1`, `α_u=.refl`; field (4): `localSub_e = β̃_e` on the reparametrized domain `α_e(D_e)`).
- **Cover.** `β̃_e '' (α_e(D_e)) = β_e '' D_e` (verified: identical image sets, 1024 pts) — the pure
  sector, unchanged. So `⋃_e β̃_e(childRegion_e) = ⋃_e β_e(D_e) = cube` = the **pure**
  `node_pivotCover_of_atom` (equivalently the sheared lemma at `ψ = .refl`). The sheared variant is not
  needed for the cover at all. Per-edge gauges are absorbed WITHOUT a gap because α_e does not touch the
  image.
- **`LeafJacobianWith` det.** `|det Dβ̃_e| = |det Dβ_e|·|det Dα_e^{-1}| = |det Dβ_e|` (α_e det 1;
  verified `|det Dβ| = |w|^{d_center−1}`, unchanged). The existing det-1-bounded-diffeo clause carries
  over verbatim, relocated to the source.
- **Monomial exponents / D1 fidelity.** The Schur update in blow-up coords is
  `t·r_{ij} − (t·r_{ip})(t·r_{pj})/t = t(r_{ij} − r_{ip}r_{pj})` (Codex Q4) — it changes only **ratio**
  coordinates and introduces **no new power of `t`**, so the exceptional monomial exponents are
  preserved (this, not `det=1` alone, is what secures the exponents). `chartMap = fold of β̃_e` stays a
  concrete composition of banked atoms (`pivotChart` + the det-1 source gauge), so the D1 fidelity fold
  is unchanged in kind.

**Recommendation — R-b.** It reuses MORE banked machinery (the pure atom; the sheared lemma can be
retired to `ψ=.refl`), and the carrier spec absorbs the gauge more cleanly: the gauge lives where it
does not move the covering sets, so the cover stays a clean tiling while the Jacobian and monomial
exponents are provably untouched. R-a's cover obligation is false at a mixed node; R-b's is the pure
atom already banked.

## Codex decorrelation (hypothesis withheld; independent derivation)

`[OBS]` Given only Aoyagi's chart structure (my T1/T2/route conclusions withheld), Codex derived, by
its own algebra: Q1 only `1(1)` covers the `u`-max sector; Q2 no single Ψ (id-on-`S_u` vs Schur-on-`S_p`
conflict, explicit overlap witness); Q3 target-displaced per-edge gauges leave an **interior** gap
(witness `(⅓,⅓,⅓,⅓,⅙)`); Q4 the det-1 gauge belongs in each chart's **source** reparam, with the
monomial-exponent argument above. Both its witnesses re-verified exactly in my battery. Two independent
derivations agreeing to the component — and the convergence is decorrelated (I did not read its answer
before deriving T1/T2 and building the batteries).

## Close

- **Firmest (Proved / Battery-verified):** the `u`-pivot is load-bearing (T1); no single per-node ψ
  factors a mixed Case-1 node (T2a); the per-edge *target*-ψ model has a fundamental interior gap
  (T2b); R-b (source reparam) reduces the cover to the banked pure atom with Jacobian + monomial
  exponents provably unchanged.
- **Most likely to break it:** if the construction's `1(2)` charts, at a node whose residual is only
  `1×n` or `n×1` (no `2×2` residual), carry a `ψ_d` acting solely on the C-layer (not the d-coords),
  the *d-cover* does not gap there even though single-ψ still fails — the `d_center≥5` residual is where
  the d-coordinate gap first bites (`d_center=3` shows only the C-layer mismatch). This does not change
  the verdict (the `u`-edge obstruction is present from `d_center=2`), but a Lean formaliser should not
  assume the gap appears at every mixed node.
- **Next construction/consult that settles the open part:** the one owed piece for R-b is the concrete
  det-1 source gauge `α_e` in ratio coordinates (`α_u=id`; `α_d` = the inverse Schur update
  `r_{ij} ↦ r_{ij} − r_{ip}r_{pj}`, a banked polynomial unipotent) + its domain-reparam identity
  `β̃_e '' α_e(D_e) = β_e '' D_e`. That is a modest, banked-atom-shaped formalisation step; no further
  paper adjudication is needed before it.
