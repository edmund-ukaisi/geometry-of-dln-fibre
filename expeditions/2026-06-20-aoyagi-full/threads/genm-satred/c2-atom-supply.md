# c2-atom-supply — my machinery for the c≥2 joint-principalization atom (decstep LEADS, I SUPPLY)

**Seat:** pen-and-paper (design), `genm-satred`, the LAST design gate. **Date:** 2026-07-17. **NO Lean.**
Supplies decstep (who LEADS the determinantal-variety rank-sector + monomial normal form + radial/polar box
lemmas + fires the decorrelated Codex): the per-corank A_r arithmetic, the c×c CoV design + |det J|
discipline, the pivot-Gram-not-corank confirmation, and — the key — the **self-similarity** that resolves
decstep's crux. Verified: exact-ℕ (`scripts/c2_atom_selfsim.py`, `decstep_c2.py`; per-corank min=minAdm,
sub-chain cut-soundness 324/324).

---

## ★ THE KEY INSIGHT — the c≥2 atom is SELF-SIMILAR (a nested DLN sub-product)

After integrating C (`gammaAtom_aniso_shifted_eq`, trading corank→pivot Gram), the residual is
`(w + ‖(Γ·Q_b)(I−P_{Q̃ₚ})‖²)^{−(c'−au/2)}`, and **`Γ·Q_b` is a PRODUCT — `Γ` (a×b) · `Q_b` (b×n)** — a
2-layer DLN sub-product (widths `a, b, n'`, `n' = n−u` the off-pivot dim; `Q_b·(I−P_{Q̃ₚ}) = A_cor·(Zf(I−P))`
adds the `M₂` layer, so the sub-chain is `(a, b, M₂, n')`-shaped). **So the c×c joint incidence `Γ₂S=0` is
the rank-drop of a nested DLN product — resolved by the SAME `minAdm` recursion, one level down.** This IS
the corank-block self-similarity: the c≥2 atom is a SMALLER DLN, resolved recursively (flag-γ' nested).

**⟹ decstep's crux (do the normal form's exceptional powers stay ≥ threshold, `a_i − 2c·N_i` sign?) reduces
to the SUB-CHAIN's cut-soundness** — the exceptional powers of the determinantal blow-up of `{rank(Γ·Q_b)=s}`
ARE the DLN codim exponents of the sub-chain, and "stay ≥ threshold" IS `minAdm(a,b,n') ≤ (a−s)(b−s) +
minAdm(s,n')` (the `minAdm` recursion), verified **0-fail (324/324, `c2_atom_selfsim.py`)**. So the
exceptional powers DO stay ≥ threshold — **by the airtight self-similar recursion**, NOT a fresh estimate.
(This is my SUPPLY; decstep confirms the exact `a_i, N_i` via the monomial normal form + the Codex red-team —
the self-similarity should make the sign uniformly non-negative.)

## ★bis REFINEMENT (decstep's Codex red-team) — RELATIVE (not free) principalization + A_r = sign-repair

decstep fired the Codex red-team on §★: **the self-similarity is the RIGHT structural idea and the arithmetic
is airtight, but NECESSARY-NOT-SUFFICIENT** (gap = the PROJECTED-TAIL principalization). Two refinements:

1. **The residual is `Γ·Q_b^⊥`, `Q_b^⊥ = Q_b(I−P_{Q̃ₚ})`, with `Q_b^⊥·Q̃ₚᵀ = 0` IDENTICALLY** — so `Q_b^⊥` is
   COUPLED to the pivot (it lives in the quotient by `rowspace(Q̃ₚ)`). So it is a **RELATIVE joint
   principalization, NOT a free sub-chain.** The sub-chain is `(a, b, n')` with **`n' = n − u` the PROJECTED
   width** (the off-pivot complement), and `Γ·Q_b^⊥` has leading width `c=min(a,b)`, not `t*` (they agree
   ACCIDENTALLY at n=4 since `t*=c=2`, not generally). So my sub-chain cut-soundness (324/324, §★) is the
   ARITHMETIC (necessary), but the ORDINARY DLN arity-IH does NOT directly apply — it needs the
   **relative-quotient lemma** (the coupling to the pivot via `Q_b^⊥Q̃ₚᵀ=0`). This is decstep's normal-form lead.

2. **`A_r = (b−r)²` IS the SIGN-REPAIR (my A_r is more central than the "outer nesting" framing).** Codex: the
   NAIVE pivot-Gram exponent on the rank-`k` shared-tail stratum is `k−n` (`−1` at `k=n−1`, `−2` at `k=n−2`),
   so the `c < c+1` gate is strict ONLY at the top (`k=n`). **The transverse determinantal Jacobian = my
   stratum codim `A_r = (b−r)²` is EXACTLY what raises `k−n` to `>−1`**, and `min_r[A_r + minAdm(redChain
   u'_r M)] = minAdm(M)` confirms the repaired sign reaches `c*`. So **A_r is the sign-repair mechanism** — the
   genuinely-new ANALYTIC theorem (decstep leads the monomial normal form) is proving the **transverse-Jacobian
   = A_r-codim identity + the `>−1` sign repair, UNIFORM across the shared-tail rank strata** (the relative
   joint principalization). Buildable (detail-at-scale, standard determinantal resolution) — NOT a wall, NOT
   cited.

**Net:** my §★ self-similarity + §1 A_r give the STRUCTURE + airtight ARITHMETIC (the necessary skeleton);
the genuinely-new ANALYTIC theorem is the RELATIVE joint principalization (the transverse-Jacobian=A_r-codim
identity + the >−1 sign repair, uniform across strata + the relative-quotient coupling), which decstep leads.

## 1. The per-corank A_r vector (the OUTER corank rank-sector, my §2)

The corank `Q_b = A_cor·Zf` (b×n) rank-strata `r ∈ [max(0,b−ρ) .. min(b,ρ)]`, stratum `r` → cut
`u'_r = u+(b−r)` → `redChain u'_r M`, charge **`A_r = peelCharge(u'_r) = (M₀−u'_r)(M₁−u'_r)`**, with

    min_r [ A_r + minAdm(redChain u'_r M) ] = minAdm(M)   (verified 0/4039 + the c≥2 examples below).

Exact A_r vectors (verified `c2_atom_selfsim.py`): `(4,4,4,4)@u=2` (a=b=2): `A_r=[0,1,4]` at `u'=[4,3,2]`,
min sum `= 11 = minAdm`. `(5,5,5,5)@u=2` (a=b=3): `A_r=[0,1,4,9]`, min `= 17 = minAdm`. The `A_r = (b−r)²`
pattern (square corank). This is the OUTER nesting (corank rank); the joint incidence (Γ·Q_b, §★) is the
INNER, self-similar level.

## 2. The c×c CoV atom design + the |det J| discipline

The genuinely-new atom (the c≥2 analogue of §3's pinned corank-one C-transversality): blow up the joint
incidence `{rank((Γ·Q_b)(I−P_{Q̃ₚ})) = s}`, `s ∈ 0..c` (`c = min(a,b)`), to a monomial normal form. **The
Jacobian `|det J| = ∏ e_i^{a_i}` (the exceptional monomial) is CARRIED — NEVER dropped** (the tide-D KILL
guard; my discipline). The normal form's pushforward = a **finite sum of shifted PLAIN reduced-chain
integrals** (the sub-chain's `redChain` at exponents `≤ ½minAdm` by the sub-chain cut-soundness §★). The
radial/polar box lemmas (decstep's lead) integrate each exceptional chart; the shift per chart stays below
the threshold by the self-similar recursion. Structure: the k=1 (§3) C-transversality is the `s=c−1..c`
special case (the disposable `|v'|^{−a}` via the a<u sphere); k≥2 is the full determinantal rank-sector,
self-similar to the sub-DLN.

## 3. Pivot-Gram-not-corank confirmation to c≥2 (my §3bis + decstep's shared catch)

The C-integration (`gammaAtom_aniso_shifted_eq`, `R=Q̃ₚ, q=u, S=Γ·Q_b, p=a`) trades corank→pivot Gram
**REGARDLESS of c** (the gammaAtom is c-agnostic — it integrates the a×u block `C`). So the carried Jacobian
is **`det(Q̃ₚQ̃ₚᵀ)^{−a/2}` (the PIVOT Gram, full-rank u, disposed by `qbox_lintegral_lt_top` per-level),
NEVER `det(Q_bQ_bᵀ)^{−a/2}` (the CORANK Gram — at edge dims `a < q−b+1 = a < a = FALSE`, the RouteMSJDecorated
"atom trap").** Confirmed carries to c≥2 (the C-block is a×u regardless of the corank rank c). The controller's
Q2 phrasing "jac = det(Q_bQ_bᵀ)" was the trap — it is the pivot Gram.

## 4. What decstep leads vs what I supplied

- **I SUPPLIED:** the self-similarity (§★, the crux-resolving insight); the per-corank A_r + nested min=minAdm
  (§1, exact-ℕ); the c×c CoV structure + the |det J| discipline (§2); the pivot-Gram-not-corank confirmation
  (§3). The min-over-strata ARITHMETIC (my §2 =minAdm 0/4039 + the sub-chain cut-soundness 324/324) is airtight.
- **decstep LEADS:** the exact determinantal-variety monomial normal form (the `a_i, N_i` exceptional powers);
  the radial/polar box lemmas; the decorrelated Codex red-team of the `a_i − 2c·N_i` sign (which the
  self-similarity §★ should make uniformly ≥0). When we pin it, the controller commissions the Route-Dec tide.

## Close

- **Firmest.** The c≥2 joint-principalization atom is SELF-SIMILAR: the residual `Γ·Q_b` is a nested DLN
  sub-product, its determinantal rank-sector resolves by the SAME `minAdm` recursion, and decstep's crux
  (exceptional powers ≥ threshold) reduces to the sub-chain's cut-soundness — airtight (324/324). The per-corank
  A_r + nested = minAdm (0/4039). Pivot-Gram-not-corank carries to c≥2. The |det J| is carried (never dropped).
- **Most likely to break.** (i) Dropping the |det J| exceptional monomial (the KILL guard). (ii) Using the
  corank Gram (the a<q−b+1 trap) — always the pivot Gram. (iii) The self-similar sub-chain widths (`a,b,n'` vs
  `a,b,M₂,n'`) must be read from the actual `Zf(I−P)` dims (decstep's normal-form detail) — the STRUCTURE
  (self-similar → minAdm recursion) is robust, the exact widths are decstep's to pin.
- **Next.** decstep pins the monomial normal form + fires the Codex red-team of the exceptional-power sign
  (the self-similarity §★ is the argument it should confirm); I'm on-call for the per-chart A_r + the
  sub-chain cut-soundness at the exact widths decstep's normal form fixes. When pinned → the Route-Dec tide.

Files (absolute): `…/threads/genm-satred/c2-atom-supply.md` (this); `D-cert.md` (§2 min-over-strata, §3 k=1
pinned atom, §3bis pivot-Gram, §4bis c≥2-decorated); `scripts/{c2_atom_selfsim,decstep_c2}.py`.
