# minAdm PERMUTATION-INVARIANCE — the general-width no-collapse closure (link A, route i)

**Seat:** pen-and-paper (obstruction→PROOF; genm-sj5-cover). **Date:** 2026-07-12. **NO Lean.**
**Charge (team-lead):** PROVE `minAdm(M) = minAdm(sort M)` DIRECTLY from the QIP min-formula (route i),
OR exhibit the M where it breaks (the collapse candidate). This is the GATING (□)-soundness fact: if
minAdm over-counts the true codim at a width-spike, (□) is FALSE there and no route can prove it.

**Exact algebra:** `scripts/{perminv,crux,prove,close}.py` (the recursion, the sweeps, the crux). **Result:
PROVEN — no monster.** `minAdm` is fully permutation-invariant; the proof is a clean induction reducing to
one 3-width min-identity, whose core is an exact difference-of-squares. Combined with the banked (B)(C)(D),
this makes (□)-soundness a THEOREM MODULO AOYAGI **∀ width** (not just width-monotone).

---

## ★ THEOREM. `minAdm(M) = minAdm(σ·M)` for every permutation `σ` of the entries of `M`.

`minAdm` (RouteMLayerSplit) is the front-peel recursion
`minAdm(M₀,M₁,M₂,…,M_L) = min_{t≤min(M₀,M₁)}[(M₀−t)(M₁−t) + minAdm(t,M₂,…,M_L)]`, base
`minAdm(M₀,M₁)=M₀M₁`. It is NOT manifestly symmetric (it singles out the front pair). Sweep: 0 breaks over
all `M` with entries `0..8`, len `2..5` (full-permutation, `scripts/perminv.py`,`prove.py`) — no collapse
candidate.

### Proof (induction on arity, via adjacent transpositions `τ_i=(M_i\,M_{i+1})`, which generate `S_{L+1}`)

- **Base** arity ≤ 2: `minAdm(M₀,M₁)=M₀M₁` symmetric.
- **`i=0` (`M₀↔M₁`) — MANIFEST.** The front term `(M₀−t)(M₁−t)` and `min(M₀,M₁)` are symmetric in `M₀,M₁`;
  the recursion body is otherwise `M₀,M₁`-free.
- **`i≥2` (`M_i↔M_{i+1}`) — via IH.** The swap permutes the REDUCED chain `(t,M₂,…,M_L)`'s entries at
  positions `≥1` (not touching `t`); by the arity-`(n−1)` IH, `minAdm(t,M₂,…)` is invariant for each `t`;
  the front term is unaffected; so `min_t[…]` is invariant.
- **`i=1` (`M₁↔M₂`) — the CRUX.** Unrolling two peels,
  `minAdm(M₀,M₁,M₂,tail) = min_v [ h(M₀,M₁,M₂,v) + minAdm(v,tail) ]`, `v` = the cut passed to the tail,
  `h(M₀,M₁,M₂,v) = min_{v≤t≤min(M₀,M₁)} [(M₀−t)(M₁−t)+(t−v)(M₂−v)]` (`0≤v≤min(M₀,M₁,M₂)`). The swap gives
  the same `tail` with `h(M₀,M₂,M₁,v)`. **So it suffices: `h(M₀,M₁,M₂,v)=h(M₀,M₂,M₁,v)`.**

### The crux identity (PROVEN, general). Substitute `s=t−v`, `(a,b,c)=(M₀−v,M₁−v,M₂−v)≥0`:
`h = g(a,b,c) := min_{s∈[0,min(a,b)]}[(a−s)(b−s)+s·c]`; claim `g(a,b,c)=g(a,c,b)`.
`p₁(s)=(a−s)(b−s)+sc = s²−(a+b−c)s+ab` (convex, vertex `s₁=(a+b−c)/2`, domain `[0,min(a,b)]`);
`p₂(s)=s²−(a+c−b)s+ac` (vertex `s₂=(a+c−b)/2`, domain `[0,min(a,c)]`).

1. **Unconstrained min values EQUAL (exact difference-of-squares).** `min p_i = C_i − B_i²/4`:
   `[ab−(a+b−c)²/4] − [ac−(a+c−b)²/4] = a(b−c) − ¼[(a+b−c)²−(a+c−b)²]`. With `(a+(b−c))²−(a−(b−c))² =
   4a(b−c)`, this `= a(b−c) − a(b−c) = 0`. **EXACT, ∀ a,b,c.** [`scripts/prove.py`: symbolic Δ=0.]
2. **The "min is interior" condition COINCIDES for `p₁` and `p₂`.** `s₁∈[0,min(a,b)] ⟺ s₂∈[0,min(a,c)]`
   (both ⟺ the triangle-type inequality: no one of `a,b,c` exceeds the sum of the other two — symmetric in
   `b,c`). [`scripts/close.py`: 0 mismatches over `a,b,c∈0..15`.]
3. **Interior case** (triangle holds): both mins equal the unconstrained value → equal by (1).
4. **Non-interior case** (some arg > sum of others, e.g. `c>a+b`): `p₁` vertex `<0` → min at `s=0`, `=ab`;
   `p₂` vertex `>min(a,c)=a` → min at the upper boundary `s=a`, `=a²−(a+c−b)a+ac=ab`. Both `=ab`.
   (Symmetric for the `a>b+c` / `b>a+c` regimes.)

So `g(a,b,c)=g(a,c,b)` for all `a,b,c≥0` ⟹ `h` symmetric in `M₁↔M₂` ⟹ `minAdm` invariant under `τ_1`.
Adjacent transpositions generate `S_{L+1}`; invariance under each `τ_i` ⟹ full permutation-invariance. ∎

**Verification.** `g(a,b,c)=g(a,c,b)`: 0 breaks over `a,b,c∈0..15` (4096 triples). Full perm-invariance of
`minAdm`: 0 breaks over entries `0..8`, len `2..5`. The interior-condition coincidence: 0 mismatches.

---

## Consequence — link (A) CLOSES general-width; (□)-soundness is a theorem modulo Aoyagi ∀ width

`minAdm(M) =`[perm-inv, above]` minAdm(sort M) =`[cCodim_eq_qipMin + MvalMultSum geometric reading,
Monotone `sort M`]` cCodim(sort M) =`[(B) CThetaArbitrary perm-inv of cCodim]` cCodim(M)`. So
**`minAdm = cCodim ∀ width`** — the general-width gap (A) is CLOSED via route (i), NOT circular (the
invariance is `minAdm`'s own, proven from its recursion; (A-monotone) supplies only the sorted equality).
With **(C)** `cCodim = fibre Ext/orbit codim` (SigmaCodim, proven gen-width, alg-closed char-0) and **(D)**
Aoyagi `RLCT = ½·codim` (Cited): `RLCT = ½·cCodim = ½·minAdm ∀ width` ⟹ **no collapse, (□) a THEOREM
MODULO AOYAGI ∀ width.** The independent hunt's collapse-candidate locus (a non-monotone binding branch) is
now closed: `minAdm` there equals `minAdm(sort)`, where the monotone theorem applies.

## Firmest / break / next
- **Firmest.** `minAdm` permutation-invariance — PROVEN (induction + the crux difference-of-squares Δ=0 +
  the symmetric interior-condition + the matching non-interior boundary `ab`). No monster (0 breaks, large
  sweeps). Closes (A) general-width → (□)-soundness = theorem modulo Aoyagi ∀ width.
- **Most likely to break.** Nothing found; the one elementary step relying on the case-analysis (interior
  coincidence + boundary `ab`) is exhaustively verified and algebraically closed above — a formaliser lifts
  it directly (convex-parabola-on-interval min + the difference-of-squares).
- **Next.** Hand to the formaliser: `minAdm_perm_invariant` (the crux `g(a,b,c)=g(a,c,b)` is the one owed
  lemma; the induction is mechanical). Then wire `minAdm = cCodim ∀ width` (perm-inv + CThetaArbitrary),
  discharging the last general-width (□)-soundness link. Aoyagi stays the sole Cite.
