# genm-cornrev — adversarial review of the general-M corner recursion (peelcert)

**Seat:** reviewer (claim-soundness, decorrelated). **Target:** peelcert `cert.md` §"GENERAL-`M`
(past 3-width): the corner RECURSES" + §CLOSE(follow-up 1) watch-item (i). **Read-only; no Lean.**
**Decorrelated:** own Codex consult (`/tmp/cornrev_codex_prompt.md`, gpt-5.x xhigh, BOTH conclusions
withheld — I asked the open question, did not encode the linchpin framing). **Exact/numeric:**
`/tmp/cornrev_explore.py`, `/tmp/cornrev_explore2.py`, `/tmp/cornrev_mc4.py`; re-ran peelcert's
`/tmp/peelcert_linchpin.py`, `/tmp/peelcert_bilinear.py` (both reproduce 0-violation).

---

## VERDICT: **GAP** (the trivial linchpin does NOT close the general-M corner recursion)

The verification the certificate rests on — `minAdm(M) ≤ corner-codim = value(t★+1)` — is **threshold
bookkeeping, not an analytic reduction**, and at general width it degenerates to a **tautology** carrying
no analytic content. The corner *claim* is true (cited Aoyagi; MC-confirmed at width 4 below), but the
certificate's general-M *argument* closes only the top corner stratum and defers the deeper strata to a
"recursion" whose descent measure and per-level threshold are not established. This is a genuine,
precisely-located obligation for decbuild's Phase-2 — not closeable by the ℕ-linchpin lemma alone.

The verdict **agrees with the certificate's own hedge** ("verified only via the linchpin … not the full
per-level exponent count") but sharpens *why* it is insufficient and *where* the residual work sits.

---

## 1. The linchpin is a tautology — it carries zero analytic information

`minAdm(M) = min_t value(M,t)` **by definition**, so `minAdm(M) ≤ value(M, t★+1)` for any legal `t★+1`
is `min ≤ element`. Verified: over 12 400 `(M,t)` pairs (`L=3..5`), `value(M,t) < minAdm(M)` in **0**
cases (`/tmp/cornrev_explore.py`). The *only* non-trivial fact in the linchpin package is the numerical
**identity** `corner-codim = value(t★+1)`, verified `0/546` for **3-width only** — the general-width
corner-codim formula is *asserted* to "generalize layer by layer", never stated or checked past 3-width.

So the certificate's 3-width closure logic is really three steps, and only for 3-width is every step
discharged:
1. `corner-codim = value(t★+1)` — numerical identity (`0/546`, 3-width).
2. **corner integral finite up to `½·corner-codim`** — the ANALYTIC content; for 3-width this is the
   **free bilinear leaf** `(a,1,D)`, `minAdm=min(a,D)`, an actual Morse computation (banked).
3. `minAdm(M) ≤ corner-codim` (tautology) ⇒ corner finite up to `½·minAdm(M)`.

For general-M the certificate keeps step 3 (tautology) and *replaces step 2 with "it recurses"*. Step 2
is the load-bearing analytic obligation, and it is the one not discharged.

## 2. A codimension inequality does NOT imply finiteness to ½·codim (Codex Q3, exact)

Independent Codex, both conclusions withheld: **"Codimension bounds alone are insufficient."** RLCT can be
strictly below `½·codim` — e.g. `f = x⁴+y⁶`, zero-set `{0}` codim 2, RLCT `5/12 < 1 = ½·codim`. Therefore
`minAdm(M) ≤ corner-codim` does **not** guarantee the corner integral is finite for `c < ½·minAdm(M)`.
Finiteness needs the corner's **own RLCT to equal ½ its codim** (normal-crossing / "as mild as its
codimension"). This is exactly the expedition lesson the controller flagged: a `≤`-budget bound is
threshold accounting, not a reduction.

The certificate's defense — "deeper corank strata have codim `value(t★+k) ≥ minAdm`, so strictly
non-binding" — is **circular against this point**: it assumes RLCT `= ½·codim` on those strata to conclude
they don't bind. If a deeper stratum's RLCT is `< ½·codim`, a *higher* codim does not save it.

## 3. Where the gap lives, precisely: rank-drop-by-≥2 of a product block (Codex Q1)

The corner `{rank Q_b < b}` stratifies by rank. Two regimes:

- **Top stratum `{rank Q_b = b−1}` (drop-by-one) — CLOSES at general width.** Codex Q1 (exact) worked
  `M=(2,3,3,2)`, `t=1` (`a=1,b=2,q=2`, `Q_b = Y·A₂` a genuine 2×2 *product*): at an explicit rank-1 point
  `det(Y A₂)` is a smooth hypersurface, `z := det` is an analytic coordinate, the split gives
  `|B₀|²+γ₁²+w²` with measure `|z|^{a−1}`, reproducing charge `tq+a(b−1)+min(a,q−b+1)=4`, finite for
  `c<2=½·minAdm`. So the **product structure does not obstruct the drop-by-one case** — the 3-width
  bilinear-leaf picture survives the composition. My MC (`/tmp/cornrev_mc4.py`) confirms: the whole
  degenerate corner `{|det(Y·A₂)|<0.15}` of `(2,3,3,2)` is finite/controlled for `c<2` and blows up at
  `c→2`. **b=1 is entirely inside this case** (`{rank<1}={Q_b=0}` is the only stratum, a drop-by-one) —
  so `(2,2,1)` and all `b=1` charts are genuinely covered.

- **Deeper strata `{rank Q_b ≤ b−2}` (only for `b≥2`) — the GAP.** Codex Q1 (heuristic, and matching the
  claimant's own degen-answer "should be read recursively"): when ≥2 singular values vanish, the map
  `(Y,A₂,…) ↦ Q_b` loses transversality, the single-`z` CoV fails, multiple vanishing minors interact —
  `Q_b = Y·A_{≥2}` is a **determinantal variety of a product**, and "resolving those deeper strata needs a
  tailored resolution … the general corner remains open." This is the `~65-75%`-new resolution content
  (Aoyagi §5), NOT the free bilinear leaf, and NOT supplied by the linchpin.

## 4. No established well-founded descent for the corner recursion (Codex Q2, exact)

Codex Q2: **"No purely width/rank descent exists."** In the `(2,3,3,2)` corner, **both `Y` and `A₂` stay
full rank yet `Q_b = Y·A₂` drops rank** — the degeneracy is an *interaction of full-rank factors*, not one
factor collapsing. So a recursion that measures progress by "the factor that dropped rank" or by
#widths/arity "can revisit the identical configuration" — the certificate's "spawns a sub-peel on
`(a,1,deeper)`" names no descent measure, and none of the obvious ones (arity, factor rank) is monotone.
A valuation-along-rank-flags monovariant is plausible (Codex heuristic) but unproven. So **termination /
well-foundedness of the general-M corner recursion is not established.**

---

## Non-concerns (checked, cleared)

- **Category III (`b>q`, "all-degenerate") does NOT fire a genuine Γ-corner.** At the binding cut, `b>q`
  forces `a=0` in **0/860** scanned charts (`L=3..5`, widths `1..6`, `/tmp/cornrev_explore2.py`). `a=0`
  ⇒ `peelCharge=0`, empty `Γ` (`a×b` with `a=0`), so the operative peel is trivial — there is no
  divergent degenerate-Γ corner to recurse (the `D=q−b+1≤0` breakdown of the 3-width formula never
  actually bites). The certificate's framing "the whole chart is the degenerate-corner treatment" for
  category III is **imprecise**: the operative cut is `a=0`. (decbuild should still confirm the driver's
  cover produces/handles these, but there is **no divergence risk** here.)
- **The claim itself is true at width 4.** Full box-zeta MC of `(2,3,3,2)` (`½·minAdm=2`) is finite for
  `c<2`, blows up at `c→2` (`/tmp/cornrev_mc4.py`). Consistent with cited Aoyagi. **The gap is in the
  certificate's general-M argument, not a falsification of the result.**

---

## Exact residual obligation for decbuild Phase-2 (what the linchpin does NOT give)

The general-corner formalisation **cannot** be discharged by the ℕ-linchpin
`minAdm(M) ≤ t★q+a(b−1)+min(a,q−b+1)` alone. What is actually needed:

1. **Deeper-strata resolution (the heart).** For `b≥2`, establish that the corner integral over
   `{rank(Y·A_{≥2}) ≤ b−2}` — a product-determinantal variety — is finite up to `½·minAdm(M)`, i.e. that
   its RLCT reaches `½·codim`. This needs an actual resolution / nested blow-up along rank flags with a
   per-divisor weight = codim check, NOT a codim inequality. **This is the genuinely-new content.**
2. **Well-founded descent measure.** Specify and prove the monovariant that makes the corner recursion
   terminate (arity and factor-rank both fail — §4). Absent this, the "recurses by the same machinery"
   claim is not a proof.
3. **OR: show the deeper strata are never operative.** If the intended (S,J) rank-flag build routes the
   deeper strata elsewhere (other charts / a different cut) so a single `t★`-peel only ever closes its
   own top stratum, that routing must be exhibited — the certificate's clean-factoring story does not
   (and Codex Q3 of the claimant's own degen consult found the corner *is* part of the same peel, since
   `rank Q_b` is a tail condition, so it cannot simply be offloaded).

**Sufficient conditions under which the linchpin route IS complete** (front-loadable safely):
`b=1` at the peel cut (single stratum, closes), and the **top stratum** `{rank=b−1}` at any width
(closes, Codex Q1 exact + MC). So category-II corners are safe *down to* their rank-`(b−2)` strata; the
obligation is exactly those deeper strata for `b≥2`.

---

## Files
- Review inputs (mine): `/tmp/cornrev_explore.py`, `/tmp/cornrev_explore2.py`, `/tmp/cornrev_mc4.py`,
  `/tmp/cornrev_codex_prompt.md`, `/tmp/cornrev_codex_out.log`.
- Target: `expeditions/2026-06-20-aoyagi-full/threads/genm-peelcert/cert.md`,
  `.../codex/degen-{prompt,answer}.md`, `.../codex/crux-answer.md`.

---

# FOLLOW-UP 2 — audit of peelcert's DEEPER-STRATA RESOLUTION (§DEEPER-STRATA)

**Charge:** peelcert responded to the GAP above with an explicit blow-up (retracting the tautological
linchpin). Adversarially audit the RESOLUTION. **Decorrelated:** own second Codex consult
(`/tmp/cornrev2_codex_prompt.md`, gpt-5.x xhigh, BOTH conclusions withheld — asked the open pushforward /
discriminating-case / well-foundedness questions, did NOT encode the "it resolves" framing).
**Exact/numeric:** `/tmp/cornrev2_discriminate.py`, `/tmp/cornrev2_measure.py`, `/tmp/cornrev2_volscan.py`,
`/tmp/cornrev2_logcheck.py`, `/tmp/cornrev2_mc2334.py`; reproduced peelcert's `/tmp/deepstrat_explore.py`
(the `freed = frobSq(W̃·A₂)` identity is residual-0, independently rerun) and `/tmp/deepstrat_rlct.py`.

## VERDICT: **SOUND IN OUTCOME / RESIDUAL GAP IN THE GENERAL ARGUMENT**

The CRUX question — does the blow-up land RLCT **at** `½·codim = ½·minAdm(M)`, not **below** (the `x⁴+y⁶`
fear) — resolves **FAVOURABLY**: the deeper-corner threshold is `= ½·minAdm(M)`, the `x⁴+y⁶` trap is
genuinely avoided. This is a real advance over the retracted linchpin. What remains is **argument
completeness for the general case**, plus one **load-bearing step missing from the certificate** and one
**incomplete center-list** — scoped precisely below. Not a wall; not a claim-falsification (MC + cited
Aoyagi + two decorrelated Codex reads all agree the result is true).

## 1. The reduced-model RLCT arithmetic is CORRECT (independently reverified)

`freed = frobSq(W̃·A₂)`, `W̃ = [R_pivot; C′R_pivot+ΓY]` is residual-0 (rerun). The reduced model
`f ~ x₁²+p²+z²(x₂²+v²)` and its blow-up giving RLCT `3/2` are correct: I reverified the `z`-chart
(`f=z²(X²+P²+x₂²+v²)`, Jac order 2, loss order 2 ⇒ `(k+1)/N=3/2`) AND the `x₁`,`p` charts (unit `≥1`, same
`3/2`) — no chart gives worse. Volume-scan `V(ε)=P(f<ε)~ε^λ` gives `λ≈1.53` (flat model), matching `3/2`.

## 2. CRUX — the measure "twist": I chased it hard; it is threshold-preserving (log, not power)

`p,v` in the reduced model are the components of the **bilinear** `ΓY`, integrated by the certificate as
**flat** `dp dv`. The true measure is the pushforward of flat `(Γ,Y)` through `(Γ,Y)↦ΓY`. This pushforward
is genuinely **non-flat** — I measured `P(‖ΓY‖<r)` with slope `≈1.70 < 2` and a twist volume-scan
`λ≈1.44 < 1.5`, which *looked* like the corner RLCT dropping below `½·minAdm(M)` (the `x⁴+y⁶` disaster).

**It is not a drop.** My own decorrelated Codex (Q1, exact) gives the Jacobian of `(Γ,Y)↦(p,v)` as `|γ₁|²`
(resp. `|γ₂|²`), and `|y|≤1` forces `|Γ|≥c|(p,v)|`, so the pushforward density is
`ρ(p,v) ≍ log(1/|(p,v)|)` — **logarithmically** divergent, NOT a power. A log factor changes only the
**multiplicity**, leaving the RLCT **threshold unchanged at `3/2`**. Confirmed numerically two ways
(`/tmp/cornrev2_logcheck.py`): (i) the pushforward local slope **rises toward 2** and tracks
`2−1/ln(1/r)` (the `r²·log` signature) almost exactly — so the `1.70` was a log, not a power; (ii)
`V(ε)/ε^{1.5}` **grows** (log multiplicity) ⇒ true RLCT `=1.5`, and my `1.44` was a finite-`ε` log
artifact. **So the certificate's flat-`(p,v)` RLCT reading gives the correct THRESHOLD.**

→ **But this justification is ABSENT from the certificate.** It integrates `p,v` flat with no argument that
the bilinear pushforward is threshold-preserving. That step (the `|γ|²`-Jacobian ⇒ log-density lemma) is
load-bearing and must be stated/proved. FILLABLE — supplied here — but currently a hole in the written proof.

## 3. The base cases are measure-DEGENERATE; the discriminating case confirms `= ½·minAdm(M)`

`(2,3,2,2)`, `(2,3,3,2)` have `½·minAdm(remove-M₁) = ½·minAdm(M)` (both `3/2`, resp. `2`), so they
**cannot** test the load-bearing claim that "the `ΓY` twist LOWERS the RLCT from `½·minAdm(remove-M₁)` to
`½·minAdm(M)`." A genuine test needs a strict gap: `(2,3,3,4)`, `t★=1` has `½·minAdm(M)=2.5` vs
`½·minAdm(remove-M₁=(2,3,4))=3.0` (`/tmp/cornrev2_discriminate.py`). My true-measure corner MC there is
**uninformative** (`{‖Q_b‖<0.15}` on a `2×4` product has mass-fraction `≈0`). Codex Q2 (Newton-polytope
weight upper bound `RLCT≤5/2` + a stratum lower bound `≥5/2` on the `(x₂,p₂)∥(x₃,p₃)` locus) gives
`RLCT = 5/2 = ½·minAdm(2,3,3,4)` **exactly** — the twist genuinely lowers it to the global value, not below.
So the mechanism IS validated on a non-degenerate case — **but only via Codex's analysis, not carried in the
certificate** (whose base template is the degenerate `(2,3,2,2)`).

## 4. Well-foundedness + general induction — genuine RESIDUAL GAP (honestly scoped)

- **Termination:** the descent index `r = rank(unresolved Q_b) ∈ {b,…,0}` strictly decreases on the
  incidence-resolved charts and is bounded ⇒ terminates. Codex Q3 (exact) supports this. OK.
- **Incidence-center list is INCOMPLETE.** Codex Q3 finds an ADDITIONAL center beyond the certificate's
  `{A=0},{Y=0},{im A⊆ker Y}`: the **proportionality locus `(x₂,p₂)∥(x₃,p₃)`** (the one carrying the `5/2`
  value in `(2,3,3,4)`) must be added to the resolution for the normal-crossing / `RLCT=½·codim` property to
  hold at that stratum. This is a concrete, actionable correction for decbuild.
- **"No sub-`½codim` stratum" is HEURISTIC.** Codex Q3's general claim rests on "no evidence of a
  `sub-½codim` stratum until simultaneous collapse of two successive pivots, which the product-rank
  ordering forbids" — asserted, not proven. This matches the certificate's own honest scoping ("import
  Aoyagi §5 product-rank-flag machinery… not a full per-width exponent count"). The general induction with a
  per-stratum normal-crossing PROOF is not done.

## Exact residual obligation for decbuild's DeeperStrataResolution

1. **State + prove the twist-is-threshold-preserving lemma** (missing from the certificate): the bilinear
   `(Γ,Y)↦ΓY` pushforward density is `≍ log(1/|·|)` (Jacobian `|γ|²`), so it changes only the multiplicity,
   not the RLCT. The base-case `RLCT=3/2` reading is unjustified without it.
2. **Carry a non-degenerate validation** (`½·minAdm(rm-M₁) > ½·minAdm(M)`, e.g. `(2,3,3,4) → 5/2`) — the
   degenerate `(2,3,2,2)` base template does not exercise the twist-lowering mechanism.
3. **Complete the incidence-center list** with the proportionality locus `(x₂,p₂)∥(x₃,p₃)` (Codex Q3) and
   **prove** (not "no evidence") that no resolved stratum has `RLCT < ½·codim` at general width — the Aoyagi
   §5 product-rank-flag induction. This is the genuinely-new content; it remains open (honestly scoped).

**Safe to formalise now:** `b=1` + top stratum (unchanged); the `b=2` deepest-corner blow-up as the base
module (RLCT `3/2`/`2`) **provided** obligation 1 (the twist lemma) is discharged as an explicit step.
