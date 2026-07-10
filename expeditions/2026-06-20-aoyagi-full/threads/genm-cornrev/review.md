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
