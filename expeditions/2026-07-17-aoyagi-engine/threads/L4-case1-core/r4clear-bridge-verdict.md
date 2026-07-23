# §-note: r4Clear-bridge soundness (the ONE open gate) — §7 arm FIRES on E_J; F₂ absorption CONFIRMED as the fix

seat-L4D's owed decisive Gröbner check (their naive bridge FALSE on E_J col-0, no recoord). The gate:
does `uncleared foldResid ∈ ⟨cleared foldResid⟩` (cleared = r4Clear = pivot-cross β,γ→0) SURVIVE branch-(ii)'s
recoord? Scripts (exact sympy + Gröbner, exit 0): `verify/r4clear_bridge_recoord.py`. Decorrelated Codex
(xhigh, hypothesis withheld) corroborates every verdict.

## VERDICT: the E_J failure SURVIVES branch-(ii) ⟹ pure-zero r4Clear is UNSOUND for an all-entries StepInv.
On `(2,2,2,2)` / `(2,3,2)` / `(2,3,2,2)`, with the §8(m) branch-(ii) recoord applied in BOTH uncleared and
cleared (both signs ±γ, scoped `i≥cleared` and unscoped): the **col-1 (D_J) entries ARE in ⟨cleared⟩**, the
**col-0 (E_J) entries are NOT**. The recoord ABSORBS the naive `γ·(A₂A₁ col1)` remainder but EXPOSES
`A₂A₁ col0` (the pure deeper product) as the new non-member. So branch-(ii) does not rescue the E_J bridge —
it moves the remainder, not removes it. seat-L4D's §7 arm fires (per their verdict map + the controller's
pre-staged wait-state: "SURVIVES ⟹ §7 fires").

## THE FIX IS PINNED — the elder's pre-staged F₂ ABSORPTION (do-not-zero-but-absorb) makes the bridge TRUE.
Full-faithful contrast on `(2,2,2,2)` (`verify/r4clear_bridge_recoord.py` part 2):

| row | cleared construction | uncleared ∈ ⟨cleared⟩ |
|---|---|---|
| (A) | full faithful `Q₁·A₀·Q₂` + BOTH compensators (`A₁·Q₁⁻¹` recoord [+γ] AND `Q₂⁻¹` input) | **TRUE** (`= uncleared` identically — product-preserving ⟹ ⟨cleared⟩=⟨uncleared⟩) |
| (B) | render r4Clear: `−γ` recoord + literal `diag(1,e₂)` zero, NO `Q₂⁻¹` | **FALSE** |
| (C) | render + `Q₂⁻¹` input added, but KEEP the `−γ` recoord + literal zero | **FALSE** |
| (D) | `+γ` recoord (`Q₁⁻¹`) + literal `diag(1,e₂)` + `Q₂⁻¹` input | **TRUE** (`= uncleared`) |

So the bridge holds IFF the operation is the product-preserving faithful: BOTH the `+γ` (`Q₁⁻¹`) recoord AND
the `Q₂⁻¹` input-side col-op. This is exactly the elder's F₂ = "do-not-zero-but-absorb; her Q₂" — the
`Q₂⁻¹` neighbor-absorption on the input side. Under F₂ the cleared residual EQUALS the uncleared (product
preserved), so `uncleared ∈ ⟨cleared⟩` holds TRIVIALLY ⟹ **the M-bridge is PROVABLE, census back to 0.**

## The sign note (flag for seat-L4D + elder — a tension with §8(m)'s −γ)
The bridge needs the `+γ` (`Q₁⁻¹`, product-preserving) recoord, NOT the §8(m) `−γ`. Row (C) shows `−γ` +
`Q₂⁻¹` still FAILS; row (D) shows `+γ` + `Q₂⁻¹` holds. Coherent reading: the `−γ` was pinned for the
PURE-ZERO regime (it made the block-form boostReady's clean multilinear block, a CHILD-residual FORM
property); the bridge is a PARENT-CHILD IDEAL property and needs the faithful `+γ` + `Q₂⁻¹`. If §7/F₂ is
adopted (do-not-zero-but-absorb), the regime changes and the recoord returns to the faithful `+γ`. So the
two are not contradictory — they are the two regimes — but the recoord SIGN is regime-dependent and the
render must use `+γ` under F₂. (Decisive datum for the elder's F₂ ruling.)

## THE LOAD-BEARING FORK — is StepInv all-entries or D_J-only? (Codex point 3; def-side, seat-L4D owns)
The E_J failure is an OBSTRUCTION only if the StepInv quantifies over ALL residual entries. If the StepInv
is **D_J-only** (the E_J = cleared/identity columns tracked SEPARATELY via `foldB`/the exceptional ledger),
then the D_J (col-1) entries — which ALWAYS pass, every config above — suffice, and the pure-zero r4Clear is
SOUND (no §7, no F₂ needed). Codex [plausible-unverified]: "sound without `Q₂⁻¹` only under a verified
D_J-only invariant with separate E_J tracking." This is the one bit I cannot settle (I don't own the exact
StepInv statement); seat-L4D reads it against the Lean StepInv.

## Decorrelated Codex (verbatim)
(1) render r4Clear does NOT satisfy E_J membership [logical necessity]; (2) full faithful (both
compensators) removes the failure — product-preserving ⟹ identical ideals [logical necessity]; (3) E_J
failure is EXPECTED only under a D_J-only StepInv with separate E_J/foldB tracking — the exact StepInv
statement is decisive [plausible-unverified]; (4) pure cross-zeroing is unsound if StepInv is all-entries
(needs `Q₂⁻¹`), sound only under a verified D_J-only invariant [logical necessity].

## AUTHORITATIVE run on arch-C-3's VERBATIM formulas (`verify/r4clear_bridge_authoritative.py`, exit 0)
The render report's branch-(ii) (`−γ`, SCOPED `i ≥ cleared`, excl. pivot-col `a`) matches my
`r3r4_recoord_scope.py` shear per the diff (team-lead). On these EXACT formulas, all three witnesses:
- **uncleared ∈ ⟨cleared⟩: col-1 (D_J) PASSES, col-0 (E_J) FAILS.** Verdict on the exact object: **SURVIVES.**
- **foldB out CLOSED (analytically + numerically):** the real foldB is a SCALAR ledger factor (seat-L4D
  def-read). In the polynomial domain `ℚ[u]`, `b·x ∈ ⟨b·gᵢ⟩ ⟺ x ∈ ⟨gᵢ⟩` for `b ≠ 0` (nonzerodivisor) — so
  the b-weighting is membership-NEUTRAL. Verified: `b·uncl ∈ ⟨b·cleared⟩` matches the unweighted membership
  on every witness (generic scalar `b`). The real accumulated ledger CANNOT rescue the E_J failure.
- **δ=1 out CLOSED:** the E_J col-0 entry = the pure deeper product `A₂A₁ col0`, NOT divisible by the pivot
  coord `u₀₀₀` — so the δ=1 `u_pivot`-divisibility form also fails.
So all three OUTS seat-L4D/team-lead named (branch-(ii) both signs; real foldB; δ=1) are closed: **SURVIVES**
on the verbatim render, modulo only the structural D_J-only fork below.

## F₂ +γ-PAIRED regime — the arc's last verification (elder condition (c); `verify/f2_paired_boostready.py`, exit 0)
§7 fired ⟹ F₂ adopted (+γ recoord `Q₁⁻¹` + `Q₂⁻¹` input + paired `Q₁·A₀·Q₂` clearing). Re-verified, on the
FINAL +γ-paired object, the two criteria previously checked only under §8(m)'s `−γ`:
- **(a) ideal-close / census 0:** rows A/D (+γ + `Q₂⁻¹`), product-preserving ⟹ `⟨cleared⟩=⟨uncleared⟩`. Settled.
- **(b) boostReady / clean multilinear block:** HOLDS under +γ-paired (SCOPED), all three witnesses —
  `L0` = clean cleared block (pivot row/col zeroed, diag-shaped), residual multilinear (`deg_u₀₀₁=1`,
  `deg_u₀₁₀=1`). Sign-robust (the `−γ`→`+γ` flip does not disturb the form). ✓
- **(c) SCOPE — the `i≥cleared` bound is STILL NEEDED, NOT subsumed by the pairing.** Unscoped +γ-paired
  STILL gives `u₀₀₁²` (deg 2), all three witnesses. Reason: the inter-edge fold-order (ed1's clearing is
  applied OUTERMOST) means ed2's branch-(ii) recoord reads ed1's PRE-clear pivot-row entry regardless of the
  paired clearing — so the paired `Q₁·A₀` clearing does NOT make ed2 read the outer row as 0. The `i≥cleared`
  scope IS that "read the cleared outer row as 0" mechanism, and it must be KEPT on branch-(ii) under F₂.

**COMPLETE F₂ RENDER SPEC (all three criteria verified on the +γ-paired object):** keep the §8(m)
`i≥cleared` scope (c); recoord `+γ` (`Q₁⁻¹`, product-preserving) + `Q₂⁻¹` input + paired `Q₁·A₀·Q₂`
clearing (a,b). Under this the bridge is provable (census 0), boostReady holds, and the block is the clean
multilinear form.

## Bottom line for the merge gate
- **If StepInv is all-entries:** pure-zero r4Clear is UNSOUND (E_J fails, survives branch-(ii)) ⟹ §7 fires
  ⟹ adopt the elder's F₂ absorption (full faithful `Q₁·A₀·Q₂`, `+γ` recoord + `Q₂⁻¹` input) ⟹ bridge PROVABLE.
- **If StepInv is D_J-only:** pure-zero r4Clear is SOUND (D_J passes) ⟹ bounded +1 frontier, arch-C-3 bakes.
- The verdict hinges on the exact StepInv statement (seat-L4D's def-read). My compute pins: E_J fails / D_J
  passes (all witnesses, both signs); F₂ makes E_J pass; the recoord under F₂ must be `+γ`.
