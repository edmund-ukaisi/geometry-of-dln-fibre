# Cert — gauge-in-chart vs squeeze-only (the shear reconciliation question)

*Seat: `pen-and-paper` (pnp08), fourth bounded task — decides whether the coverage fold needs a
reconciliation lemma. Adjudicated from the record + the page images p.16–18 (no new heavy computation);
the architect's framing is `threads/01-skeleton/t2-buildtree-design.md §6`. Register key as before.*

**Question.** Do Aoyagi's per-step chart substitutions compose a nontrivial coordinate gauge `ψ` (the
unipotent `Q`/`P` clears) INTO the chart map — verdict **(A) ψ-COMPOSED** (coverage fold needs the
one-lemma reconciliation: covers transport through the per-node bounded homeomorphism) — or is the chart
the PURE pivot blow-up with all residual distortion absorbed by the `LeafPullback` squeeze
(`ψ = id`) — verdict **(B) SQUEEZE-ONLY** (pure-pivot contract stands; no lemma)?

## VERDICT: **(A) ψ-COMPOSED.** The escape hatch (squeeze-only) is REJECTED.

**Page-pinned evidence (p.16–18, Case 1(2); the Case-2 clears pp.20–21 are identical in shape).**
`[CERT]` After the pivot blow-up factors `u_{S,J+1}` (the corner normalised to a unit, p.16), the paper
introduces two **regular (unipotent) matrices that transform the variables**:
- **`Q`** (p.17): `Q = [[1, -d'_{J+1,J+2}, …, -d'_{J+1,M^{(S+1)}}], [0,1,0,…], …]` — a unipotent matrix
  whose entries **are the residual variables** `-d'_{J+1,j}`. It defines the child's column coordinates:
  `D''_J = D'_J · Q`, and `C'^{(S+1)}_J = Q^{-1} C^{(S+1)}_J`.
- **`P`** (p.18): `P = [[1,0,…], [-(b'_{J+2}/b'_{J+1})·d''_{J+2,J+1}, 1, 0,…], …]` — unipotent, entries
  `-(b'/b')·d''` (again **variable-dependent**). It clears the pivot column: `P·diag(b')·D''_J =
  diag(b')·D'''_J`, `D'''_J = [1 O; O D_{J+1}]`.

`[CERT]` These are **variable-dependent** unipotent (triangular) matrices, applied as change-of-variables
that **define the child's residual coordinates** `d''`/`c'`. The recursion then continues on `D_{J+1}` in
those transformed coordinates. So the child's chart map to the parent is
> `chartMap = ψ ∘ β`, `β` = the monomial pivot blow-up (factor `u_{S,J+1}`), `ψ` = the unipotent
> `Q`/`P` shear (+ the corner-unit normalisation).

`ψ` is a **nontrivial, variable-dependent shear** — NOT the identity, and not a constant relabel (its
entries are the residual variables, so it bends/shears a coordinate box). This exactly instantiates the
compass fork-8 `chartMap = ψ∘β` and the architect's `LeafJacobian`.

**Why the determinant does NOT discriminate (and the chart geometry does).** `[CERT]` `Q` and `P` are
unipotent ⇒ `det = 1`; the corner-unit normalisation contributes a bounded unit ⇒ `lo ≤ |det Dψ| ≤ hi`
(the architect's bound; here the unipotent part is exactly 1). So `|det Dφ| = |det Dβ|·|det Dψ|` is the
pure monomial `∏|u|^{divExp-1}` up to a bounded unit — precisely the `g-chart-bridge-pullback` finding
("Jacobian = pure monomial"), which is therefore consistent with BOTH (A) and (B) and cannot decide it.
The discriminator is the **chart GEOMETRY**: because `ψ` is a nontrivial variable-dependent shear, the
image of a source box under the real chart is a **sheared** region, differing from `β`'s pure-pivot image
by `ψ`. Hence (A).

**Escape hatch (squeeze-only) REJECTED — precisely.** `[CERT]` Squeeze-only would require the residual
distortion to be a mere magnitude rescale of the integrand (`lo·‖z‖² ≤ residualCore ≤ hi·‖z‖²`) with the
integration coordinates unmoved. But `Q`/`P` **move the coordinates** (they DEFINE `d''`/`c'`, and the
recursion proceeds in them); pivot-clearing `D_J → [1 O; O D_{J+1}]` is a coordinate shear, not a
magnitude squeeze. The `LeafPullback` squeeze correctly absorbs the residual **Morse core / bounded-unit
`R`** (the `resRank` residual), but it does NOT absorb the pivot-clearing **shear** — that is a separate
coordinate gauge. So `ψ ≠ id`.

**Corroboration.** `[OBS]` Matches (i) the paper-map cert §5 ("unipotent `Q` (columns) then `P` (rows)
clear one pivot"); (ii) the architect's lean (the LDU/Morse gauge machinery — `RouteMInteriorLDU*`,
`DeepestGaugeChart` — exists as coordinate maps); (iii) compass fork-8 (`ψ` a bounded-unit local diffeo
with full inverse data). `[OBS]` My own T/M simulators do NOT discriminate: they carry only the
divisor-`T`/exponent ledger (ideal-side), never the coordinate maps — so their silence on `ψ` is not
evidence for (B); the geometric content lives in the `Q`/`P` substitutions, which are (A).

**Scoped-claim wording.** `[CERT]` *In Aoyagi's construction the per-step unipotent `Q`/`P` clears (p.17–18,
variable-dependent) are composed INTO the coordinate chart: `chartMap = ψ∘β` with `ψ` a nontrivial
bounded-unit shear (`det Dψ = 1` for the unipotent part; `lo≤|det Dψ|≤hi` with the corner-unit). `ψ ≠ id`
in general — the emission is the ψ-composed form. The pure-monomial Jacobian is consistent with both
options and is not the discriminator; the sheared chart geometry is.*

## Consequence for the build

Route the **one-lemma reconciliation**: coverage's cover argument must absorb the per-node bounded
homeomorphism `ψ` (covers transport through `ψ`), OR the pure-pivot cover contract gains an explicit
shear factor. The pure-pivot contract does NOT stand as-is. This confirms the architect's default
(route the reconciliation) and rejects the escape hatch.

**Most likely to break this verdict:** if the build reformulates the residual entirely inside
`residualCore` (so `Q`/`P` never appear as coordinate maps but only as ideal-generator rewrites justified
by Lemma 1) — then the RLCT VALUE would be gauge-free (Lemma-1 ideal invariance) but COVERAGE (a
geometric image-cover) still needs the chart, which is `ψ∘β`. The value-vs-coverage split is the crux:
Lemma 1 absorbs `Q`/`P` for the value; the geometric cover cannot. So (A) stands for the coverage fold
specifically — which is exactly what the reconciliation lemma is for.
