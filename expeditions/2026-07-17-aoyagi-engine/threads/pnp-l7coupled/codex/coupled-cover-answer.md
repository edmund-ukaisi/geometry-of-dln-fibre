1. VERDICT: BOUNDED (buildable) for the stated full-fan atlas; the currently col-pinned atlas has a genuine escape unless the promised outer gauge charts are actually added.

2. Q1 — box clause

DERIVED: write/read disjointness holds structurally: (i) writes off the pivot cross and reads the cross; (ii) writes column \(a\) and reads columns \(i\ne a\); (iii) writes row \(b\) and reads rows \(k\ne b\). Different layers prevent cross-support collisions. Thus \(\sigma^{-1}=id-\phi\).

For fixed \(d\), take \(C_*=\max\) layer width and \(f(r)=r+C_*r^2\). This is depth-independent, though not dimension-independent. Finite iteration cannot diverge; enormous finite closed balls remain compact.

Cheapest failure: domain admissibility. The actual chart region must contain the required \(f^{[\mathrm{depth}]}(1)\)-ball. Merely containing some positive-radius ball, as currently required at [MonumentAtlas.lean:152](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/lean/DLNFibre/DLN/Aoyagi/MonumentAtlas.lean:152), is insufficient. If the algebra and chart maps are global, this is harmless.

3. Q2 — fan completeness

DERIVED: a literal full fan over every \(p\in S\), with continuation for every pivot, covers the entire closed ball—not merely a.e. Pivot ties and the all-zero center stratum do not escape. Coupling and shared deeper factors do not alter this set-theoretic atom.

The sharp confound is that the current branch predicate fixes the pivot column to `cleared` [MonumentAtlas.lean:1068](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/lean/DLNFibre/DLN/Aoyagi/MonumentAtlas.lean:1068). For \(d=(4,4,4)\), at the root case-2 step, let \(q=(\text{layer }0,\text{row }0,\text{col }1)\). If only column-0 pivots occur, compactness gives a uniform \(M\) with
\[
|x_q|\le M|x_p|
\]
on every chart image. Hence the open cone
\[
|x_q|>(M+1)\max_{p\text{ allowed}}|x_p|
\]
escapes. The \(q\)-pivot full-fan chart closes it. An inner shear cannot repair an omitted outer blow-up pivot.

A determinantal-versus-coordinate-center mismatch would threaten resolution fidelity/`hideal`, not the full-fan cover atom itself.

4. Most likely breaker

Prove prefixwise that the actual emitted `gmap` family realizes every full-fan pivot—or an outer gauge-equivalent chart. First discriminating test: does the \(q=(0,0,1)\) root chart above genuinely occur? If not, current `hcover` is false.

5. F1–F5 audit

- F1 and F4 look correct; I found no coupled write/read overlap.
- F2’s conclusion is correct, but “reads only fresh block coordinates” overstates it: supports (ii)/(iii) read neighboring layers. Fixed widths, not freshness, give uniformity.
- F3 is plausible but unnecessary once F1 is established; “fresh coordinates” needs an actual branch-factorization theorem.
- F5 proves the abstract atom only. Sampling a full fan does not establish that the concrete atlas emits that fan or has adequate domains.