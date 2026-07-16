**Q1 — Composition validity**
- FACT: After pivotBlock_radial_blowup the “pivot energy” entering the radial integral is  
  `E(Phat,A_cor) = ||Phat_p Q_p + Phat_b A_cor Z||_F^2`  
  `= tr(Q_p^T Phat_p^T Phat_p Q_p) + tr(Z^T A_cor^T Phat_b^T Phat_b A_cor Z) + 2 tr(Z^T A_cor^T Phat_b^T Phat_p Q_p)`. It depends affinely on `A_cor`.
- FACT: For scalar case `u=b=1`, `Z=[1,…,1]` with row length `n≥1`, `Q_p = q` (row), `Phat_p=α`, `Phat_b=β` with `α^2+β^2=1`, the energy is `||α q + β a Z||_2^2` (here `a` is the scalar entry of `A_cor`). Minimizing over `a∈[-1,1]` gives  
  `inf_a E = ||α q||^2 – α^2 (q·Z)^2 / ||Z||^2` (unconstrained minimizer `a* = - α (q·Z)/(β||Z||^2)`). If `|a*|≤1` and `q` is colinear with `Z` (e.g., take `q=Z`, `α=β=1/√2`, choose `a=-1`), then `inf_a E = 0`.
- FACT: Therefore no uniform `w0>0` independent of `A_cor` exists; the “pivot energy” used as the scalar `w` in `shell_corankOffSector_le_unif` varies with `A_cor` and can be driven to 0 inside the box.
- VERDICT: Step (ii) is invalid—`shell_corankOffSector_le_unif` assumes a fixed scalar `w` independent of `A_cor`, but the pivot energy produced in (i) depends on `A_cor` and can vanish.

**Q2 — Rank-drop locus**
- FACT: Energy `E=0` requires `Phat_p Q_p` to lie in the row-span of `Z`; then the stacked matrix `hsQ=[Q_p;A_cor Z]` has row-span contained in `span(Z)` and rank at most `rank(Z) (=M2) < M1` whenever `u>0`, so `hsQ` is rank-deficient relative to `M1`.
- INFERENCE: Restricting to the “shell” `{σ_min(hsQ) ≥ ε}` would enforce `E(Phat,A_cor) ≥ ε · κ(Phat)` for some `κ(Phat)>0`, giving a positive lower bound, but `shell_corankOffSector_le_unif` integrates over the full box, so excluding the rank-drop set does not repair the lemma’s applicability.
- VERDICT: The infimum 0 occurs on a rank-deficient locus of `hsQ`; shell restriction would help but is not permitted by the lemma’s domain, so the interface remains invalid.

**Q3 — Descent vs circularity**
- FACT: From the recursion `minAdm(M) = min_t [(M0−t)(M1−t) + minAdm(redChain t M)]`, taking the specific cut `u` gives  
  `minAdm(M) ≤ (M0−u)(M1−u) + minAdm(redChain u M) = peelCharge + minAdm(redChain u M)`.
- FACT: Rearranging, `minAdm(M) − peelCharge ≤ minAdm(redChain u M)`. Thus, if `c' < minAdm(M)/2`, then  
  `c' − peelCharge/2 < (minAdm(M) − peelCharge)/2 ≤ minAdm(redChain u M)/2`.
- VERDICT: The exponent after peeling, `c' − peelCharge/2`, automatically lies below the integrability threshold of the reduced chain; the step is a genuine descent to a shorter chain (one fewer layer), not circular. The only obstruction to the route is the faulty use of the corank lemma noted in Q1.
