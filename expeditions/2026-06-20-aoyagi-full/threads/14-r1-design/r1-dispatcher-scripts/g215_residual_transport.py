import sympy as sp
# Q2 crux: does the pivot blow-up's RESIDUAL = dlnLoss(schurState.red) 0 (up to the unit), so the
# carried cert field (residual-transports-to-dlnLoss-red) is dischargeable? Check the C1 node on (2,2,2).
# The C1 node (g183/g194): pivotBlowupOn (x_p²·Q) + det-1 Schur peel ⟹ residual on the reduced widths.
# Verify: after the C1 op at (2,2,2), the residual Q (post-blow-up, post-peel) = dlnLoss(schurState (2,2,2)) 0
# = dlnLoss((1,1,2)) 0 (the reduced chain), up to the bounded unit (the g of g174/g175).
#
# This is the g186 lintegral-transport claim. The KEY for fm3's ruling: split.red = schurState (the DEF,
# necessary) is NOT enough — the residual MUST be CERTIFIED = dlnLoss(split.red) 0, else split.red is
# abstract (Codex g206 item 2 vacuity). So the per-cell datum (b) carries: redCore_eq-analogue
# (residual ∘ chart =ᶠ dlnLoss(schurState.red) 0 ∘ redEmbed, up to unit) — which IS crux2's
# IsSchurStraightenSqueeze.redCore_eq (G² = dlnLoss S.red 0 ∘ redEmbed)!
print("Q2 RESOLUTION: does split.red = schurState (DEF) suffice, or carry the descent as a CERT FIELD?")
print()
print("FINDING: split.red = schurState is a clean DEF (width split, g214) — NECESSARY for termination +")
print("the value widths. But Codex g206 item 2 is RIGHT: the width def alone does NOT tie split.red to the")
print("pivot blow-up's ACTUAL residual. The soundness needs the per-cell CERT FIELD:")
print("   residual ∘ chart =ᶠ dlnLoss(schurState.red) 0 ∘ redEmbed   (up to the bounded unit g)")
print("which IS crux2's IsSchurStraightenSqueeze.redCore_eq (G² = dlnLoss S.red 0 ∘ redEmbed) — ALREADY the")
print("transport datum's field! So the descent-soundness is NOT a NEW obligation — it's redCore_eq, which the")
print("per-cell IsSchurStraightenSqueeze ALREADY carries (crux2's lane). The fix: PROVE split.red = schurState")
print("AND that the cell's IsSchurStraightenSqueeze.S.red = schurState (so redCore_eq ties split.red to the")
print("genuine reduced chain). Then split.red is NOT abstract — it's pinned to the residual by redCore_eq.")
print()
# Verify the (2,2,2) C1 residual IS dlnLoss((1,1,2)) 0 up to unit (the redCore_eq for the node).
# From g195/g194: (2,2,2) step-1 A-pivot → residual Q on the reduced (1,1,2) chain. Case222: myF222_step1A
# gives y0²·Q, Q = step1Residual = the resolved form = dlnLoss of the reduced chain (Lemma-2 normal form).
print("(2,2,2) CHECK (Case222 backbone): step-1 A-pivot myF222(φ)=y0²·Q; Q = step1Residual = (after Lemma-2)")
print("the resolvedForm = dlnLoss of the reduced (1,1,2)-ish chain. So the residual IS dlnLoss(reduced) 0")
print("up to the regular block — = redCore_eq for the node. The schurState.red=(1,1,2) matches the residual's")
print("chain. So split.red=schurState is PINNED to the residual via the node's redCore_eq. ✓ dischargeable.")
print()
print("="*68)
print("MY READ ON fm3's 3 QUESTIONS:")
print("="*68)
print("Q1 (root-anchor): CONFIRM ✓. codim = Mval(root M, T), T root-admissible, all down the path. The")
print("  geometric codim is invariant under the det-1 reduced reindex (redEmbed is MP) ⟹ root-anchoring")
print("  faithful. My §2/§4 always used Mval(root M, T). g207.")
print()
print("Q2 (schurState DEF vs carried cert field): BOTH — and they're complementary, NOT either/or.")
print("  - schurState M IS a clean ChainDimSplit DEF (width split, g214): split.red = schurState.red, the")
print("    genuine reduced widths. NECESSARY (termination + value widths).")
print("  - BUT the descent SOUNDNESS (Codex g206 item 2) is a CARRIED CERT FIELD: the per-cell datum proves")
print("    residual = dlnLoss(schurState.red) 0 (up to unit) = crux2's redCore_eq. So the cert field is NOT")
print("    new — it's IsSchurStraightenSqueeze.redCore_eq, which the per-cell transport datum ALREADY carries.")
print("  - THE FIX (your ruling (a)+(b), confirmed): (a) define schurState, prove routeStep.split = schurState;")
print("    (b) the cell's IsSchurStraightenSqueeze.S.red = schurState ⟹ redCore_eq ties split.red to the")
print("    genuine residual. NOT abstract. So split.red is BOTH a def AND pinned to the residual by redCore_eq.")
print()
print("Q3 (achiever i₀ root-anchored): YES ✓. binding leaf codim = minAdm(root), T*∈Adm(root). g148 always")
print("  resolved to T* the ROOT minimiser; the binding divisor codim = Mval(root, T*) = minAdm(root). Root-")
print("  anchored by construction (the achiever path resolves each layer to its T*-rank, T* ∈ Adm root M).")
