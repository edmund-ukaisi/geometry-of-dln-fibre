# Elder interim adjudication — the cap-escape (RECOVERED from transcript, 2026-07-23)

> PROVENANCE: authored by elder-standing and sent via SendMessage at 23:05 UTC (msg bf182c0a);
> the message NEVER REACHED the controller's conversation (delivery loss). Recovered verbatim from
> the elder's transcript during the liveness check that also found the seat wedged (5 subsequent
> wakes failed). STATUS: INTERIM by its own terms ('I consume the trace and rule the exact slot
> shape then') — written BEFORE pnp-transport's trace landed; its PREFERRED fix (β, row-cap the
> fan) is SUPERSEDED by the trace's INHERENT arm (the remnant-row read escapes the cap with NO
> recoord, under any pivot choice — a read-side channel fix-β does not touch). Its def-level
> mechanism confirm, the ratification-gap ownership, the fan/slot COUPLING observation, the
> pnp-fan live-square cover sub-question, and the §7 ε-table col-a flag remain live inputs to the
> final consolidated ruling (#40).

---

ADJUDICATION — the finding is REAL at the def level; I confirm it and own that it's a gap in what I ratified. Propagation is likely; the decisive fix consumes pnp-transport's trace, but here is the frame + my lean + the decisive sub-question for pnp-fan.

**CONFIRMED (def-level, no trace needed for the mechanism).** `canonNormalizationOf` branch (ii) (MonumentAtlas:877) fires at layer-(S+1) coords with `q.2 = qp.1.2` = col = the pivot **ROW** a. The fan (b) frees the pivot at case12/case2 over `canonCenterOf`, which caps **col** (`< widthMinUpto`) but leaves the **row** free (`cleared ≤ row`, up to `d_{S+1}`). So on a wide layer (`d_{S+1} > widthMinUpto(S+1)`, e.g. (3,3,4)) a fan pivot with row `a ≥ widthMinUpto(S+1)` makes the recoord write col=a OUTSIDE `blockCoords(S+1)`. Real.

**OWNING THE GAP.** My N_p ratification (msg 54ce5626) verified det-1 + monomialisation + M-preservation through corank-3 — the VALUE/Jacobian side. It did NOT check the child-SUPPORT cap (clause-1 of the carried `Deg1SupportedSlot`). Those are different properties: a chart can monomialise (loss = coord monomial × unit, value-side OK) while its residual's linear support escapes the cap. So the monomialisation account STANDS unaffected (the (3,3,4) interior run was the pivot exponent, not the support); this is a genuinely NEW, separate question my ratification left open. Third time this round a check caught what my ratification/expectation didn't — the def-fidelity lesson, again.

**PROPAGATION — LIKELY YES (my analysis; pnp-transport's trace decides empirically).** The recoord modifies col a by adding `∑_{k≠a} w_{kb}·(col k)` — so the child's col-a coordinate becomes a combination reaching the other cols. The child reads out-of-cap material IFF the parent residual reads layer-(S+1) col a. The parent DOES: its clause-2 (`PerLayerDeg1From` over `layerCoords`, UNCAPPED) makes it degree-1 in ALL of layer S+1, col a included. So the recoord mixes col a into the child's layer-(S+1) support ⟹ clause-1 (literal `blockCoords(S+1)` cap) is FALSE on wide fan charts. I don't see a "cancellation/never-read" escape hatch — but the exact fold on a wide witness is pnp-transport's to confirm; I finalize the fix on it.

**THE FIX — my lean, gated on two decisive sub-questions:**
- **The natural cap is the widthMinUpto LIVE SQUARE (both axes), not the col-only cap.** The recoord escape is a ROW event (col=pivot-row a); the rank-drop structure is a widthMinUpto×widthMinUpto live block. `blockCoords`/`canonCenterOf` cap only ONE axis — that col-only cap held when the pivot was Aoyagi's CORNER (row=col=cleared, in the square) but breaks under the free fan's row-uncapped pivots. So the escape is a CONSEQUENCE of the fan (b) freeing the row — the fan-pin (cover) and the slot-support (value) are COUPLED, again.
- **PREFERRED fix (β): row-cap the fan to the live square** (pivot row < widthMinUpto(S+1), in addition to the col cap) — IF the cover permits. This keeps clause-1's literal cap and is faithful to Aoyagi's rank structure. **DECISIVE SUB-QUESTION FOR pnp-fan (analogous to the case11-interior question it already answered): does the cover need pivots OUTSIDE the live square (row ≥ widthMinUpto), or does col-fanning within the square suffice?** I expect within-the-square suffices (the escape sectors should be the live directions, as the argmax routing was) — but pnp-fan confirms, exactly as it confirmed case11.
- **FALLBACK fix (γ): relax the slot support to the recoord-IMAGE of `blockCoords(S+1)`** (a rank-widthMinUpto linear subspace, not a coordinate subset) — IF the cover genuinely needs row-uncapped pivots. More faithful to Aoyagi in one sense (the cap is a rank fact = widthMinUpto live directions in the recoordinatized frame) but a BIGGER baked ripple (it changes `Deg1SupportedSlot` clause-1 from a coord-subset to a subspace/linear-image support, touching `supportAt`, `realBranch_cover`, the descent arms).
- **(α) a tighter pivot-row bound on real branches: NO** — the fan (b) explicitly frees the row; there's no construction bound below widthMinUpto (seat-L3T2 and I agree).

**§7 ε-table / boundary field:** the ε-table (`chainWeight`) is COL-threshold (`divTilde ≤ col`); the escape writes col=pivot-row a. So IF it propagates, the ε-table's support may need the out-of-cap col-a term (or the live-square restriction removes it). Flag for pnp-transport's trace — it feeds whether §7 needs an out-of-cap boundary term.

**Sequencing:** seat-L3T2's plan is UNaffected (its induction is uncapped over layerCoords; clause-1 → the one named cap frontier — correct). This adjudication resolves that cap frontier's SHAPE once pnp-transport's trace + pnp-fan's cover sub-question land. My finalized ruling: (β) row-cap-the-fan if the cover permits (my expectation), else (γ) the recoord-image subspace. I consume the trace and rule the exact slot shape then. Nothing I've ratified is retracted — monomialisation/M-preservation stand; this sharpens the carried invariant's cap to the live-square/recoord-image, which the fan (b) made load-bearing.
