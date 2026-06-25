import DLNFibre.DLN.RLCT.Validate.CascadeAchiever

/-!
# `RouteMAchieverForce` — the achiever-realizability FORCING FIELD (fm3 #142, consumer-side)

The general-branch assembly's achiever leaf `i₀` (the leaf whose accumulated codims contain `minAdm`)
must be GENUINELY reached — the binding admissible `T*` must realize the achiever's orbit-stratum rank
pattern, NOT merely satisfy a vacuous `∃ i₀, minAdm ∈ codimsOf i₀` (which could hold without any cascade
realizing the stratum). The `RouteMBranchRead` doc-block (the #99/#125 seam) names this obligation as
EXACTLY `#121-(ii)`'s conclusion:

> `rankFn M (cascadeTuple M T) = achieverRankPattern M T`  for `T ∈ Adm M`.

At the time of `RouteMBranchRead` that conclusion referenced `achieverRankPattern`, a decl ABSENT on the
branch — so it was carried as a doc-deferred NAMED hypothesis, not a typed object. That blocker has FLIPPED:
the tie is now PROVEN and on-branch (`DLNFibre.DLN.RLCT.rankFn_cascadeTuple_eq_achieverRankPattern`, the
matrix-side of the #137 split). So the achiever-realizability is now a real **forcing field** — a typed
object the assembly consumes, carrying the GENUINE equality, NOT a placeholder.

**Forcing field, not producer field.** This is deliberately CONSUMER-side (a standalone object the
general-branch assembly takes), NOT a new field of `RouteMBranchRead`: that structure's fields are frozen
1:1 with `RouteStep.branch`, and the realizability is not part of the `RouteStep` term — it is the
non-vacuity CERTIFICATE the assembly demands of the binding leaf. The "forcing" is that
`RealizesAchiever` cannot be inhabited vacuously: its field IS the proven tie's conclusion at the binding
`T*`, so producing it forces the cascade to realize the achiever's stratum.
-/

open DLNFibre.Core

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The achiever-realizability forcing field.** For an admissible binding exponent vector `T ∈ Adm M`,
the witness that the cascade `cascadeTuple M T` GENUINELY realizes the achiever's orbit-stratum rank
pattern `achieverRankPattern M T` — the `#121-(ii)` conclusion as a typed object (`hT` the admissibility,
`realizes` the rank equality over the working field `k`). Inhabited ONLY by the proven tie
(`ofAdm`), so it cannot be satisfied vacuously: the assembly's binding leaf must carry this. -/
structure RealizesAchiever (k : Type*) [Field k] (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Prop where
  /-- The binding exponent vector is admissible. -/
  hT : T ∈ Adm M
  /-- The cascade at `T` realizes the achiever's orbit-stratum rank pattern (the genuine `#121-(ii)`
  equality — NOT a `⟨_, rfl⟩` membership). -/
  realizes : rankFn (k := k) M (cascadeTuple (k := k) M T) = achieverRankPattern M T

/-- **The forcing field is inhabited by the proven tie (and ONLY by it).** From admissibility
`T ∈ Adm M`, the `RealizesAchiever` certificate follows — its `realizes` field is exactly
`rankFn_cascadeTuple_eq_achieverRankPattern`. This is the genuine non-vacuity: the achiever leaf is reached
because the cascade's rank pattern IS the achiever's stratum, proven via the `Q3` window-min collapse
(fm3 `#121-(i)` caveat b), not assumed. -/
theorem RealizesAchiever.ofAdm {k : Type*} [Field k] (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ)
    (hT : T ∈ Adm M) : RealizesAchiever k M T :=
  { hT := hT
    realizes := rankFn_cascadeTuple_eq_achieverRankPattern M T hT }

/-- The forcing field's `realizes` is genuinely the achiever pattern (re-export for the assembly): the
binding leaf's rank pattern equals `achieverRankPattern M T`, the column-constant orbit-stratum completion
(`i<j ↦ ρ_j`, `i=j ↦ M_i`, else `0`). -/
theorem RealizesAchiever.rank_eq {k : Type*} [Field k] {M : Fin (L + 1) → ℕ} {T : Fin L → ℕ}
    (r : RealizesAchiever k M T) :
    rankFn (k := k) M (cascadeTuple (k := k) M T) = achieverRankPattern M T :=
  r.realizes

end DLNFibre.DLN.RLCT
