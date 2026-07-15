import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# `Meta.Cordon` — the citation cordon (attributes + core + `#audit_cited` / `#audit_blueprint`)

The **accounted-axioms citation cordon**, plus a **blueprint-leak** guard. Two disciplines, one
mechanism, both riding Lean's own kernel dependency graph (`collectAxioms` / `getUsedConstants` — the
`#print axioms` engine and the constant-reference graph):

* **Cited accounting.** Any external result one *cites* — here the Aoyagi `rlct = ½·codim` DLN
  equality (`RlctInterface.cited_aoyagi_dln`) — is a Lean `axiom` tagged `@[cited "<source>"]`.
  DLNFibre's definition of done is **NOT zero-cite**: that Aoyagi equality is a *legitimate* cited
  interface (Watanabe's universal bound + Aoyagi's exact DLN computation), so the gate here certifies
  **proved modulo declared citations** — no *unaccounted* axiom has crept in, every cite is tagged and
  located — rather than the stricter zero-cite bar of the sibling `qs` harness (see
  `docs/policies/citation-cordon.md` § "difference from qs"). For a declaration `D`:

  ```
  UNACCOUNTED(D) = collectAxioms(D) − FOUNDATIONAL − CITED_TAGGED
  ```

  where `FOUNDATIONAL = {propext, Classical.choice, Quot.sound}` (the standard-3 allowlist, explicit
  and extensible below) and `CITED_TAGGED` is the set of `@[cited]`-tagged axioms. `D` is **proved
  modulo declared citations** iff `UNACCOUNTED(D) = ∅`.

* **Blueprint-leak guard.** A declaration tagged `@[blueprint]` is a **forecast** — a sketch,
  placeholder, or map-node stub that is *not yet banked*. The rule (from the expedition discipline:
  *banked never consumes a forecast*) is that a **banked** (non-`@[blueprint]`) result must not
  transitively rest on any forecast. For a declaration `D` not itself `@[blueprint]`:

  ```
  BLUEPRINT_LEAKS(D) = { @[blueprint]-tagged constants in D's transitive constant dependencies }
  ```

  `D` is **banked-clean** iff `BLUEPRINT_LEAKS(D) = ∅`. Unlike the cited accounting (which walks
  *axioms*), this walks the full **constant-reference** graph (types *and* values, every declaration
  kind — the `WalkDecls` edge set), because a forecast can be any `def`/`theorem`/`axiom`, not only an
  axiom.

**Forget-proofness (both halves).** Forgetting the `@[cited]` tag does *not* hide a cite:
`collectAxioms` still returns the axiom (completeness is the kernel's, not ours), so it lands in
`UNACCOUNTED` and the gate goes red — you are forced to tag+locate it (or prove it). The tag only
*accounts*; it can never *conceal*. Likewise the `@[blueprint]` tag *accounts* a forecast; the leak
walk reads the kernel's constant-reference graph, so a banked decl that reaches a forecast surfaces
whether or not anyone remembered to think of it as one. A sneaked-in `sorry` becomes `sorryAx`, and (at
this v4.29 pin) a `native_decide` introduces a fresh per-invocation generated axiom — neither is
foundational nor `@[cited]`, so both surface as `UNACCOUNTED`.

**What green does / does not mean.** Green = "no unaccounted *axiom* in scope, all cites located, no
banked decl rests on a forecast." It is not a whole-TCB audit: `unsafe`, `@[implemented_by]`,
`@[extern]`, and plugins live outside the axiom graph (the repo's style discipline bans them
separately). Nor does it vouch for the *honesty* of a cite's source string, nor the *consistency* of a
cited axiom — the machine enforces accounting; a human reviews that the source is the right theorem and
that the axiom is not vacuous/inconsistent (`docs/policies/citation-cordon.md` § consistency review).

This module provides:
* the `@[cited "<source>"]` **parametric attribute** (source string as structured data);
* the `@[blueprint]` **tag attribute** (a plain tag on any declaration — `def`s included);
* one reusable **cited core** (`auditDecl`) computing the `UNACCOUNTED` / `CITED` / non-foundational
  sets, and the **blueprint traversal** (`collectBlueprintBatch` / `blueprintDepsOf`);
* the in-file `#audit_cited foo` and `#audit_blueprint foo` commands (mirror `#print axioms`).

The repo gate (`scripts/cordon` / `lake exe cordon-audit`) is a thin env-reading frontend over the same
core (`Meta.CordonAudit`). Policy: `docs/policies/citation-cordon.md`.
-/

open Lean Elab Command

namespace Meta.Cordon

/-! ## The foundational allowlist (the standard-3, explicit + extensible) -/

/-- The **foundational axiom allowlist**: the three axioms of classical Lean/Mathlib that every
"axiom-clean" declaration is permitted to rest on. Explicit and in one place; extend here (and only
here) if a genuinely-foundational Mathlib axiom must be added — never to silence a real cite. -/
def foundationalAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Membership test against the foundational allowlist. -/
def isFoundational (n : Name) : Bool :=
  foundationalAxioms.contains n

/-! ## The `@[cited "<source>"]` parametric attribute -/

/-- The concrete syntax `@[cited "<source>"]`: the attribute keyword `cited` followed by a mandatory
string-literal source. Registered in the `attr` category (mirrors Mathlib's `@[stacks TAG "…"]`). -/
syntax (name := cited) "cited" str : attr

/-- The `@[cited "<source>"]` **parametric attribute**: tags a cited `axiom` with its citation source
as *structured data* (a `String`), so the per-headline manifest is auto-derived from the same store
the accounting reads. Applied to each cited `axiom` (which must live in a located `Cited` file — the
gate's location check). -/
initialize citedAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `cited
    descr := "marks an axiom as a cited external result, carrying its citation source string"
    getParam := fun decl stx => do
      -- `@[cited]` may only tag an `axiom` (a cite is an assumed external result, not a proof).
      unless (← getEnv).find? decl |>.any (·.isAxiom) do
        throwError "`@[cited]` may only tag a cited external result declared as `axiom` — `{decl}` is not one"
      match stx with
      | `(attr| cited $s:str) =>
        let src := s.getString
        -- A cite MUST carry a real source: the accounting is only meaningful if a human can review
        -- the source string (green ≠ source-honesty). Reject an empty/whitespace-only source.
        if src.all Char.isWhitespace then
          throwError "`@[cited]` requires a non-empty citation source string (author, theorem, section)"
        pure src
      | _ => throwError "`@[cited]` expects a string literal source, e.g. `@[cited \"Aoyagi 2019, DLN RLCT\"]`"
  }

/-- The citation source of a `@[cited]`-tagged declaration, if any. -/
def getCitedSource? (env : Environment) (n : Name) : Option String :=
  citedAttr.getParam? env n

/-- Is `n` a `@[cited]`-tagged axiom? -/
def isCited (env : Environment) (n : Name) : Bool :=
  (getCitedSource? env n).isSome

/-! ## The `@[blueprint]` tag attribute

A **plain** tag (no source), applicable to **any** declaration (`def`/`theorem`/`axiom`/…). It marks a
*forecast* — a not-yet-banked sketch/placeholder/map-node stub. The banked-never-consumes-a-forecast
rule is mechanised by the blueprint-leak walk below. Contrast `@[cited]`, which is axiom-only and
carries a mandatory source. -/

/-- The `@[blueprint]` tag: marks a declaration as a blueprint *forecast* — a sketch/placeholder not
yet banked. A banked (non-`@[blueprint]`) result must not transitively depend on one. -/
initialize blueprintAttr : TagAttribute ←
  registerTagAttribute `blueprint
    "marks a declaration as a blueprint forecast (not yet banked); a banked result must not transitively depend on one"

/-- Is `n` a `@[blueprint]`-tagged declaration (a forecast)? -/
def isBlueprint (env : Environment) (n : Name) : Bool :=
  blueprintAttr.hasTag env n

/-! ## The source-module + location check -/

/-- The source module (as a `Name`) where declaration `n` lives, `none` if in the current module. -/
def sourceModule? (env : Environment) (n : Name) : Option Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => env.header.mainModule

/-- **The located-cite allowlist** (explicit + extensible, in one place). A cited axiom must be
declared in one of these files (matched by exact *module name*, not a filesystem path — module
provenance is what the `Environment` gives us). The default rule below also accepts any module whose
last component is exactly `"Cited"` (the generic `…/Cited.lean` convention); this allowlist adds the
named cite files that don't fit that shape. Extend here (only here) when a new located cite file is
introduced (e.g. `DLNFibre.DLN.RlctInterface` if the Aoyagi cite is not moved to a `…Cited` module). -/
def citedFileAllowlist : List Name :=
  [`CordonFixtures.FixtureCited, `FixtureCited]

/-- **The located-cite rule.** A cited axiom must be declared in a *located cite file*: either its
source-module's last component is exactly `"Cited"` (the generic `…/Cited.lean` convention), or the
whole source-module name is in `citedFileAllowlist`. Module identity (not a source path) is the clean
in-Lean invariant. This is the *location* half of the gate's tag+location invariant. -/
def isInCitedFile (env : Environment) (n : Name) : Bool :=
  match sourceModule? env n with
  | some m =>
    citedFileAllowlist.contains m ||
      (match m.components.getLast? with
        | some (Name.str _ s) => s == "Cited"
        | _ => false)
  | none => false

/-! ## The reusable cited core -/

/-- The verdict of auditing one declaration for cited/unaccounted axioms. -/
structure AuditResult where
  /-- The declaration audited. -/
  decl : Name
  /-- Non-foundational axioms this decl transitively depends on (sorted). -/
  nonFoundational : Array Name
  /-- The `@[cited]`-tagged axioms this decl uses, with their sources (sorted by name). -/
  cited : Array (Name × String)
  /-- The **unaccounted** axioms: non-foundational, not `@[cited]` (sorted). Empty ⟺ proved-mod-cites. -/
  unaccounted : Array Name
  deriving Inhabited

/-- Is this decl proved modulo declared citations? (`unaccounted = ∅`.) -/
def AuditResult.ok (r : AuditResult) : Bool := r.unaccounted.isEmpty

/-! ### The constant-reference edge set (shared by both walks)

`getUsedConstants` on the type (and value, per declaration kind) is the kernel's constant-reference
graph — the same edges `collectAxioms` follows for axioms, generalised to *all* constants for the
blueprint walk. Matches the `WalkDecls` `axEdges`/`reachAxioms` reachability exactly. -/

/-- The constants referenced by one declaration's type and (where present) value — the dependency
edges of the constant-reference graph. Mirrors `Lean.collectAxioms`'s per-kind traversal. -/
def usedConstantsOf (ci : ConstantInfo) : Array Name :=
  match ci with
  | .axiomInfo v  => v.type.getUsedConstants
  | .defnInfo v   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v    => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _   => #[]
  | .ctorInfo v   => v.type.getUsedConstants
  | .recInfo v    => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-! ### Batched axiom collection (one shared traversal over many roots)

`Lean.collectAxioms` starts a fresh `visited` set per call, so auditing a whole library decl-by-decl
re-traverses the shared (Mathlib) dependency graph once per declaration — O(decls × depth), far too
slow for the repo gate. `collectAxiomsBatch` traverses from *all* roots with a **single** shared
`visited` set, so each constant is visited once total — O(reachable constants). The result is the
*union* of the roots' transitive axioms; per-root attribution (for a violation listing) is a separate,
rarely-needed pass. Same completeness as `collectAxioms` (same kernel constant graph). -/

/-- One shared traversal collecting the union of transitive axioms of all `roots`. Iterative
(explicit worklist) so it is not `partial` — `visited` bounds it (each constant pushed once). -/
def collectAxiomsBatch (env : Environment) (roots : Array Name) : Array Name := Id.run do
  let kenv := env.checked.get
  let mut visited : NameSet := {}
  let mut axioms : Array Name := #[]
  let mut stack : Array Name := roots
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    unless visited.contains c do
      visited := visited.insert c
      match kenv.find? c with
      | some (.axiomInfo v) =>
        axioms := axioms.push c
        stack := stack ++ v.type.getUsedConstants
      | some (.defnInfo v)   => stack := (stack ++ v.type.getUsedConstants) ++ v.value.getUsedConstants
      | some (.thmInfo v)    => stack := (stack ++ v.type.getUsedConstants) ++ v.value.getUsedConstants
      | some (.opaqueInfo v) => stack := (stack ++ v.type.getUsedConstants) ++ v.value.getUsedConstants
      | some (.quotInfo _)   => pure ()
      | some (.ctorInfo v)   => stack := stack ++ v.type.getUsedConstants
      | some (.recInfo v)    => stack := stack ++ v.type.getUsedConstants
      | some (.inductInfo v) => stack := (stack ++ v.type.getUsedConstants) ++ v.ctors.toArray
      | none                 => pure ()
  pure axioms

/-! ### Batched blueprint collection (the leak walk)

The blueprint analogue of `collectAxiomsBatch`, over the full constant-reference graph. Each traversal
descends *through* forecast nodes (a forecast whose own proof rests on a deeper forecast is reported
too — completeness), collecting every `@[blueprint]`-tagged constant reachable from the (non-forecast)
roots. `collectBlueprintBatch` gives the union over all roots in one shared traversal (the fast, green
path); `blueprintDepsOf` gives per-root attribution (the rare red path). -/

/-- The union of `@[blueprint]`-tagged constants reachable from any of `roots`, in one shared
traversal (O(reachable constants)). The roots themselves are excluded from the result (a root is a
*banked* decl whose forecast dependencies we want). Iterative so it is not `partial`. -/
def collectBlueprintBatch (env : Environment) (roots : Array Name) : Array Name := Id.run do
  let rootSet : NameSet := roots.foldl (·.insert ·) {}
  let mut visited : NameSet := {}
  let mut found : Array Name := #[]
  let mut stack : Array Name := roots
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    unless visited.contains c do
      visited := visited.insert c
      if isBlueprint env c && !rootSet.contains c then
        found := found.push c
      match env.find? c with
      | some ci => stack := stack ++ usedConstantsOf ci
      | none => pure ()
  pure (found.qsort Name.lt)

/-- The `@[blueprint]`-tagged constants in `root`'s transitive constant dependencies (`root` itself
excluded — per-root attribution for the leak listing). Iterative; sorted. -/
def blueprintDepsOf (env : Environment) (root : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut found : Array Name := #[]
  -- Seed from `root`'s direct dependencies so `root` itself is never counted as its own leak.
  let mut stack : Array Name :=
    match env.find? root with
    | some ci => usedConstantsOf ci
    | none => #[]
  while h : stack.size > 0 do
    let c := stack[stack.size - 1]
    stack := stack.pop
    unless visited.contains c || c == root do
      visited := visited.insert c
      if isBlueprint env c then
        found := found.push c
      match env.find? c with
      | some ci => stack := stack ++ usedConstantsOf ci
      | none => pure ()
  pure (found.qsort Name.lt)

/-- **The reusable audit core (DRY).** For a declaration, `collectAxioms` its transitive axiom set,
subtract the foundational allowlist, split the remainder into `@[cited]` (accounted) vs `unaccounted`.
The single source of truth for both the `#audit_cited` command and the `cordon-audit` executable. -/
def auditDecl [Monad m] [MonadEnv m] (decl : Name) : m AuditResult := do
  let env ← getEnv
  let axs ← collectAxioms decl
  let nonFoundational := (axs.filter (fun a => !isFoundational a)).qsort Name.lt
  let mut cited : Array (Name × String) := #[]
  let mut unaccounted : Array Name := #[]
  for a in nonFoundational do
    match getCitedSource? env a with
    | some src => cited := cited.push (a, src)
    | none => unaccounted := unaccounted.push a
  pure { decl, nonFoundational, cited, unaccounted }

/-! ## Frontend 1 — the `#audit_cited foo` command (mirrors `#print axioms`) -/

/-- Render an `AuditResult` as human-readable `MessageData`. -/
def AuditResult.toMessageData (r : AuditResult) : MessageData :=
  let citedLine :=
    if r.cited.isEmpty then m!""
    else
      let items := r.cited.toList.map (fun (n, src) => m!"{MessageData.ofConstName n} [{src}]")
      m!"\n  cited: {MessageData.joinSep items ", "}"
  if r.unaccounted.isEmpty then
    if r.cited.isEmpty then
      m!"'{r.decl}' is FORMALISED (no unaccounted axioms; rests only on the foundational allowlist)"
    else
      m!"'{r.decl}' is proved modulo declared citations (UNACCOUNTED = ∅){citedLine}"
  else
    let bad := r.unaccounted.toList.map MessageData.ofConstName
    m!"'{r.decl}' has UNACCOUNTED axioms: {MessageData.joinSep bad ", "}\n\
       → prove each, or `@[cited \"…\"]` it and move to a `…/Cited.lean` file.{citedLine}"

/-- **`#audit_cited foo`** — the in-file cordon report, mirroring `#print axioms`. Shows `foo`'s
unaccounted axioms (which redden the gate) and its `@[cited]` dependencies with sources. The
formaliser's inner loop: run it right where you are proving. -/
syntax (name := auditCitedCmd) "#audit_cited " ident : command

@[command_elab auditCitedCmd]
def elabAuditCited : CommandElab
  | `(#audit_cited $id:ident) => do
    let cs ← liftCoreM <| realizeGlobalConstWithInfos id
    for c in cs do
      let r ← auditDecl c
      logInfo r.toMessageData
  | _ => throwUnsupportedSyntax

/-! ## Frontend 2 — the `#audit_blueprint foo` command (the blueprint-leak inner loop) -/

/-- **`#audit_blueprint foo`** — shows the `@[blueprint]` forecasts `foo` transitively rests on. If
`foo` is itself `@[blueprint]`, it says so (blueprint-internal is permitted). If `foo` is banked and
the set is non-empty, those are leaks — a banked result resting on a forecast. -/
syntax (name := auditBlueprintCmd) "#audit_blueprint " ident : command

@[command_elab auditBlueprintCmd]
def elabAuditBlueprint : CommandElab
  | `(#audit_blueprint $id:ident) => do
    let cs ← liftCoreM <| realizeGlobalConstWithInfos id
    let env ← getEnv
    for c in cs do
      let deps := blueprintDepsOf env c
      if isBlueprint env c then
        if deps.isEmpty then
          logInfo m!"'{c}' is a @[blueprint] forecast (rests on no other forecast)"
        else
          let items := deps.toList.map MessageData.ofConstName
          logInfo m!"'{c}' is a @[blueprint] forecast resting on: {MessageData.joinSep items ", "} (blueprint-internal — permitted)"
      else if deps.isEmpty then
        logInfo m!"'{c}' is banked-clean (rests on no @[blueprint] forecast)"
      else
        let items := deps.toList.map MessageData.ofConstName
        logInfo m!"'{c}' LEAKS @[blueprint] forecasts: {MessageData.joinSep items ", "}\n\
           → a banked result must not rest on a forecast: prove/ban them, or `@[blueprint]` this decl."
  | _ => throwUnsupportedSyntax

end Meta.Cordon
