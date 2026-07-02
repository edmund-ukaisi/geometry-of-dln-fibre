import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# `DLNFibre.Core.Meta.Cited` — the citation cordon (attribute + core + `#audit_cited`)

The **accounted-axioms citation cordon**. External results we *cite* (monuments: resolution of
singularities, Aoyagi's RLCT computation, Watanabe's universal bound) are declared as Lean `axiom`s
tagged `@[cited "<source>"]`. Lean's kernel then auto-tracks every axiom dependency of every
declaration through `collectAxioms` (the `#print axioms` engine). For a declaration `D`:

```
UNACCOUNTED(D) = collectAxioms(D) − FOUNDATIONAL − CITED_TAGGED
```

where `FOUNDATIONAL = {propext, Classical.choice, Quot.sound}` (the standard-3 allowlist, explicit
and extensible below) and `CITED_TAGGED` is the set of `@[cited]`-tagged axioms. `D` is **proved
modulo declared citations** iff `UNACCOUNTED(D) = ∅`.

**Forget-proofness.** Forgetting the `@[cited]` tag does *not* hide a cite: `collectAxioms` still
returns the axiom (completeness is the kernel's, not ours), so it lands in `UNACCOUNTED`, so the gate
goes red — you are forced to tag+locate it (or prove it). The tag only *accounts*; it can never
*conceal*. Likewise a sneaked-in `sorry` becomes `sorryAx`, and (at this v4.29 pin) a `native_decide`
introduces a fresh per-invocation generated axiom (`…_native.native_decide.ax_…`, not
`Lean.ofReduceBool`) — neither is foundational nor `@[cited]`, so both surface as `UNACCOUNTED`. (The
foundational allowlist is exactly the standard-3; the other four axioms of Lean's standard set —
`sorryAx`, `Lean.trustCompiler`, `Lean.ofReduceBool`, `Lean.ofReduceNat` — are deliberately *not*
allowlisted, so anything resting on them goes red.)

**What green does / does not mean.** Green = "no unaccounted *axiom* in the imported gate environment."
It is not a whole-TCB audit: `unsafe`, `@[implemented_by]`, `@[extern]`, and plugins live outside the
axiom graph (the repo's style discipline bans them separately, and this project uses `decide +kernel`,
never `native_decide`). Nor does it vouch for the *honesty* of a cite's source string — the machine
enforces accounting; a human reviews that the source is the right theorem.

This module provides:
* the `@[cited "<source>"]` **parametric attribute** (source string as structured data);
* one reusable **core** (`auditDecl`) computing the `UNACCOUNTED` / `CITED` / non-foundational sets;
* the in-file `#audit_cited foo` command (mirrors `#print axioms`), the formaliser's inner loop.

The repo gate (`scripts/cited` / `lake exe cited-audit`) is a thin env-reading frontend over the same
core (`DLNFibre.Core.Meta.CordonAudit`). Policy: `docs/policies/citation-cordon.md`.
-/

open Lean Elab Command

namespace DLNFibre.Meta.Cited

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
      | _ => throwError "`@[cited]` expects a string literal source, e.g. `@[cited \"Aoyagi Thm 1\"]`"
  }

/-- The citation source of a `@[cited]`-tagged declaration, if any. -/
def getCitedSource? (env : Environment) (n : Name) : Option String :=
  citedAttr.getParam? env n

/-- Is `n` a `@[cited]`-tagged axiom? -/
def isCited (env : Environment) (n : Name) : Bool :=
  (getCitedSource? env n).isSome

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
named cite files that don't fit that shape (e.g. `…/AoyagiCited.lean`). Extend here (only here) when a
new located cite file is introduced. -/
def citedFileAllowlist : List Name :=
  [`DLNFibre.DLN.RLCT.AoyagiCited, `CordonFixtures.FixtureCited, `FixtureCited]

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

/-! ## The reusable core -/

/-- The verdict of auditing one declaration. -/
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

/-- **The reusable audit core (DRY).** For a declaration, `collectAxioms` its transitive axiom set,
subtract the foundational allowlist, split the remainder into `@[cited]` (accounted) vs `unaccounted`.
The single source of truth for both the `#audit_cited` command and the `cited-audit` executable. -/
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

end DLNFibre.Meta.Cited
