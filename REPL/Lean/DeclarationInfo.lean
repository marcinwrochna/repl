import Lean

namespace Lean.Elab


instance : ToJson String.Pos where
  toJson n := toJson n.byteIdx

instance : ToJson String.Range where
  toJson r := toJson (r.start, r.stop)



/-- Information about the syntax of a declaration. -/
structure DeclarationInfo where
  modifiers: Array String  -- Array of the six modifiers, as raw strings that got parsed as:
  -- * docComment: like '/-- Comment -/'
  -- * attributes: like '@[simp]'
  -- * visibility: 'private' or 'protected' or ''
  -- * 'noncomputable' or ''
  -- * 'unsafe' or ''
  -- * 'partial' or 'nonrec' or ''
  -- Does not include modifiers implied by the surrounding scope.
  -- See also: https://lean-lang.org/doc/reference/latest/Definitions/Modifiers/#declaration-modifiers

  kind: String  -- The Lean.Parser.Command.kind, like 'theorem'.
  -- Note that lemmas (and any other similar macros) will be seen as theorems; non-inductive classes as structures.
  -- One of: theorem/abbrev/definition/opaque/instance/example/axiom/inductive/classInductive/structure.

  isDefLike: Bool -- Is it theorem/abbrev/definition/opaque/instance/example rather than axiom/inductive/classInductive/structure.

  id: Name  -- ident as used in the declaration syntax.
  -- May be .anonymous like for 'example' declarations.
  -- Does not include universe parameters like in 'foo.{u,v}'.

  fullName: Name -- The full name of the declaration, including containing namespaces.
  -- When `id` and `shortName` are anonymous, this may be the namespace name only.

  shortName: Name -- Short name as used in recursion.
  -- Usually the same as id, but excludes macro scopes and includes namespaces for protected declarations.

  declRange: Option String.Range -- Range of the whole declaration, including modifiers and id.

  typeByteRange: Option String.Range -- Range that got parsed as the signature's type term (after ':').
  -- For theorems and similar this is the theorem statement.
  -- Does not include any binders like '(n : Nat)'.
  -- See also: https://lean-lang.org/doc/reference/latest//Definitions/Headers-and-Signatures/#parameter-syntax
  -- Optional when kind is "abbrev", "def", "example", "inductive", "classInductive".
  -- No support when kind is "structure".

  valByteRange: Option String.Range -- Range of decl value (with ':=' and with 'where' clauses).
  -- For theorems, this is the proof (including 'by' for tactic proofs).
  -- May begin with '|' when its a match expression or with 'where ' sometimes, instead of ':='.
  -- Does not include 'deriving foo' trailing some definitions.
  -- Not present when kind is "abbrev" or "axiom".
  -- No support when kind "inductive", "classInductive", or "structure".

  valBodyByteRange: Option String.Range -- Byte range of value's body (w/o ':=' nor 'where' clauses).

deriving ToJson


-- Same as ContextInfo.runCoreM, but we pass the fileMap.
def ContextInfo.runCoreM' (info : ContextInfo) (x : CoreM α) : IO α := do
  (·.1) <$>
    (withOptions (fun _ => info.options) x).toIO
      { currNamespace := info.currNamespace, openDecls := info.openDecls
        fileName := "<InfoTree>", fileMap := info.fileMap }
      { env := info.env, ngen := info.ngen }


-- A version of `Lean.Elab.elabModifiers` without monads; attributes are ignored as they require more context.
def elabModifiers' (stx : TSyntax ``Parser.Command.declModifiers) : IO Modifiers := do
  let docCommentStx := stx.raw[0]
  let attrsStx      := stx.raw[1]
  let visibilityStx := stx.raw[2]
  let noncompStx    := stx.raw[3]
  let unsafeStx     := stx.raw[4]
  let recKind       :=
    if stx.raw[5].isNone then
      RecKind.default
    else if stx.raw[5][0].getKind == ``Parser.Command.partial then
      RecKind.partial
    else
      RecKind.nonrec
  let docString? := docCommentStx.getOptional?.map TSyntax.mk
  let visibility ← match visibilityStx.getOptional? with
    | none   => pure Visibility.regular
    | some v =>
      let kind := v.getKind
      if kind == ``Parser.Command.private then pure Visibility.private
      else if kind == ``Parser.Command.protected then pure Visibility.protected
      else throw $ IO.userError "unexpected visibility modifier"
  let attrs := #[]  -- Can't elaborate attributes without significantly more context.
  return {
    stx, docString?, visibility, recKind, attrs,
    isUnsafe        := !unsafeStx.isNone
    isNoncomputable := !noncompStx.isNone
  }


-- A version of `Lean.Elab.mkDeclName` without monads: does not protect names nor check shadowing.
-- Env is only used for env.mainModule in `mkPrivateName`.
def mkDeclName' (currNamespace : Name) (visibility : Visibility) (shortName : Name) (env : Environment) : IO (Name × Name) := do
  let mut shortName := shortName
  let mut currNamespace := currNamespace
  let view := extractMacroScopes shortName
  let name := view.name
  let isRootName := (`_root_).isPrefixOf name
  if name == `_root_ then
    throw $ IO.userError "invalid declaration name `_root_`, `_root_` is a prefix used to refer to the 'root' namespace"
  let declName := if isRootName then { view with name := name.replacePrefix `_root_ Name.anonymous }.review else currNamespace ++ shortName
  if isRootName then
    let .str p s := name | throw $ IO.userError "invalid declaration name '{name}'"
    shortName := Name.mkSimple s
    currNamespace := p.replacePrefix `_root_ Name.anonymous
  match visibility with
  | Visibility.private => return (mkPrivateName env declName, shortName)
  | Visibility.protected =>
    match currNamespace with
    | .str _ s => return (declName, Name.mkSimple s ++ shortName)
    | _ =>
      if shortName.isAtomic then
        throw $ IO.userError "protected declarations must be in a namespace"
      return (declName, shortName)
  | _ => return (declName, shortName)


def getDeclInfo (info : CommandInfo) (ctx : ContextInfo) : IO DeclarationInfo := do
  let stx : Lean.Syntax := info.stx
  if (! stx.isOfKind ``Lean.Parser.Command.declaration) then
    throw (IO.userError s!"Unexpected Syntax.kind for declaration: {stx.getKind}")
  let (modifiersNode, declNode) ← match stx with
    | .node _ _ #[modifiersNode, declNode] => pure (modifiersNode, declNode)
    | _ => throw (IO.userError s!"Unexpected Syntax for declaration: {stx.reprint}")

  -- Modifiers:
  if (! modifiersNode.isOfKind ``Lean.Parser.Command.declModifiers) then
    throw (IO.userError s!"Unexpected modifiers kind for declaration: {modifiersNode.getKind}")
  -- Get the six modifier kinds as six separate strings.
  let modifiers := modifiersNode.getArgs.map (fun m => (m.reprint.getD "").trim)
  let modifiers' ← elabModifiers' ⟨modifiersNode⟩

  -- Kind/keyword: strip 'Lean.Parser.Command.' from the kind Name.
  let kind := match declNode.getKind with | .str _ s => s | _ => ""  --

  -- Id/name:
  let declIdNode? := declNode.getArgs.find? (·.isOfKind ``Lean.Parser.Command.declId)
  -- Skip universe parameters.
  let identSyntax? := declIdNode?.map (fun x => (x.getArg 0))
  let id := identSyntax?.elim Lean.Name.anonymous (·.getId)
  let (fullName, shortName) ← mkDeclName' ctx.currNamespace modifiers'.visibility id ctx.env

  -- Signature/type:
  let declSigNode := declNode.getArgs.find? (fun x => x.isOfKind ``Lean.Parser.Command.declSig || x.isOfKind ``Lean.Parser.Command.optDeclSig)
  let declSigTypeSpec := declSigNode.bind (·.getArgs.back?)  -- Skip any number of binders.
  let declSigType := declSigTypeSpec.bind (·.getArgs.back?)  -- Skip the ':' token.

  -- Value/body: we only care about normal theorem proofs, so we use declBody in declValSimple.
  -- (we ignore equational definitions with '|' match patterns, and 'where' declarations).
  let declVal := declNode.getArgs.find? (fun x =>
    x.isOfKind ``Lean.Parser.Command.declValSimple ||
    x.isOfKind ``Lean.Parser.Command.declValEqns ||
    x.isOfKind ``Lean.Parser.Command.whereStructInst)
  let declValSimple := declNode.getArgs.find? (·.isOfKind ``Lean.Parser.Command.declValSimple)
  let declBody := declValSimple.bind (·.getArg 1)

  let declRange ← ContextInfo.runCoreM' ctx (Lean.Elab.getDeclarationRange? stx)
  let declRange: Option String.Range := declRange.map
    fun r => ⟨ctx.fileMap.ofPosition r.pos, ctx.fileMap.ofPosition r.endPos⟩

  pure {
    modifiers := modifiers
    kind := kind
    isDefLike := Lean.Elab.Command.isDefLike declNode
    id := id
    fullName := fullName
    shortName := shortName
    declRange := declRange
    typeByteRange := (declSigType.getD Syntax.missing).getRange?
    valByteRange := (declVal.getD Syntax.missing).getRange?
    valBodyByteRange := (declBody.getD Syntax.missing).getRange?
    -- rawType := declSigType.bind Lean.Syntax.reprint
    -- rawBody := declBody.reprint
  }


-- == Previous attempts at getting a full name. ==

-- -- Mimic the initial part of elabDeclaration to get modifier and declId data.
-- This actually doesn't work well, because:
-- * we don't have levelNames, varDecls, ... in the ContextInfo;
-- * elaboration modifies state and checks that the declaration is not already present, for example.
-- def elabDeclId (stx: Syntax) : Command.CommandElabM (DefView × ExpandDeclIdResult) := do
--   let modifiers : TSyntax ``Parser.Command.declModifiers := ⟨stx[0]⟩
--   let modifiers ← elabModifiers modifiers
--   let view ← Lean.Elab.Command.mkDefView modifiers stx[1]
--   let declId ← Lean.Elab.Command.runTermElabM fun vars => do
--     Term.expandDeclId (← getCurrNamespace) (← Lean.Elab.Term.getLevelNames) view.declId view.modifiers
--   pure (view, declId)

-- def runCommandElab (cmd : Command.CommandElabM α) (ctx: ContextInfo) : IO α := do
--   let cmdContex : Elab.Command.Context :=
--     { fileName := "", fileMap := ctx.fileMap, snap? := none, cancelTk? := none }
--   let cmdState := (Elab.Command.mkState ctx.env {} ctx.options)
--   let cmdState := { cmdState with scopes := [{
--     header := "",
--     opts := ctx.options,
--     currNamespace := ctx.currNamespace,
--     openDecls := ctx.openDecls,
--     -- Note we don't have info about levelNames, varDecls, includedVars, omittedVars, and isNoncomputable here.
--   }] }
--   let cmdStateRef ← IO.mkRef { cmdState with messages := .empty, traceState := {}, snapshotTasks := #[] }
--   match ← EIO.toIO' (cmd.run cmdContex cmdStateRef) with
--   | .ok result => pure result
--   | .error (Exception.error _ msg) => do throw (IO.userError (← msg.toString))
--   | .error (Exception.internal id _) => do throw (IO.userError <| "internal exception #" ++ toString id.idx)


-- -- The fullName should be as computed by `Lean.Elab.mkDeclName`.
-- -- Unfortunately that requires more context than we have, and modifies the state, e.g. checking if a private name already exists.
-- -- So we do some best-effort approximation. Usually declName is just `currNamespace ++ id`, except:
-- -- * macro scopes are extracted - we probably don't handle that well.
-- -- * '_root_' has special handling - we handle it partially?
-- -- * private names have an additional prefix – this is added correctly by realizeGlobalConstNoOverloadCore
-- let fullName: Name ← do
--   if id.isAnonymous then
--     pure Name.anonymous
--   else if let some identSyntax := identSyntax? then
--     ctx.runMetaM {} do
--       try
--         realizeGlobalConstNoOverloadCore (ctx.currNamespace ++ id)
--       catch _ =>
--         try
--           realizeGlobalConstNoOverload identSyntax
--         catch _ =>
--           -- In some rare cases neither of the above works, but somehow we can find the name here.
--           let range ← ctx.runCoreM' $ Lean.findDeclarationRanges? (ctx.currNamespace ++ id)
--           if range.isSome then
--             IO.eprintln s!"Failed to resolve global const {ctx.currNamespace}∷{id} {(ctx.currNamespace ++ id)} but got {range.repr 0}"
--             pure (ctx.currNamespace ++ id)
--           else
--             let consts := ctx.env.constants.map₂.toList.map (·.fst)
--             throw (Exception.error stx s!"Failed to resolve global const {ctx.currNamespace}∷{id} in {consts}")
--   else
--     pure Name.anonymous
