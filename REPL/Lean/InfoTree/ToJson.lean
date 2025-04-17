import REPL.Lean.InfoTree
import REPL.Lean.ContextInfo

/-!
# Exporting an `InfoTree` as Json

-/

namespace Lean.Elab

instance : ToJson Substring where
  toJson s := toJson s.toString

instance : ToJson String.Pos where
  toJson n := toJson n.1

instance : ToJson String.Range where
  toJson r := toJson (r.start, r.stop)
-- deriving instance ToJson for String.Range

deriving instance ToJson for SourceInfo
deriving instance ToJson for Syntax.Preresolved
deriving instance ToJson for Syntax



structure InfoTreeNode (α : Type) where
  kind : String
  node : Option α
  children : List Json
deriving ToJson

deriving instance ToJson for Lean.Position

structure Syntax.Range where
  synthetic : Bool
  start : Lean.Position
  finish : Lean.Position
  byteRange: String.Range
deriving ToJson

structure Syntax.Json where
  pp : Option String
  raw : Syntax
  range : Range
deriving ToJson

def _root_.Lean.Syntax.toRange (stx : Syntax) (ctx : ContextInfo) : Syntax.Range :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  { start := ctx.fileMap.toPosition pos
    finish := ctx.fileMap.toPosition endPos
    byteRange := ⟨pos, endPos⟩
    synthetic := match stx.getHeadInfo with
    | .original .. => false
    | _ => true }

def cutDepth (stx : Syntax) (d : Nat) : Syntax :=
  match d with
  | 0 => Syntax.missing
  | d' + 1 => match stx with
    | .node info kind args => .node info kind (args.map (fun c => cutDepth c d'))
    | _ => stx


def _root_.Lean.Syntax.toJson (stx : Syntax) (ctx : ContextInfo) (lctx : LocalContext) : IO Syntax.Json := do
  return {
    pp := match (← ctx.ppSyntax lctx stx).pretty with
      | "failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)" => none
      | pp => some pp
    raw := cutDepth stx 2
    range := stx.toRange ctx }

structure TacticInfo.Json where
  name : Option Name
  stx : Syntax.Json
  goalsBefore : List String
  goalsAfter : List String
deriving ToJson

-- Note: this is not responsible for converting the children to Json.
def TacticInfo.toJson (i : TacticInfo) (ctx : ContextInfo) : IO TacticInfo.Json := do
  return {
    name := i.name?
    stx :=
    { pp := Format.pretty (← i.pp ctx),
      raw := cutDepth i.stx 2,
      range := i.stx.toRange ctx },
    goalsBefore := (← i.goalState ctx).map Format.pretty,
    goalsAfter := (← i.goalStateAfter ctx).map Format.pretty }

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

  id: Name  -- ident as used in the declaration (TODO unscoped?).
  -- May be .anonymous like for 'example' declarations.
  -- Does not include universe parameters like in 'foo.{u,v}'.

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

structure CommandInfo.Json where
  elaborator : Option Name
  declaration: Option DeclarationInfo
  stx : Syntax.Json
deriving ToJson

private def nameTail : Name → String
  | Name.str _ s => s
  | _ => ""


def getDeclInfo (info : CommandInfo) : IO DeclarationInfo := do
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

  -- Kind/keyword: strip 'Lean.Parser.Command.' from the kind Name.
  let kind := match declNode.getKind with | .str _ s => s | _ => ""  --

  -- Id/name:
  let declIdNode := declNode.getArgs.find? (·.isOfKind ``Lean.Parser.Command.declId)
  -- Skip universe parameters.
  let id := declIdNode.elim Lean.Name.anonymous (fun x => (x.getArg 0).getId)

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

  pure {
    modifiers := modifiers
    kind := kind
    isDefLike := Lean.Elab.Command.isDefLike declNode
    id := id
    typeByteRange := (declSigType.getD Syntax.missing).getRange?
    valByteRange := (declVal.getD Syntax.missing).getRange?
    valBodyByteRange := (declBody.getD Syntax.missing).getRange?
    -- rawType := declSigType.bind Lean.Syntax.reprint
    -- rawBody := declBody.reprint
  }

def CommandInfo.toJson (info : CommandInfo) (ctx : ContextInfo) : IO CommandInfo.Json := do
  let declaration ← if (info.elaborator  == ``Lean.Elab.Command.elabDeclaration)
    then pure (some (← getDeclInfo info))
    else pure none
  return {
    elaborator := match info.elaborator with | .anonymous => none | n => some n,
    declaration := declaration,
    stx := ← info.stx.toJson ctx {} }

structure TermInfo.Json where
  elaborator : Option Name
  stx : Syntax.Json
  expectedType? : Option String
  expr : String
  isBinder : Bool
deriving ToJson

def TermInfo.toJson (info : TermInfo) (ctx : ContextInfo) : IO TermInfo.Json := do
  return {
    elaborator := match info.elaborator with | .anonymous => none | n => some n,
    stx := ← info.stx.toJson ctx info.lctx,
    expectedType? := ← info.expectedType?.mapM fun ty => do
      pure (← ctx.ppExpr info.lctx ty).pretty
    expr := (← ctx.ppExpr info.lctx info.expr).pretty
    isBinder := info.isBinder }

structure PartialTermInfo.Json where
  elaborator : Option Name
  stx : Syntax.Json
  expectedType? : Option String
deriving ToJson

def PartialTermInfo.toJson (info : PartialTermInfo) (ctx : ContextInfo) : IO PartialTermInfo.Json := do
  return {
    elaborator := match info.elaborator with | .anonymous => none | n => some n,
    stx := ← info.stx.toJson ctx info.lctx,
    expectedType? := ← info.expectedType?.mapM fun ty => do
      pure (← ctx.ppExpr info.lctx ty).pretty }

structure MacroExpansionInfo.Json where
  stx : Syntax.Json  -- syntax before expansion
deriving ToJson

def MacroExpansionInfo.toJson (info : MacroExpansionInfo) (ctx : ContextInfo) : IO MacroExpansionInfo.Json := do
  return { stx := ← info.stx.toJson ctx info.lctx }

structure InfoTree.HoleJson where
  goalState : String
deriving ToJson

partial def InfoTree.toJson (t : InfoTree) (ctx? : Option ContextInfo) : IO Json := do
  match t with
  | .context ctx t => t.toJson (ctx.mergeIntoOuter? ctx?)
  | .node info children =>
    if let some ctx := ctx? then
      let node : Option Json ← match info with
      | .ofTermInfo           info => some <$> (do pure <| Lean.toJson (← info.toJson ctx))
      | .ofPartialTermInfo    info => some <$> (do pure <| Lean.toJson (← info.toJson ctx))
      | .ofCommandInfo        info => some <$> (do pure <| Lean.toJson (← info.toJson ctx))
      | .ofTacticInfo         info => some <$> (do pure <| Lean.toJson (← info.toJson ctx))
      | .ofMacroExpansionInfo info => some <$> (do pure <| Lean.toJson (← info.toJson ctx))
      | _                   => pure none
      return Lean.toJson (InfoTreeNode.mk info.kind node (← children.toList.mapM fun t' => t'.toJson ctx))
    else throw <| IO.userError "No `ContextInfo` available."
  | .hole mvarId =>
    if let some ctx := ctx? then
     return Lean.toJson (InfoTree.HoleJson.mk (← ctx.runMetaM {} (do Meta.ppGoal mvarId)).pretty)
    else throw <| IO.userError "No `ContextInfo` available."


def constKind : ConstantInfo → String
  | .defnInfo   _ => "definition"  -- a "def"
  | .axiomInfo  _ => "axiom"
  | .thmInfo    _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo   _ => "Quot"  -- from quotients (Quot/Quot.mk/Quot.lift/Quot.ind)
  | .inductInfo _ => "inductive"  -- One for each inductive datatype in a mutual declaration.
  | .ctorInfo   _ => "constructor"  -- Of an inductive type; one per Constructor in mutual decl.
  | .recInfo    _ => "recursor" -- Generated by mutual declaration.

structure ConstantInfo.Json where
  name : Name
  kind: String
  levelParams: List Name  -- https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/#--tech-term-universe-parameters
  type : String  -- The constant's type Expr, pretty-printed (for a theorem, this is the statement without binders).
  isProp: Bool -- Whether type is a Prop.
  value: Option String  -- The constant's value Expr, pretty-printed (for a theorem, this is the proof, as an unreduced term).
  safety: String -- "safe" or "unsafe" or "partial", see https://lean-lang.org/doc/reference/latest/Definitions/Modifiers/#declaration-modifiers
deriving ToJson


def constInfoToJson (c: ConstantInfo) (ctx : ContextInfo) : IO (Option ConstantInfo.Json) := do
  if (nameTail c.name).startsWith "_" then
    return none
  let safety := if c.isUnsafe then "unsafe" else (if c.isPartial then "partial" else "safe")
  let type := (← ctx.ppExpr {} c.type).pretty
  let isProp ←  ctx.runMetaM {} <| Lean.Meta.isProp c.type
  let value ←  c.value?.mapM (fun v => do pure (← ctx.ppExpr {} v).pretty)
  return some {
    name := c.name, kind := constKind c, levelParams := c.levelParams, type, isProp, safety, value
  }

def constantsToJson(constants: Array ConstantInfo) (ctx : ContextInfo) : IO (Array ConstantInfo.Json) := do
  constants.filterMapM (fun x => constInfoToJson x ctx)

def constMapToJson(constMap: Lean.ConstMap) (ctx : ContextInfo) : IO (List ConstantInfo.Json) := do
  constMap.toList.filterMapM (fun (_, c) => (constInfoToJson c ctx))

end Lean.Elab
