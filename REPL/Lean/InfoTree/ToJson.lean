import REPL.Lean.InfoTree
import REPL.Lean.ContextInfo
import REPL.Lean.DeclarationInfo

/-!
# Exporting an `InfoTree` as Json

-/

namespace Lean.Elab

instance : ToJson Substring where
  toJson s := toJson s.toString

deriving instance ToJson for SourceInfo
deriving instance ToJson for Syntax.Preresolved
deriving instance ToJson for Syntax

deriving instance BEq for QuotKind, QuotVal, InductiveVal, ConstantInfo


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
  elaborator: Option Name
  stx : Syntax.Json
  goalsBefore : List String
  goalsAfter : List String
deriving ToJson

-- Note: this is not responsible for converting the children to Json.
def TacticInfo.toJson (i : TacticInfo) (ctx : ContextInfo) : IO TacticInfo.Json := do
  return {
    name := i.name?
    elaborator := match i.elaborator with | .anonymous => none | n => some n,
    stx :=
    { pp := Format.pretty (← i.pp ctx),
      raw := cutDepth i.stx 2,
      range := i.stx.toRange ctx },
    goalsBefore := (← i.goalState ctx).map Format.pretty,
    goalsAfter := (← i.goalStateAfter ctx).map Format.pretty }


structure CommandInfo.Json where
  elaborator : Option Name
  declaration: Option DeclarationInfo
  stx : Syntax.Json
deriving ToJson

def CommandInfo.toJson (info : CommandInfo) (ctx : ContextInfo) : IO CommandInfo.Json := do
  let declaration ← if (info.elaborator  == ``Lean.Elab.Command.elabDeclaration)
    then pure (some (← getDeclInfo info ctx))
    else pure none
  return {
    elaborator := match info.elaborator with | .anonymous => none | n => some n,
    declaration := declaration,
    stx := ← info.stx.toJson ctx {} }


structure ConstantRef where
  fullName : Name
  moduleName : Option Name  -- none means current module.
deriving ToJson

def Constant.toJson (fullName: Name) (_levels: List Level) (ctx : ContextInfo) : IO ConstantRef := do
  let moduleName := if let some modIdx := ctx.env.getModuleIdxFor? fullName then
    some ctx.env.header.moduleNames[modIdx.toNat]!
  else
    none -- ctx.env.header.mainModule
  return { fullName, moduleName }

structure TermInfo.Json where
  elaborator : Option Name
  stx : Syntax.Json
  expectedType? : Option String
  expr : String
  isBinder : Bool
  const: Option ConstantRef -- If the term is a constant, info about what exactly it refers to.
deriving ToJson

def TermInfo.toJson (info : TermInfo) (ctx : ContextInfo) : IO TermInfo.Json := do
  let const ← if let .const name us := info.expr then
    pure (some (← Constant.toJson name us ctx))
  else
    pure none
  let expr ← do
    -- Workaround for the fact that we can't pretty-print Prod.fst and Prod.snd
    -- in the module that defines pretty-printing options for them.
    let manual: Option String := match info.expr with
      | .const `Prod.fst _ => some "Prod.fst"
      | .const `Prod.snd _ => some "Prod.snd"
      | _ => none
    if ctx.currNamespace == `Prod.PrettyPrinting && manual.isSome then
      pure manual.get!
    else
      pure (← ctx.ppExpr info.lctx info.expr).pretty
  return {
    elaborator := match info.elaborator with | .anonymous => none | n => some n,
    stx := ← info.stx.toJson ctx info.lctx,
    expectedType? := ← info.expectedType?.mapM fun ty => do
      pure (← ctx.ppExpr info.lctx ty).pretty
    expr := expr
    isBinder := info.isBinder
    const
  }


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

structure CustomInfo.Json where
  typeName : Name
  stx: Syntax.Json
deriving ToJson

def CustomInfo.toJson (info : CustomInfo) (ctx : ContextInfo) : IO CustomInfo.Json := do
  return { typeName := info.value.typeName, stx := ← info.stx.toJson ctx {} }

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
      | .ofCustomInfo         info => some <$> (do pure <| Lean.toJson (← info.toJson ctx))
      | _                   => pure none
      return Lean.toJson (InfoTreeNode.mk info.kind node (← children.toList.mapM fun t' => t'.toJson ctx))
    else throw <| IO.userError "No `ContextInfo` available."
  | .hole mvarId =>
    if let some ctx := ctx? then
     return Lean.toJson (InfoTree.HoleJson.mk (← ctx.runMetaM {} (do Meta.ppGoal mvarId)).pretty)
    else throw <| IO.userError "No `ContextInfo` available."


end Lean.Elab
