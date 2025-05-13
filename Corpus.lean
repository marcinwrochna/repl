
import Lean.Data.Json.Printer
import Lean.Data.Json.Stream
import Lean.Elab.Open
import Lean.Elab.Command
import Lean.Server.References
import Lake.Util.Cli
import Lean.Util.Paths
import Lake.Config.Env

import REPL.Lean.ConstantInfo

open Lean Lean.Elab


structure CorpusOptions where
  width: Nat := Std.Format.defWidth
  trustLevel: UInt32 := 1
  openDecls: List OpenDecl := []
  deps: Bool := false


namespace Cli

abbrev CliMainM := IO
abbrev CliStateM := StateT CorpusOptions CliMainM
abbrev CliM := Lake.ArgsT CliStateM


def takeOptionArg (opt arg : String) : CliM String := do
  match (← Lake.takeArg?) with
  | none => throw <| IO.userError s!"Missing argument ⟨{arg}⟩ for option `{opt}`"
  | some arg => pure arg

@[inline] def takeOptionArg' (opt arg : String) (f : String → Option α)  : CliM α := do
  let a ← takeOptionArg opt arg
  if let some fa :=  f a then return fa
  throw <| IO.userError s!"Invalid argument for option `{opt} ⟨{arg}⟩`: {a}"

@[inline] def takeOptionArgNat (opt arg : String) : CliM Nat := do
  takeOptionArg' opt arg String.toNat?

@[inline] def takeOptionArgUint32 (opt arg : String) : CliM UInt32 := do
  takeOptionArg' opt arg (·.toNat?.map Nat.toUInt32)

def addOpenDecl (decl : OpenDecl) : CliM PUnit := do
  modifyThe CorpusOptions (fun d => {d with openDecls := decl :: d.openDecls })

def addOpenDecl' (ns : String) : CliM PUnit := do
  addOpenDecl (OpenDecl.simple ns.toName [])

def corpusLongOption : (opt : String) → CliM PUnit
  | "--width"   => do let w ← takeOptionArgNat "--width" "width" ; modifyThe CorpusOptions ({· with width := w })
  | "--trust"   => do let t ← takeOptionArgUint32 "--trust" "trustLevel"; modifyThe CorpusOptions ({· with trustLevel := t })
  | "--open"    => do let o ← takeOptionArg "--open" "namespace"; addOpenDecl' o
  | "--deps"    => modifyThe CorpusOptions ({· with deps := true })
  | opt =>  throw <| IO.userError s!"Unknown option: {opt}"

def corpusShortOption : (opt : Char) → CliM PUnit
  | 'w' => do let w ← takeOptionArgNat "-w" "width"; modifyThe CorpusOptions ({· with width := w })
  | 't' => do let t ← takeOptionArgUint32 "-t" "trustLevel"; modifyThe CorpusOptions ({· with trustLevel := t })
  | 'o' => do let o ← takeOptionArg "-o" "namespace"; addOpenDecl' o
  | 'd' => modifyThe CorpusOptions ({· with deps := true })
  | opt => throw <| IO.userError s!"Unknown option: -{opt}"

def corpusOption :=
  Lake.option {
    short := corpusShortOption
    long := corpusLongOption
    longShort := Lake.shortOptionWithArg corpusShortOption
  }

def runAux {α} (self : CliM α) (args : List String) : IO α := do
  self.run' args |>.run' {}

def run {α} (f : CorpusOptions → IO α) (args : List String) : IO α := do
  let opts ← runAux
    do
      Lake.processOptions Cli.corpusOption
      let opts ← getThe CorpusOptions
      let remainingArgs ← Lake.getArgs
      if !remainingArgs.isEmpty then
        throw <| IO.userError s!"Unexpected arguments: {remainingArgs}"
      pure opts
    args
  f opts

end Cli



structure ModuleInfo where
  name: Name
  imports: List Name
  oleanPath: System.FilePath
  leanPath: System.FilePath
  constants: RBMap String ConstantInfo.Json compare
  deriving ToJson



def ppExpr' (ppCtx: PPContext) (cOpts: CorpusOptions) (x : Expr) : IO String := do
  let fmtWithInfo ← ppExprWithInfos ppCtx x
  return fmtWithInfo.fmt.pretty (width := cOpts.width)

-- Same as ContextInfo.runCoreM, but we pass the fileMap.
def ContextInfo.runCoreM' (info : Elab.ContextInfo) (x : CoreM α) : IO α := do
  (·.1) <$>
    (withOptions (fun _ => info.options) x).toIO
      { currNamespace := info.currNamespace, openDecls := info.openDecls
        fileName := "<InfoTree>", fileMap := info.fileMap }
      { env := info.env, ngen := info.ngen }


def getConstInfo (const: ConstantInfo) (pp : Expr → IO String) (ctx : Elab.ContextInfo)
    : IO (Option (String × ConstantInfo.Json)) := do
  if let .str _p s := const.name then
    if !s.startsWith "_" then
      let name := const.name
      let kind := constKind const
      let type ← pp const.type
      let value ← if const.hasValue then (pp const.value!).map (some ·) else pure none
      let levelParams := const.levelParams
      -- This might be problematic with `withImportModules`
      let isProp ←  ctx.runMetaM {} <| Lean.Meta.isProp const.type
      let isUnsafe := const.isUnsafe
      let isPartial := const.isPartial
      -- This doesn't work with `withImportModules`, because we don't initialize extensions.
      -- Maybe there's a way to load `Lean.DeclarationRange` properly?
      -- let ranges ← if ctx.fileMap.source.isEmpty then
      --     pure $ none
      --   else
      --     ContextInfo.runCoreM' ctx (Lean.findDeclarationRanges? const.name)
      -- let pos := ranges.map (fun r => r.range.pos)
      -- let endPos := ranges.map (fun r => r.range.endPos)
      -- let byteRange: Option String.Range := ranges.map
      --  fun r => ⟨ctx.fileMap.ofPosition r.range.pos, ctx.fileMap.ofPosition r.range.endPos⟩
      let c : ConstantInfo.Json := {
        name, kind, type, value, levelParams, isProp, isUnsafe, isPartial
      }
      return some (const.name.toString, c)
    else
      return none
  else
    return none


/-- Find the `.lean` source of a module in a `LEAN_SRC_PATH` search path. -/
partial def findLean (sp : SearchPath) (mod : Name) : IO System.FilePath := do
  if let some fname ← sp.findWithExt "lean" mod then
    return fname
  else
    throw <| IO.userError s!"Failed to find source file for {mod}"


unsafe def processModule
  (i : Nat) (n : Nat)
  (oleanPath : System.FilePath)
  (searchPath: SearchPath)
  (srcSearchPath: SearchPath)
  (cOpts: CorpusOptions)
  (atomicStdOut: IO.Mutex IO.FS.Stream)
: IO Unit := do

  let some moduleName ← searchModuleNameOfFileName oleanPath searchPath
    | throw <| IO.userError s!"failed to find module name for {oleanPath}"

  let (module, _region) ← readModuleData oleanPath
  IO.eprintln s!"({i + 1} / {n}) Loading {moduleName} {oleanPath} with {module.constants.size} entries"
  let imports := module.imports.filterMap (fun m => if m.runtimeOnly then (some m.module) else none)
  let leanPath ← (if moduleName.toString == "LakeMain"
                  then pure $ System.FilePath.mk ""
                  else findLean srcSearchPath moduleName)
  let leanContents ← if (← System.FilePath.pathExists leanPath) then IO.FS.readFile leanPath else pure ""
  let inputCtx := Parser.mkInputContext leanContents leanPath.toString

  let opts : Options := {}
  -- withImportModules might need (level := OLeanLevel.private) in some future Lean version.
  let moduleInfo ← withImportModules
      (trustLevel := cOpts.trustLevel) #[⟨moduleName, false⟩] opts fun env => do
    let ppCtx : PPContext := { env, opts, currNamespace := Name.anonymous, openDecls := cOpts.openDecls }
    let ctx : Elab.ContextInfo := {
      env := env,
      fileMap := inputCtx.fileMap,
      mctx := {},
      options := opts,
      currNamespace := Name.anonymous,
      openDecls := cOpts.openDecls,
      ngen := {},
    }
    let pp := ppExpr' ppCtx cOpts
    -- let cmdState := Elab.Command.mkState env {} opts
    let constInfos ← module.constants.filterMapM fun c => getConstInfo c pp ctx
    pure {
      name := moduleName,
      imports := imports.toList,
      oleanPath,
      leanPath,
      constants := RBMap.fromArray constInfos compare
      : ModuleInfo
    }


  atomicStdOut.atomically fun stdOut' => do
    let stdOut ← stdOut'.get
    IO.FS.Stream.writeJson stdOut (toJson moduleInfo)
    stdOut.putStrLn ""
    stdOut.flush

unsafe def corpusMain (cOpts: CorpusOptions) : IO Unit := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← Lake.findInstall?
  let some lakeInstall := lakeInstall? | throw <| IO.userError "Lake installation not found"
  let some leanInstall := leanInstall? | throw <| IO.userError "Lean installation not found"
  let lakeEnv? ← (Lake.Env.compute lakeInstall leanInstall elanInstall?).toIO'
  let .ok lakeEnv := lakeEnv? | throw <| IO.userError "Lake environment not found"

  let srcSearchPath := lakeEnv.leanSrcPath ++ [lakeEnv.lean.srcDir]
  initSearchPath (← findSysroot)
  let searchPath ← searchPathRef.get

  let oleans: Array System.FilePath ←
    if cOpts.deps then
      searchPath.findAllWithExt "olean"
    else do
      let sp : SearchPath := [System.mkFilePath [".lake", "build", "lib", "lean"]]
      sp.findAllWithExt "olean"
  -- TODO add option to exclude Init, Lake, Lean, Std, Qq, ProofWidget, Batteries; Mathlib.


  let atomicStdOut ← IO.Mutex.new (← IO.getStdout)

  let mut visited: Array System.FilePath := #[]
  let mut tasks: List (Task (Except IO.Error Unit)) := []

  for (oleanPath, i) in oleans.zipWithIndex do
    if visited.contains oleanPath then
      IO.eprintln s!"({i + 1} / {oleans.size}) Skipping already loaded {oleanPath}."
      continue
    visited := visited.push oleanPath

    -- Synchronized:
    -- processModule i oleans.size oleanPath searchPath srcSearchPath cOpts

    -- Parallel:
    let task ← (processModule i oleans.size oleanPath searchPath srcSearchPath cOpts atomicStdOut).asTask
    tasks := task :: tasks

  let results? := (← IO.mapTasks (fun results => pure results) tasks).get
  match results? with
  | .error e => throw e
  | .ok results =>
    results.forM fun result =>
      match result with
      | .error e => throw e
      | .ok () => pure ()

  IO.eprintln s!"Done!"


unsafe def main (args : List String) : IO Unit := do
  inline <| Cli.run corpusMain args
