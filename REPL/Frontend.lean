/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Frontend

open Lean Elab

namespace Lean.Elab.IO

/--
Process some text input, with or without an existing command state.
If there is no existing environment, we parse the input for headers (e.g. import statements),
and create a new environment.
Otherwise, we add to the existing environment.

Returns:
1. The resulting command state after processing the entire input
2. The header-only command state (only useful when cmdState? is none)
3. The header Syntax (if there was one).
-/
def processInput (input : String) (cmdState? : Option Command.State)
    (opts : Options := {}) (fileName : Option String := none) :
    IO (Frontend.State × Command.State × Option Syntax) := unsafe do
  Lean.initSearchPath (← Lean.findSysroot)
  enableInitializersExecution
  let fileName   := fileName.getD "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let (parserState, beforeCommandState, headerSyntax) ← match cmdState? with
  | none => do
      let (header, parserState, messages) ← Parser.parseHeader inputCtx
      let (env, messages) ← processHeader header opts messages inputCtx
      let headerOnlyState := Command.mkState env messages opts
      pure (parserState, headerOnlyState, some header)
  | some cmdState => do
      pure ({ : Parser.ModuleParserState }, cmdState, none)
  let commandState := { beforeCommandState with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState
  pure (s, beforeCommandState, headerSyntax)
