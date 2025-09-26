/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashMap
import VersoManual
import IFRNotes

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

--open IFRNotes

def config : Config where
  extraFiles := [("diagrams", "diagrams")]
  emitTeX := false
  emitHtmlSingle := false
  emitHtmlMulti := true
  htmlDepth := 1

--def main := manualMain (%doc IFRNotes) (extraSteps := [buildExercises]) (config := config)
--def main := manualMain (%doc IFRNotes) (config := config)
def main := manualMain (%doc IFRNotes) (config := config.addKaTeX)
