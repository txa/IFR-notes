import VersoManual
open Verso.Doc.Elab
open Lean Elab Term -- open Lean, open Lean.Elab ...

@[role_expander comment]
def comment : RoleExpander
  | _, _ => pure #[]
@[code_block_expander comment]
def commentCode : CodeBlockExpander
  | _, _ => pure #[]
-- These are part commands rather than block expanders so that it can be used in contexts where
-- block content doesn't fit, like right after an include. However, the blocks are still needed
-- for contexts where part commands aren't run.
-- @[part_command Verso.Syntax.codeblock, part_command Verso.Syntax.directive]
-- def commentBlock : PartCommand
--   | `(block| ::: $commentId $_* { $_* } )
--   | `(block| ``` $commentId $_* | $_ ``` ) => do
--     try
--       let n ← realizeGlobalConstNoOverloadWithInfo commentId
--       if n == ``comment then
--         return ()
--       else
--         throwUnsupportedSyntax
--     catch | _ => throwUnsupportedSyntax
--   | _ => throwUnsupportedSyntax
