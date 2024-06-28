import Lake
open Lake DSL

require verso from git "https://github.com/leanprover/verso"@"main"

package "verso-manual" where
  -- add package configuration options here

lean_lib Manual where

@[default_target]
lean_exe "generate-manual" where
  root := `Main
