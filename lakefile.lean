import Lake
open Lake DSL

package «leanprojectcoolio2» where
  -- add package configuration options here

lean_lib «Leanprojectcoolio2» where
  -- add library configuration options here

@[default_target]
lean_exe «leanprojectcoolio2» where
  root := `Main

require mathlib from git
  "https://github.com/realharryhero/mathliboldrepo"
