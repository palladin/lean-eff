import Lake
open Lake DSL

require leansqlite from git
  "https://github.com/leanprover/leansqlite.git" @ "main"

package lean_eff where
  version := v!"0.1.0"

@[default_target]
lean_lib LeanEff where
  srcDir := "."

@[default_target]
lean_exe lean_eff_tests where
  root := `Test.LeanEff

@[default_target]
lean_exe ascii_tetris where
  root := `Examples.AsciiTetris

@[default_target]
lean_exe video_rental_shop where
  root := `Examples.VideoRental

@[default_target]
lean_exe agent_snake_arena where
  root := `Examples.AgentSnake
