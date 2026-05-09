import Lake
open Lake DSL

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
