import Lake
open Lake DSL

package lean_eff where
  version := v!"0.1.0"
  defaultTargets := #[`LeanEff, `lean_eff_tests]

lean_lib LeanEff where
  srcDir := "."

lean_exe lean_eff_tests where
  root := `Test.LeanEff
