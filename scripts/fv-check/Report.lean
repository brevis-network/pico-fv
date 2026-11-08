import PicoFV64

/-! Prints, for each theorem named in `theorems.d/*.txt`, the axioms it depends on and its
statement, in a line-oriented form that `check.sh` compares against the whitelist and
the committed signature snapshot. -/

open Lean Elab Command Meta

elab "#fv_report " dir:str : command => do
  let files := (← System.FilePath.readDir dir.getString).map (·.path)
    |>.filter (·.extension == some "txt") |>.qsort (·.toString < ·.toString)
  let mut names := #[]
  for file in files do
    names := names ++ (← IO.FS.lines file).filter (·.trim ≠ "")
  for line in names do
    let n := line.trim.toName
    match (← getEnv).find? n with
    | none => IO.println s!"MISSING {n}"
    | some ci =>
      let axs ← collectAxioms n
      let axs := axs.map toString |>.qsort (· < ·)
      IO.println s!"AXIOMS {n} {String.intercalate "," axs.toList}"
      let ty ← liftTermElabM do return (← ppExpr ci.type).pretty 100000
      IO.println s!"SIGNATURE {n} {ty.replace "\n" " "}"

#fv_report "scripts/fv-check/theorems.d"
