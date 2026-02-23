import Mathlib

/-!
# Pico CPU AIR simplification attributes

Custom simp attribute sets for selectively simplifying the OpcodeSpecificCols
union interpretations. Each union member gets its own tag so you can do e.g.
`simp only [cpu_branch_cols]` to unfold only the branch column aliases.
-/

-- All airs: primary simplification attribute
register_simp_attr pico_encapsulation

-- CPU Air: Union member interpretation tags
register_simp_attr cpu_branch_cols
register_simp_attr cpu_jump_cols
register_simp_attr cpu_auipc_cols
register_simp_attr cpu_ecall_cols

-- CPU Air: Groupings for non-union computed values
register_simp_attr cpu_syscall_derived
