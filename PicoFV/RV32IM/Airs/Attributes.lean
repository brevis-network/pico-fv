import Lean.Meta.Tactic.Simp.RegisterCommand

-- General
register_simp_attr pico_encapsulation

-- CPU Air: Union member interpretation tags
register_simp_attr cpu_branch_cols_simplification
register_simp_attr cpu_jump_cols_simplification
register_simp_attr cpu_auipc_cols_simplification
register_simp_attr cpu_ecall_cols_simplification

-- CPU Air: Groupings for non-union computed values
register_simp_attr cpu_syscall_derived_simplification
