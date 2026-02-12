import PicoFV.RV32D.Auxiliaries

inductive RV32MemoryWidth where
| Byte | Half | Word

def width_of_mem_width (mw : RV32MemoryWidth) :=
match mw with
| .Byte   => 8
| .Half   => 16
| .Word   => 32

inductive RV32Operation where
| ReadPC   (val : BitVec 32) : RV32Operation
| WritePC  (val : BitVec 32) : RV32Operation
| ReadReg  (reg : regidx) (val : BitVec 32) : RV32Operation
| WriteReg (reg : regidx) (val : BitVec 32) : RV32Operation
| ReadMem  (addr : ℕ) (mw : RV32MemoryWidth) (val : BitVec (width_of_mem_width mw)) : RV32Operation
| WriteMem (addr : ℕ) (mw : RV32MemoryWidth) (val : BitVec (width_of_mem_width mw)) : RV32Operation

structure RV32OperationEffect where
  hypotheses : Prop
  state : EStateM.Result (Sail.Error exception) (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult

def operation_effect
  (result : RV32OperationEffect)
  (entry : RV32Operation)
: RV32OperationEffect :=
  match result.state with
  | .error _ _ => result
  | .ok _ state =>
    match entry with
    | .ReadPC val =>
      { result with
          hypotheses := result.hypotheses ∧ Sail.readReg Register.PC state = EStateM.Result.ok val state }
    | .WritePC val =>
      { result with
          state := EStateM.Result.map
                    (fun _ ↦ ExecutionResult.Retire_Success ())
                    (Sail.writeReg Register.nextPC val state) }
    | .ReadReg reg val =>
      { result with
          hypotheses := result.hypotheses ∧ read_xreg (regidx_to_fin reg) state = EStateM.Result.ok val state }
    | .WriteReg reg val =>
      { result with
          state := EStateM.Result.map
                    (fun _ ↦ ExecutionResult.Retire_Success ())
                    (write_xreg (regidx_to_fin reg) val state) }
    | .ReadMem addr mw val =>
      match mw with
      | .Byte =>
        { result with
            hypotheses := result.hypotheses ∧ state.mem[addr]? = .some val }
      | .Half =>
        let data0 := BitVec.extractLsb 7 0 val
        let data1 := BitVec.extractLsb 15 8 val
        { result with
            hypotheses := result.hypotheses ∧
                          state.mem[addr]? = .some data0 ∧
                          state.mem[addr + 1]? = .some data1 }
      | .Word =>
        let data0 := BitVec.extractLsb 7 0 val
        let data1 := BitVec.extractLsb 15 8 val
        let data2 := BitVec.extractLsb 23 16 val
        let data3 := BitVec.extractLsb 31 24 val
        { result with
            hypotheses := result.hypotheses ∧
                          state.mem[addr]? = .some data0 ∧
                          state.mem[addr + 1]? = .some data1 ∧
                          state.mem[addr + 2]? = .some data2 ∧
                          state.mem[addr + 3]? = .some data3 }
    | .WriteMem addr mw val =>
      { result with
          state :=
            match mw with
            | .Byte =>
              EStateM.Result.ok (ExecutionResult.Retire_Success ()) {
                state with mem := state.mem.insert addr val
              }
            | .Half =>
              let data0 := BitVec.extractLsb 7 0 val
              let data1 := BitVec.extractLsb 15 8 val
              EStateM.Result.ok (ExecutionResult.Retire_Success ()) {
                state with
                  mem := (state.mem.insert addr data0).insert (addr + 1) data1
              }
            | .Word =>
              let data0 := BitVec.extractLsb 7 0 val
              let data1 := BitVec.extractLsb 15 8 val
              let data2 := BitVec.extractLsb 23 16 val
              let data3 := BitVec.extractLsb 31 24 val
              EStateM.Result.ok (ExecutionResult.Retire_Success ()) {
                state with
                  mem := (((state.mem.insert addr data0
                            ).insert (addr + 1) data1
                          ).insert (addr + 2) data2
                        ).insert (addr + 3) data3
              }
      }

/-- `RV32_operation_effect` captures the effect of a list of operations on the RISC-V state, returning:
    - the hypotheses obtained from the reads; and
    - the state after the writes. -/
def RV32_operation_effect
  (ops : List RV32Operation)
  (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
:
  RV32OperationEffect
:=
  -- Execution bus assumption
  List.foldl
    operation_effect
    { hypotheses := True, state := EStateM.Result.ok (ExecutionResult.Retire_Success ()) state }
    ops

lemma operation_effect_state_hyps
:
  (List.foldl
    operation_effect
    { hypotheses := hyps₁, state := EStateM.Result.ok (ExecutionResult.Retire_Success ()) state }
    ops).state
  =
  (List.foldl
    operation_effect
    { hypotheses := hyps₂, state := EStateM.Result.ok (ExecutionResult.Retire_Success ()) state }
    ops).state
:= by
  induction ops generalizing hyps₁ hyps₂ state
  case nil => simp
  case cons op ops ih =>
    simp [List.foldl_cons]
    conv => lhs; arg 1; arg 2; unfold operation_effect
    conv => rhs; arg 1; arg 2; unfold operation_effect
    cases op <;> try grind
    case WritePC pc_val =>
      simp [Sail.writeReg, PreSail.writeReg]
      grind
    case WriteReg reg val =>
      simp [write_xreg]
      by_cases hz : regidx_to_fin reg = 0
      . simp_all; grind
      . simp_all [Sail.writeReg, PreSail.writeReg]
        grind

@[simp]
lemma RV32_operation_effect_state_readPC
:
  (RV32_operation_effect (.ReadPC pc_val :: ops) state).state
    =
  (RV32_operation_effect ops state).state
:= by
  simp [RV32_operation_effect, List.foldl_cons]
  conv => lhs; arg 1; arg 2; unfold operation_effect; simp
  apply operation_effect_state_hyps

@[simp]
lemma RV32_operation_effect_state_readReg
:
  (RV32_operation_effect (.ReadReg reg val :: ops) state).state
    =
  (RV32_operation_effect ops state).state
:= by
  simp [RV32_operation_effect, List.foldl_cons]
  conv => lhs; arg 1; arg 2; unfold operation_effect; simp
  apply operation_effect_state_hyps

lemma RV32_operation_effect_swap_writePC_writeReg
:
  (RV32_operation_effect (.WritePC pc_val :: .WriteReg reg val :: ops) state).state
    =
  (RV32_operation_effect (.WriteReg reg val :: .WritePC pc_val :: ops) state).state
:= by
  simp [RV32_operation_effect, List.foldl_cons]
  conv => lhs; arg 1; arg 2; unfold operation_effect; simp [Sail.writeReg, PreSail.writeReg]
  conv => rhs; arg 1; arg 2; unfold operation_effect; simp [Sail.writeReg, PreSail.writeReg]
  simp [write_xreg]
  by_cases hz : regidx_to_fin reg = 0
  . simp_all
  . simp_all [Sail.writeReg, PreSail.writeReg]
    congr 5
    rw [ExtDHashMap.insert_comm]
    simp [reg_of_fin, regidx_to_fin]
    split <;> simp
