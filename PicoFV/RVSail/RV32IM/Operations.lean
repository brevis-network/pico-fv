import PicoFV.RVSail.RV32IM.Auxiliaries
import PicoFV.RVSail.RV32IM.Buses

namespace RV32IM

  inductive MemoryWidth where
  | Byte | Half | Word

  def width_of_mem_width (mw : MemoryWidth) :=
  match mw with
  | .Byte   => 8
  | .Half   => 16
  | .Word   => 32

  inductive Operation where
  | ReadPC   (val : BitVec 32) : Operation
  | WritePC  (val : BitVec 32) : Operation
  | ReadReg  (reg : regidx) (val : BitVec 32) : Operation
  | WriteReg (reg : regidx) (val : BitVec 32) : Operation
  | ReadMem  (addr : ℕ) (mw : MemoryWidth) (val : BitVec (width_of_mem_width mw)) : Operation
  | WriteMem (addr : ℕ) (mw : MemoryWidth) (val : BitVec (width_of_mem_width mw)) : Operation

  section OperationEffect

    structure OperationEffect where
      hypotheses : Prop
      state : EStateM.Result (Sail.Error exception) (PreSail.SequentialState RegisterType Sail.trivialChoiceSource) ExecutionResult

    def operation_effect
      (result : OperationEffect)
      (entry : Operation)
    : OperationEffect :=
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

    /-- `operation_list_effect` captures the effect of a list of operations on the RISC-V state, returning:
        - the hypotheses obtained from the reads; and
        - the state after the writes. -/
    def operation_list_effect
      (ops : List Operation)
      (state : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    :
      OperationEffect
    :=
      -- Execution bus assumption
      List.foldl
        operation_effect
        { hypotheses := True, state := EStateM.Result.ok (ExecutionResult.Retire_Success ()) state }
        ops

    lemma operation_list_effect_hypothesis_extract_general
      (h_equiv : hyps₁ ∧ hyps₂ ↔ hyps)
    :
      (List.foldl operation_effect
        { hypotheses := hyps,
          state := EStateM.Result.ok (ExecutionResult.Retire_Success ()) state } ops).hypotheses ↔
      hyps₁ ∧
      (List.foldl operation_effect
        { hypotheses := hyps₂,
          state := EStateM.Result.ok (ExecutionResult.Retire_Success ()) state } ops).hypotheses
    := by
      induction ops generalizing hyps hyps₁ hyps₂ state
      case nil => simp_all
      case cons op ops ih =>
        cases op <;>
          simp_all [operation_effect, Sail.writeReg, PreSail.writeReg] <;>
          try (rw [ih]; grind)
        case WriteReg reg val =>
          by_cases h_r0 : (regidx_to_fin reg).val = 0 <;>
            simp [write_xreg, h_r0, Sail.writeReg, PreSail.writeReg] <;>
            rw [ih] <;> grind
        case ReadMem addr width val =>
          cases width <;> simp <;> rw [ih] <;> grind
        case WriteMem addr width val =>
          cases width <;> simp <;> rw [ih] <;> grind

    lemma operation_list_effect_hypothesis_extract
    :
      (List.foldl operation_effect
        { hypotheses := hyps,
          state := EStateM.Result.ok (ExecutionResult.Retire_Success ()) state } ops).hypotheses ↔
      hyps ∧
      (List.foldl operation_effect
        { hypotheses := True,
          state := EStateM.Result.ok (ExecutionResult.Retire_Success ()) state } ops).hypotheses
    := by
      apply operation_list_effect_hypothesis_extract_general (by tauto)

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
    lemma operation_list_effect_hypotheses_readPC
    :
      (operation_list_effect (.ReadPC pc_val :: ops) state).hypotheses
        =
      (Sail.readReg Register.PC state = EStateM.Result.ok pc_val state ∧ (operation_list_effect ops state).hypotheses)
    := by
      simp [operation_list_effect, List.foldl_cons]
      conv => lhs; arg 1; arg 2; unfold operation_effect; simp
      apply operation_list_effect_hypothesis_extract

    @[simp]
    lemma operation_list_effect_state_readPC
    :
      (operation_list_effect (.ReadPC pc_val :: ops) state).state
        =
      (operation_list_effect ops state).state
    := by
      simp [operation_list_effect, List.foldl_cons]
      conv => lhs; arg 1; arg 2; unfold operation_effect; simp
      apply operation_effect_state_hyps

    @[simp]
    lemma operation_list_effect_hypotheses_readReg
    :
      (operation_list_effect (.ReadReg reg val :: ops) state).hypotheses
        =
      (read_xreg (regidx_to_fin reg) state = EStateM.Result.ok val state ∧ (operation_list_effect ops state).hypotheses)
    := by
      simp [operation_list_effect, List.foldl_cons, operation_effect]
      exact operation_list_effect_hypothesis_extract

    @[simp]
    lemma operation_list_effect_state_readReg
    :
      (operation_list_effect (.ReadReg reg val :: ops) state).state
        =
      (operation_list_effect ops state).state
    := by
      simp [operation_list_effect, List.foldl_cons]
      conv => lhs; arg 1; arg 2; unfold operation_effect; simp
      apply operation_effect_state_hyps

    @[simp]
    lemma operation_list_effect_hypotheses_writePC
    :
      (operation_list_effect [.WritePC val] state).hypotheses = True
    := by
      simp [operation_list_effect, operation_effect, Sail.writeReg, PreSail.writeReg]

    @[simp]
    lemma operation_list_effect_hypotheses_writeReg
    :
      (operation_list_effect [.WriteReg reg val] state).hypotheses
        =
      True
    := by
      simp [operation_list_effect, operation_effect]

    lemma operation_list_effect_hypotheses_writeReg_same
      (h_reg : read_xreg (regidx_to_fin reg) state = EStateM.Result.ok val state)
    :
      (operation_list_effect (.WriteReg reg val :: ops) state).hypotheses
        =
      (operation_list_effect ops state).hypotheses
    := by
      simp [operation_list_effect, operation_effect]
      simp [read_xreg] at h_reg; simp [write_xreg]
      by_cases h_r0 : (regidx_to_fin reg).val = 0 <;> simp [h_r0] at h_reg ⊢
      simp [Sail.writeReg, PreSail.writeReg]
      rw [ExtDHashMap.insert_eq_self]; assumption

    lemma operation_list_effect_state_writeReg_same
      (h_reg : read_xreg (regidx_to_fin reg) state = EStateM.Result.ok val state)
    :
      (operation_list_effect (.WriteReg reg val :: ops) state).state
        =
      (operation_list_effect ops state).state
    := by
      simp [operation_list_effect]; congr
      simp [operation_effect]; exists ()
      simp [read_xreg] at h_reg; simp [write_xreg]
      by_cases h_r0 : (regidx_to_fin reg).val = 0 <;> simp [h_r0] at h_reg ⊢
      simp [Sail.writeReg, PreSail.writeReg]; congr
      rw [ExtDHashMap.insert_eq_self]; assumption

    lemma operation_list_effect_state_swap_writePC_writeReg
    :
      (operation_list_effect (.WritePC pc_val :: .WriteReg reg val :: ops) state).state
        =
      (operation_list_effect (.WriteReg reg val :: .WritePC pc_val :: ops) state).state
    := by
      simp [operation_list_effect, List.foldl_cons]
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

  end OperationEffect

  section BusOperations

    open RV32IM_Interactions

    def bus_operations (row : BusRow) : List Operation :=
      let program : List Operation := List.map (fun program_row => .ReadPC (BitVec.ofNatLT (w := 32) program_row.pc (by omega))) row.Program
      let state : List Operation :=
        List.filterMap (
          fun state_row =>
            let value := U32.toBV #v[state_row.x_0, state_row.x_1, state_row.x_2, state_row.x_3]
            if _ : state_row.ptr < 32 then
              (let register : regidx := .Regidx (BitVec.ofNatLT (w := if false = true then 4 else 5) state_row.ptr.val (by simpa))
              if (state_row.multiplicity = -1) then
                .some (.ReadReg register value)
              else if (state_row.multiplicity = 1) then
                .some (.WriteReg register value)
              else .none)
            else
              if (state_row.multiplicity = -1) then
                .some (.ReadMem state_row.ptr.val .Word value)
              else if (state_row.multiplicity = 1) then
                .some (.WriteMem state_row.ptr.val .Word value)
              else .none
        ) row.State
      program ++ state

  end BusOperations

end RV32IM
