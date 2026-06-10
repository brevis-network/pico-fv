import LeanZKCircuit_Plonky3.Interactions

import PicoFV.Fundamentals.KoalaBear

set_option maxHeartbeats 1_000_000_000

attribute [simp]
  List.filter_cons
  List.map_flatMap

attribute [-simp]
  Fin.val_fin_le
  exists_and_left
  exists_and_right
  List.minimum_of_length_pos_le_iff
  List.le_maximum_of_length_pos_iff

attribute [local grind =]
  Fin.add_def
  Fin.neg_def
  Fin.val_natCast

namespace Interaction

  section Buses

    variable
      (F : Type)
      [Field F]

    instance : Inhabited F := by exact Inhabited.mk 0

    /-- Type class for generic bus entries -/
    class BusEntry (α : Type*) where
      multiplicity : α → F

      data_length : ℕ
      data : α → Vector F data_length

      -- Infrastructure-external constraints on bus entries
      axioms : α → Prop

      -- Chip-external, but infrastructure-internal constraints on bus entries
      externals : α → Prop

      -- Well-formedness properties of bus entries
      wf_properties : α → Prop

      -- Condition under which well-formedness properties are assumed
      wf_assume_cond : α → Prop := fun entry => multiplicity entry = -1
      -- Condition under which well-formedness properties need to be asserted
      wf_assert_cond : α → Prop := fun entry => multiplicity entry = 1

      -- Condition under which external properties are assumed
      ext_assume_cond : α → Prop := fun entry => multiplicity entry = 1
      -- Condition under which external properties need to be asserted
      ext_assert_cond : α → Prop := fun entry => multiplicity entry = -1

      -- Assumption and assertion of externals
      ext_assume (a : α) := ext_assume_cond a → externals a
      ext_assert (a : α) := ext_assert_cond a → externals a

      -- Assumption and assertion of well-formedness properties
      wf_assume (a : α) := wf_assume_cond a → wf_properties a
      wf_assert (a : α) := wf_assert_cond a → wf_properties a

      -- Serialisation, deserialisation, inverses
      serialise (x : α) := (multiplicity x, data x)
      serialiseToList (x : α) := (multiplicity x, (data x).toList)
      deserialise : F × Vector F data_length → α

      inv_ser_deser (x : F × Vector F data_length) : serialise (deserialise x) = x
      inv_deser_ser {x : α} : deserialise (serialise x) = x

  end Buses

end Interaction
