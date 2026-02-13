import Sail

import PicoFV.Fundamentals.Core

attribute [simp]
  get
  getThe
  instMonadStateOfMonadStateOf
  liftM
  modify
  modifyGet
  monadLift
  MonadLift.monadLift
  pure

  Functor.map

  ExceptT.bind
  ExceptT.bindCont
  ExceptT.instMonad
  ExceptT.lift
  ExceptT.map
  ExceptT.mk
  ExceptT.pure
  ExceptT.run

  EStateM.bind
  EStateM.get
  EStateM.map
  EStateM.modifyGet
  EStateM.instMonad
  EStateM.instMonadStateOf
  EStateM.pure

  ExceptT.instMonad ExceptT.pure ExceptT.mk

  Int.le
  Int.neg
  Int.negOfNat
  Int.sub
  Int.tmod_eq_emod

  untilFuelM
  untilFuelM.go

  Sail.BitVec.access
  Sail.BitVec.addInt
  Sail.BitVec.extractLsb
  Sail.BitVec.signExtend
  Sail.BitVec.toNatInt
  Sail.BitVec.updateSubrange
  Sail.BitVec.updateSubrange'
  Sail.BitVec.zeroExtend
  Sail.get_slice_int

  PreSail.ConcurrencyInterfaceV1.sail_mem_read
  PreSail.ConcurrencyInterfaceV1.sail_mem_write
  PreSail.PreSailME.run
  PreSail.readByte
  PreSail.readBytes
  PreSail.writeByte
  PreSail.writeBytes
