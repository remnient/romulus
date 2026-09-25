 

import Std

namespace Romulus

structure Config where
  numGuests : Nat
  numFrames : Nat
  numPages : Nat
  numCaps : Nat
  l1Size : Nat
  l2Size : Nat
  tableShape : l1Size * l2Size = numPages
  l2Pos : l2Size > 0

def referenceConfig : Config := ⟨3, 8, 8, 8, 2, 4, by decide, by decide⟩

instance : NeZero referenceConfig.numGuests := ⟨by decide⟩
instance : NeZero referenceConfig.numFrames := ⟨by decide⟩
instance : NeZero referenceConfig.numPages := ⟨by decide⟩
instance : NeZero referenceConfig.numCaps := ⟨by decide⟩

abbrev GuestId (cfg : Config) := Fin cfg.numGuests

abbrev FrameId (cfg : Config) := Fin cfg.numFrames

abbrev GuestPage (cfg : Config) := Fin cfg.numPages

abbrev CapabilityId (cfg : Config) := Fin cfg.numCaps

abbrev Epoch := Nat

abbrev pageSize : Nat := 64

structure MachineAddress (cfg : Config) where
  frame : FrameId cfg
  offset : Fin pageSize
  deriving DecidableEq, Repr

abbrev PageContents := Fin pageSize → UInt8

def zeroContents : PageContents := fun _ => 0

def setByte (c : PageContents) (off : Fin pageSize) (v : UInt8) : PageContents :=
  fun o => if o = off then v else c o

@[simp] theorem setByte_self (c : PageContents) (off : Fin pageSize) (v : UInt8) :
    setByte c off v off = v := by simp [setByte]

@[simp] theorem setByte_of_ne (c : PageContents) (off : Fin pageSize) (v : UInt8)
    {off' : Fin pageSize} (h : off' ≠ off) : setByte c off v off' = c off' := by
  simp [setByte, h]

structure Permission where
  read : Bool
  write : Bool
  execute : Bool
  deriving DecidableEq, Repr

namespace Permission

def readOnly : Permission := ⟨true, false, false⟩

def readWrite : Permission := ⟨true, true, false⟩

def all : Permission := ⟨true, true, true⟩

def leq (p q : Permission) : Prop :=
  (p.read = true → q.read = true) ∧
  (p.write = true → q.write = true) ∧
  (p.execute = true → q.execute = true)

instance (p q : Permission) : Decidable (leq p q) := by
  unfold leq
  infer_instance

theorem leq_refl (p : Permission) : p.leq p := by
  unfold leq
  exact ⟨fun h => h, fun h => h, fun h => h⟩

theorem leq_trans {p q r : Permission} (hpq : p.leq q) (hqr : q.leq r) : p.leq r := by
  unfold leq at *
  exact ⟨fun h => hqr.1 (hpq.1 h), fun h => hqr.2.1 (hpq.2.1 h), fun h => hqr.2.2 (hpq.2.2 h)⟩

end Permission

end Romulus
