 

import romulus.Semantics.Transition

set_option linter.unusedSimpArgs false

namespace Romulus

variable {cfg : Config}

def Step (s : MachineState cfg) (h : Hypercall cfg) (t : MachineState cfg) : Prop :=
  step s h = .ok t

theorem step_allocate_iff (s t : MachineState cfg) (actor : GuestId cfg) (f : FrameId cfg) :
    step s (.allocate actor f) = .ok t ↔
      s.status f = .free ∧
      t = updateFrame s f (.owned actor) zeroContents 0 (s.epoch f) := by
  unfold step
  cases h : s.status f <;> simp [h, eq_comm]

theorem step_map_iff (s t : MachineState cfg) (actor : GuestId cfg) (p : GuestPage cfg)
    (f : FrameId cfg) (perms : Permission) :
    step s (.map actor p f perms) = .ok t ↔
      s.mappings actor p = none ∧
      ((s.status f = .owned actor ∧
          t = installMapping s actor p f perms .ownership) ∨
       (s.status f ≠ .owned actor ∧ capAuthorizes s actor f perms ∧
          t = installMapping s actor p f perms .shared)) := by
  unfold step
  cases hm : s.mappings actor p with
  | some m => simp [hm]
  | none =>
    by_cases hown : s.status f = .owned actor
    · simp [hm, hown, eq_comm]
    · by_cases hc : capAuthorizes s actor f perms
      · simp [hm, hown, hc, eq_comm]
      · by_cases hce : capExistsFor s actor f <;> simp [hm, hown, hc, hce, eq_comm]

theorem step_unmap_iff (s t : MachineState cfg) (actor : GuestId cfg) (p : GuestPage cfg) :
    step s (.unmap actor p) = .ok t ↔
      ∃ m : Mapping cfg, s.mappings actor p = some m ∧
        t = setPendingFlush (setMapping s actor p none) actor p
              (m.frame :: s.pendingFlush actor p) := by
  unfold step
  cases hm : s.mappings actor p with
  | none => simp [hm]
  | some m => simp [hm, eq_comm]

theorem step_share_iff (s t : MachineState cfg) (grantor : GuestId cfg) (c : CapabilityId cfg)
    (f : FrameId cfg) (holder : GuestId cfg) (perms : Permission) :
    step s (.share grantor c f holder perms) = .ok t ↔
      s.shares c = none ∧ s.status f = .owned grantor ∧
      t = setShare s c (some ⟨f, holder, perms, s.epoch f⟩) := by
  unfold step
  cases hs : s.shares c with
  | some cap => simp [hs]
  | none =>
    by_cases hown : s.status f = .owned grantor <;> simp [hs, hown, eq_comm]

theorem step_revoke_iff (s t : MachineState cfg) (c : CapabilityId cfg) :
    step s (.revoke c) = .ok t ↔
      ∃ cap : ShareCapability cfg, s.shares c = some cap ∧ t = revokeState s c cap := by
  unfold step
  cases hs : s.shares c with
  | none => simp [hs]
  | some cap => simp [hs, eq_comm]

theorem step_transfer_iff (s t : MachineState cfg) (f : FrameId cfg) (src dst : GuestId cfg) :
    step s (.transfer f src dst) = .ok t ↔
      src ≠ dst ∧ s.status f = .owned src ∧
      ¬ hasMappingsFrom s src f ∧ s.pins f = 0 ∧
      ¬ tlbReaches s src f ∧ ¬ holdsCapOn s src f ∧
      t = updateFrame s f (.owned dst) (s.contents f) (s.pins f) (s.epoch f) := by
  unfold step
  by_cases hne : src = dst
  · simp [hne]
  · simp only [hne, if_false]
    by_cases hown : s.status f = .owned src
    · simp only [hown, if_true]
      by_cases hm : hasMappingsFrom s src f
      · simp [hm]
      · simp only [hm, if_false]
        by_cases hp : s.pins f = 0
        · simp only [hp, if_true]
          by_cases ht : tlbReaches s src f
          · simp [ht]
          · simp only [ht, if_false]
            by_cases hc : holdsCapOn s src f <;> simp [hc, hne, eq_comm]
        · simp [hp]
    · simp [hown]

theorem step_pin_iff (s t : MachineState cfg) (actor : GuestId cfg) (f : FrameId cfg) :
    step s (.pin actor f) = .ok t ↔
      s.status f = .owned actor ∧ t = setPins s f (s.pins f + 1) := by
  unfold step
  by_cases hown : s.status f = .owned actor <;> simp [hown, eq_comm]

theorem step_unpin_iff (s t : MachineState cfg) (actor : GuestId cfg) (f : FrameId cfg) :
    step s (.unpin actor f) = .ok t ↔
      s.status f = .owned actor ∧ s.pins f > 0 ∧ t = setPins s f (s.pins f - 1) := by
  unfold step
  by_cases hown : s.status f = .owned actor
  · simp only [hown, if_true]
    by_cases hp : s.pins f > 0 <;> simp [hp, eq_comm]
  · simp [hown]

theorem step_beginReclaim_iff (s t : MachineState cfg) (actor : GuestId cfg) (f : FrameId cfg) :
    step s (.beginReclaim actor f) = .ok t ↔
      s.status f = .owned actor ∧ s.pins f = 0 ∧
      t = updateFrame s f (.reclaiming actor) (s.contents f) (s.pins f) (s.epoch f) := by
  unfold step
  by_cases hown : s.status f = .owned actor
  · simp only [hown, if_true]
    by_cases hp : s.pins f = 0 <;> simp [hp, eq_comm]
  · simp [hown]

theorem step_reclaim_iff (s t : MachineState cfg) (f : FrameId cfg) :
    step s (.reclaim f) = .ok t ↔
      (∃ g : GuestId cfg, s.status f = .reclaiming g) ∧
      ¬ hasMappingsTo s f ∧ ¬ hasCapsOn s f ∧ s.pins f = 0 ∧
      ¬ hasTlbRef s f ∧ ¬ hasPendingFlushFor s f ∧
      t = updateFrame s f .free zeroContents 0 (s.epoch f + 1) := by
  unfold step
  by_cases hrec : ∃ g : GuestId cfg, s.status f = .reclaiming g
  · simp only [hrec, if_true]
    by_cases hm : hasMappingsTo s f
    · simp [hm]
    · simp only [hm, if_false]
      by_cases hc : hasCapsOn s f
      · simp [hc]
      · simp only [hc, if_false]
        by_cases hp : s.pins f = 0
        · simp only [hp, if_true]
          by_cases ht : hasTlbRef s f
          · simp [ht]
          · simp only [ht, if_false]
            by_cases hpf : hasPendingFlushFor s f <;> simp [hpf, eq_comm]
        · simp [hp]
  · simp [hrec]

theorem step_flush_iff (s t : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg) :
    step s (.flush g p) = .ok t ↔
      t = setPendingFlush (setTlb s g p none) g p [] := by
  unfold step
  simp [eq_comm]

theorem step_write_iff (s t : MachineState cfg) (actor : GuestId cfg) (p : GuestPage cfg)
    (offset : Fin pageSize) (value : UInt8) :
    step s (.write actor p offset value) = .ok t ↔
      ∃ m : Mapping cfg, s.mappings actor p = some m ∧ m.perms.write = true ∧
        t = setContents s m.frame (setByte (s.contents m.frame) offset value) := by
  unfold step
  cases hm : s.mappings actor p with
  | none => simp [hm]
  | some m =>
      by_cases hw : m.perms.write = true
      · simp only [hm, hw, if_true]
        constructor
        · intro h
          injection h with h
          exact ⟨m, rfl, hw, h.symm⟩
        · rintro ⟨m', hm', hw', ht⟩
          injection hm' with hm''
          subst hm''
          rw [ht]
      · simp [hm, hw]

theorem step_acknowledge_iff (s t : MachineState cfg) (actor : GuestId cfg) :
    step s (.acknowledge actor) = .ok t ↔ t = clearNotifications s actor := by
  unfold step
  simp [eq_comm]

end Romulus
