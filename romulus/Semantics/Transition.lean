 

import romulus.Core.Invariants
import romulus.Semantics.Hypercall

namespace Romulus

variable {cfg : Config}

 
def capExistsFor (s : MachineState cfg) (actor : GuestId cfg) (frame : FrameId cfg) : Prop :=
  ∃ c : CapabilityId cfg, capNamesFrame s actor frame c

def capAuthorizes (s : MachineState cfg) (actor : GuestId cfg) (frame : FrameId cfg)
    (perms : Permission) : Prop :=
  ∃ c : CapabilityId cfg, capGrants s actor frame perms c

def hasMappingsFrom (s : MachineState cfg) (actor : GuestId cfg) (frame : FrameId cfg) : Prop :=
  ∃ p m, s.mappings actor p = some m ∧ m.frame = frame

def hasMappingsTo (s : MachineState cfg) (frame : FrameId cfg) : Prop :=
  ∃ g p m, s.mappings g p = some m ∧ m.frame = frame

def hasCapsOn (s : MachineState cfg) (frame : FrameId cfg) : Prop :=
  ∃ c cap, s.shares c = some cap ∧ cap.frame = frame

def hasTlbRef (s : MachineState cfg) (frame : FrameId cfg) : Prop :=
  ∃ g p e, s.tlb g p = some e ∧ e.frame = frame

def tlbReaches (s : MachineState cfg) (guest : GuestId cfg) (frame : FrameId cfg) : Prop :=
  ∃ p e, s.tlb guest p = some e ∧ e.frame = frame

def holdsCapOn (s : MachineState cfg) (holder : GuestId cfg) (frame : FrameId cfg) : Prop :=
  ∃ c cap, s.shares c = some cap ∧ cap.holder = holder ∧ cap.frame = frame

def hasPendingFlushFor (s : MachineState cfg) (frame : FrameId cfg) : Prop :=
  ∃ g p, frame ∈ s.pendingFlush g p

instance instDecidableCapExistsFor (s : MachineState cfg) (actor : GuestId cfg)
    (frame : FrameId cfg) : Decidable (capExistsFor s actor frame) :=
  inferInstanceAs (Decidable (∃ c : CapabilityId cfg, capNamesFrame s actor frame c))

instance instDecidableCapAuthorizes (s : MachineState cfg) (actor : GuestId cfg)
    (frame : FrameId cfg) (perms : Permission) : Decidable (capAuthorizes s actor frame perms) :=
  inferInstanceAs (Decidable (∃ c : CapabilityId cfg, capGrants s actor frame perms c))

instance instDecidableHasMappingsFrom (s : MachineState cfg) (actor : GuestId cfg)
    (frame : FrameId cfg) : Decidable (hasMappingsFrom s actor frame) :=
  inferInstanceAs (Decidable (∃ p, ∃ m, s.mappings actor p = some m ∧ m.frame = frame))

instance instDecidableHasMappingsTo (s : MachineState cfg) (frame : FrameId cfg) :
    Decidable (hasMappingsTo s frame) :=
  inferInstanceAs (Decidable (∃ g, ∃ p, ∃ m, s.mappings g p = some m ∧ m.frame = frame))

instance instDecidableHasCapsOn (s : MachineState cfg) (frame : FrameId cfg) :
    Decidable (hasCapsOn s frame) :=
  inferInstanceAs (Decidable (∃ c, ∃ cap, s.shares c = some cap ∧ cap.frame = frame))

instance instDecidableHasTlbRef (s : MachineState cfg) (frame : FrameId cfg) :
    Decidable (hasTlbRef s frame) :=
  inferInstanceAs (Decidable (∃ g, ∃ p, ∃ e, s.tlb g p = some e ∧ e.frame = frame))

instance instDecidableTlbReaches (s : MachineState cfg) (guest : GuestId cfg) (frame : FrameId cfg) :
    Decidable (tlbReaches s guest frame) :=
  inferInstanceAs (Decidable (∃ p, ∃ e, s.tlb guest p = some e ∧ e.frame = frame))

instance instDecidableHoldsCapOn (s : MachineState cfg) (holder : GuestId cfg) (frame : FrameId cfg) :
    Decidable (holdsCapOn s holder frame) :=
  inferInstanceAs (Decidable (∃ c, ∃ cap, s.shares c = some cap ∧ cap.holder = holder ∧ cap.frame = frame))

instance instDecidableHasPendingFlushFor (s : MachineState cfg) (frame : FrameId cfg) :
    Decidable (hasPendingFlushFor s frame) :=
  inferInstanceAs (Decidable (∃ g, ∃ p, frame ∈ s.pendingFlush g p))

 
def installMapping (s : MachineState cfg) (actor : GuestId cfg) (p : GuestPage cfg)
    (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin) : MachineState cfg :=
  setTlb (setMapping s actor p (some ⟨f, perms, origin⟩)) actor p (some ⟨f, perms⟩)

def clearNotifications (s : MachineState cfg) (g : GuestId cfg) : MachineState cfg :=
  { s with notifications := fun g' => if g' = g then [] else s.notifications g' }

def revokeState (s : MachineState cfg) (c : CapabilityId cfg) (cap : ShareCapability cfg) :
    MachineState cfg :=
  addNotification
    (dropSharedMappingsFor (recordRevokedFlush (setShare s c none) cap.holder cap.frame)
      cap.holder cap.frame)
    cap.holder (.revocation c cap.frame cap.epoch)

@[simp] theorem installMapping_mappings (s : MachineState cfg) (actor : GuestId cfg)
    (p : GuestPage cfg) (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin) :
    (installMapping s actor p f perms origin).mappings =
      (setMapping s actor p (some ⟨f, perms, origin⟩)).mappings := rfl

@[simp] theorem installMapping_tlb (s : MachineState cfg) (actor : GuestId cfg)
    (p : GuestPage cfg) (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin) :
    (installMapping s actor p f perms origin).tlb =
      (setTlb s actor p (some ⟨f, perms⟩)).tlb := rfl

@[simp] theorem installMapping_status (s : MachineState cfg) (actor : GuestId cfg)
    (p : GuestPage cfg) (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin) :
    (installMapping s actor p f perms origin).status = s.status := rfl

@[simp] theorem installMapping_shares (s : MachineState cfg) (actor : GuestId cfg)
    (p : GuestPage cfg) (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin) :
    (installMapping s actor p f perms origin).shares = s.shares := rfl

@[simp] theorem installMapping_pins (s : MachineState cfg) (actor : GuestId cfg)
    (p : GuestPage cfg) (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin) :
    (installMapping s actor p f perms origin).pins = s.pins := rfl

@[simp] theorem installMapping_epoch (s : MachineState cfg) (actor : GuestId cfg)
    (p : GuestPage cfg) (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin) :
    (installMapping s actor p f perms origin).epoch = s.epoch := rfl

@[simp] theorem installMapping_contents (s : MachineState cfg) (actor : GuestId cfg)
    (p : GuestPage cfg) (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin) :
    (installMapping s actor p f perms origin).contents = s.contents := rfl

@[simp] theorem installMapping_pendingFlush (s : MachineState cfg) (actor : GuestId cfg)
    (p : GuestPage cfg) (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin) :
    (installMapping s actor p f perms origin).pendingFlush = s.pendingFlush := rfl

@[simp] theorem installMapping_notifications (s : MachineState cfg) (actor : GuestId cfg)
    (p : GuestPage cfg) (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin) :
    (installMapping s actor p f perms origin).notifications = s.notifications := rfl

@[simp] theorem installMapping_mappings_self (s : MachineState cfg) (actor : GuestId cfg)
    (p : GuestPage cfg) (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin) :
    (installMapping s actor p f perms origin).mappings actor p = some ⟨f, perms, origin⟩ := by
  simp [installMapping, setMapping]

@[simp] theorem installMapping_tlb_self (s : MachineState cfg) (actor : GuestId cfg)
    (p : GuestPage cfg) (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin) :
    (installMapping s actor p f perms origin).tlb actor p = some ⟨f, perms⟩ := by
  simp [installMapping, setTlb]

theorem installMapping_mappings_of_ne (s : MachineState cfg) (actor : GuestId cfg)
    (p : GuestPage cfg) (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin)
    {g' : GuestId cfg} {p' : GuestPage cfg} (h : ¬(g' = actor ∧ p' = p)) :
    (installMapping s actor p f perms origin).mappings g' p' = s.mappings g' p' := by
  simp only [installMapping_mappings]
  exact setMapping_mappings_of_ne s actor p (some ⟨f, perms, origin⟩) h

theorem installMapping_tlb_of_ne (s : MachineState cfg) (actor : GuestId cfg)
    (p : GuestPage cfg) (f : FrameId cfg) (perms : Permission) (origin : MappingOrigin)
    {g' : GuestId cfg} {p' : GuestPage cfg} (h : ¬(g' = actor ∧ p' = p)) :
    (installMapping s actor p f perms origin).tlb g' p' = s.tlb g' p' := by
  simp only [installMapping_tlb]
  by_cases hg : g' = actor
  · have hp : p' ≠ p := fun hp => h ⟨hg, hp⟩
    subst hg; simp [setTlb, hp]
  · simp [setTlb, hg]

@[simp] theorem clearNotifications_self (s : MachineState cfg) (g : GuestId cfg) :
    (clearNotifications s g).notifications g = [] := by simp [clearNotifications]

@[simp] theorem clearNotifications_of_ne (s : MachineState cfg) (g : GuestId cfg)
    {g' : GuestId cfg} (h : g' ≠ g) : (clearNotifications s g).notifications g' = s.notifications g' := by
  simp [clearNotifications, h]

@[simp] theorem clearNotifications_status (s : MachineState cfg) (g : GuestId cfg) :
    (clearNotifications s g).status = s.status := rfl
@[simp] theorem clearNotifications_mappings (s : MachineState cfg) (g : GuestId cfg) :
    (clearNotifications s g).mappings = s.mappings := rfl
@[simp] theorem clearNotifications_shares (s : MachineState cfg) (g : GuestId cfg) :
    (clearNotifications s g).shares = s.shares := rfl
@[simp] theorem clearNotifications_pins (s : MachineState cfg) (g : GuestId cfg) :
    (clearNotifications s g).pins = s.pins := rfl
@[simp] theorem clearNotifications_epoch (s : MachineState cfg) (g : GuestId cfg) :
    (clearNotifications s g).epoch = s.epoch := rfl
@[simp] theorem clearNotifications_contents (s : MachineState cfg) (g : GuestId cfg) :
    (clearNotifications s g).contents = s.contents := rfl
@[simp] theorem clearNotifications_tlb (s : MachineState cfg) (g : GuestId cfg) :
    (clearNotifications s g).tlb = s.tlb := rfl
@[simp] theorem clearNotifications_pendingFlush (s : MachineState cfg) (g : GuestId cfg) :
    (clearNotifications s g).pendingFlush = s.pendingFlush := rfl

@[simp] theorem revokeState_status (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : ShareCapability cfg) : (revokeState s c cap).status = s.status := rfl

@[simp] theorem revokeState_shares (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : ShareCapability cfg) : (revokeState s c cap).shares = (setShare s c none).shares := rfl

@[simp] theorem revokeState_pins (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : ShareCapability cfg) : (revokeState s c cap).pins = s.pins := rfl

@[simp] theorem revokeState_epoch (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : ShareCapability cfg) : (revokeState s c cap).epoch = s.epoch := rfl

@[simp] theorem revokeState_contents (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : ShareCapability cfg) : (revokeState s c cap).contents = s.contents := rfl

@[simp] theorem revokeState_tlb (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : ShareCapability cfg) : (revokeState s c cap).tlb = s.tlb := rfl

@[simp] theorem revokeState_mappings (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : ShareCapability cfg) :
    (revokeState s c cap).mappings =
      (dropSharedMappingsFor (recordRevokedFlush (setShare s c none) cap.holder cap.frame)
        cap.holder cap.frame).mappings := rfl

theorem revokeState_notifications_holder (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : ShareCapability cfg) :
    (revokeState s c cap).notifications cap.holder =
      .revocation c cap.frame cap.epoch :: s.notifications cap.holder := by
  simp [revokeState, addNotification]

theorem WellFormed.clearNotifications {s : MachineState cfg} (hwf : WellFormed s)
    (g : GuestId cfg) : WellFormed (clearNotifications s g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g' p m hm; exact hwf.mapping_authority g' p m (by simpa using hm)
  · intro c cap hc; exact hwf.capability_epoch c cap (by simpa using hc)
  · intro c cap hc; exact hwf.capability_allocated c cap (by simpa using hc)
  · intro f hp; exact hwf.pins_owned f (by simpa using hp)
  · intro f g' hst; exact hwf.reclaiming_unpinned f g' (by simpa using hst)
  · intro g' p e he; exact hwf.tlb_allocated g' p e (by simpa using he)
  · intro f hv; exact hwf.vacant_unreferenced f (by simpa using hv)

theorem WellFormed.addNotification {s : MachineState cfg} (hwf : WellFormed s)
    (g : GuestId cfg) (n : Notice cfg) : WellFormed (addNotification s g n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g' p m hm; exact hwf.mapping_authority g' p m (by simpa using hm)
  · intro c cap hc; exact hwf.capability_epoch c cap (by simpa using hc)
  · intro c cap hc; exact hwf.capability_allocated c cap (by simpa using hc)
  · intro f hp; exact hwf.pins_owned f (by simpa using hp)
  · intro f g' hst; exact hwf.reclaiming_unpinned f g' (by simpa using hst)
  · intro g' p e he; exact hwf.tlb_allocated g' p e (by simpa using he)
  · intro f hv; exact hwf.vacant_unreferenced f (by simpa using hv)

theorem capAuthorizes_allocated {s : MachineState cfg} (hwf : WellFormed s)
    {actor : GuestId cfg} {f : FrameId cfg} {perms : Permission}
    (h : capAuthorizes s actor f perms) :
    ∃ g : GuestId cfg, s.status f = .owned g ∨ s.status f = .reclaiming g := by
  obtain ⟨c, hc⟩ := h
  simp only [capGrants] at hc
  cases hsh : s.shares c with
  | none => simp only [hsh] at hc
  | some cap =>
      simp only [hsh] at hc
      obtain ⟨-, hcframe, -, -⟩ := hc
      rw [← hcframe]
      exact hwf.capability_allocated c cap hsh

 
def step (s : MachineState cfg) : Hypercall cfg → Except HypervisorError (MachineState cfg)
  | .allocate actor f =>
      match s.status f with
      | .free => .ok (updateFrame s f (.owned actor) zeroContents 0 (s.epoch f))
      | .reserved => .error .frameNotFree
      | .owned _ => .error .frameNotFree
      | .reclaiming _ => .error .frameNotFree
  | .map actor p f perms =>
      match s.mappings actor p with
      | some _ => .error .pageAlreadyMapped
      | none =>
        if s.status f = .owned actor then
          .ok (installMapping s actor p f perms .ownership)
        else if capAuthorizes s actor f perms then
          .ok (installMapping s actor p f perms .shared)
        else if capExistsFor s actor f then
          .error .insufficientPermission
        else
          .error .notAuthorized
  | .unmap actor p =>
      match s.mappings actor p with
      | none => .error .pageNotMapped
      | some m =>
          .ok (setPendingFlush (setMapping s actor p none) actor p (m.frame :: s.pendingFlush actor p))
  | .share grantor c f holder perms =>
      match s.shares c with
      | some _ => .error .capabilitySlotOccupied
      | none =>
        if s.status f = .owned grantor then
          .ok (setShare s c (some ⟨f, holder, perms, s.epoch f⟩))
        else .error .notAuthorized
  | .revoke c =>
      match s.shares c with
      | none => .error .capabilityUnknown
      | some cap => .ok (revokeState s c cap)
  | .transfer f src dst =>
      if src = dst then .error .invalidTransfer
      else if s.status f = .owned src then
        if hasMappingsFrom s src f then .error .frameMapped
        else if s.pins f = 0 then
          if tlbReaches s src f then .error .staleTranslation
          else if holdsCapOn s src f then .error .frameShared
          else .ok (updateFrame s f (.owned dst) (s.contents f) (s.pins f) (s.epoch f))
        else .error .framePinned
      else .error .frameNotOwned
  | .pin actor f =>
      if s.status f = .owned actor then .ok (setPins s f (s.pins f + 1))
      else .error .frameNotOwned
  | .unpin actor f =>
      if s.status f = .owned actor then
        if s.pins f > 0 then .ok (setPins s f (s.pins f - 1)) else .error .frameNotPinned
      else .error .frameNotOwned
  | .beginReclaim actor f =>
      if s.status f = .owned actor then
        if s.pins f = 0 then
          .ok (updateFrame s f (.reclaiming actor) (s.contents f) (s.pins f) (s.epoch f))
        else .error .framePinned
      else .error .frameNotOwned
  | .reclaim f =>
      if ∃ g : GuestId cfg, s.status f = .reclaiming g then
        if hasMappingsTo s f then .error .frameMapped
        else if hasCapsOn s f then .error .frameShared
        else if s.pins f = 0 then
          if hasTlbRef s f then .error .staleTranslation
          else if hasPendingFlushFor s f then .error .invalidationPending
          else .ok (updateFrame s f .free zeroContents 0 (s.epoch f + 1))
        else .error .framePinned
      else .error .frameNotReclaiming
  | .flush g p => .ok (setPendingFlush (setTlb s g p none) g p [])
  | .write actor p offset value =>
      match s.mappings actor p with
      | none => .error .pageNotMapped
      | some m =>
          if m.perms.write then
            .ok (setContents s m.frame (setByte (s.contents m.frame) offset value))
          else .error .insufficientPermission
  | .acknowledge actor => .ok (clearNotifications s actor)

end Romulus
