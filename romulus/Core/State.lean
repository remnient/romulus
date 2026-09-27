 

import romulus.Core.Types

namespace Romulus

variable {cfg : Config}

inductive FrameStatus (cfg : Config) where
  | free
  | reserved
  | owned (guest : GuestId cfg)
  | reclaiming (guest : GuestId cfg)
  deriving DecidableEq, Repr

inductive MappingOrigin where
  | ownership
  | shared
  deriving DecidableEq, Repr

structure Mapping (cfg : Config) where
  frame : FrameId cfg
  perms : Permission
  origin : MappingOrigin
  deriving DecidableEq, Repr

structure ShareCapability (cfg : Config) where
  frame : FrameId cfg
  holder : GuestId cfg
  perms : Permission
  epoch : Epoch
  deriving DecidableEq, Repr

structure TlbEntry (cfg : Config) where
  frame : FrameId cfg
  perms : Permission
  deriving DecidableEq, Repr

inductive InterruptKind where
  | ipi
  | timer
  | io
  deriving DecidableEq, Repr

inductive Notice (cfg : Config) where
  | revocation (cap : CapabilityId cfg) (frame : FrameId cfg) (epoch : Epoch)
  | interrupt (kind : InterruptKind)
  deriving DecidableEq, Repr

structure MachineState (cfg : Config) where
  status : FrameId cfg → FrameStatus cfg
  mappings : GuestId cfg → GuestPage cfg → Option (Mapping cfg)
  shares : CapabilityId cfg → Option (ShareCapability cfg)
  pins : FrameId cfg → Nat
  epoch : FrameId cfg → Epoch
  contents : FrameId cfg → PageContents
  tlb : GuestId cfg → GuestPage cfg → Option (TlbEntry cfg)
  pendingFlush : GuestId cfg → GuestPage cfg → List (FrameId cfg)
  notifications : GuestId cfg → List (Notice cfg)

def emptyState (cfg : Config) : MachineState cfg where
  status := fun _ => .free
  mappings := fun _ _ => none
  shares := fun _ => none
  pins := fun _ => 0
  epoch := fun _ => 0
  contents := fun _ => zeroContents
  tlb := fun _ _ => none
  pendingFlush := fun _ _ => []
  notifications := fun _ => []

 
def setStatus (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg) :
    MachineState cfg :=
  { s with status := fun f' => if f' = f then st else s.status f' }

def setPins (s : MachineState cfg) (f : FrameId cfg) (n : Nat) : MachineState cfg :=
  { s with pins := fun f' => if f' = f then n else s.pins f' }

def setContents (s : MachineState cfg) (f : FrameId cfg) (c : PageContents) :
    MachineState cfg :=
  { s with contents := fun f' => if f' = f then c else s.contents f' }

def setEpoch (s : MachineState cfg) (f : FrameId cfg) (e : Epoch) : MachineState cfg :=
  { s with epoch := fun f' => if f' = f then e else s.epoch f' }

def setMapping (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (m : Option (Mapping cfg)) : MachineState cfg :=
  { s with mappings := fun g' p' =>
      if g' = g ∧ p' = p then m else s.mappings g' p' }

def setTlb (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (e : Option (TlbEntry cfg)) : MachineState cfg :=
  { s with tlb := fun g' p' =>
      if g' = g ∧ p' = p then e else s.tlb g' p' }

def setPendingFlush (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (l : List (FrameId cfg)) : MachineState cfg :=
  { s with pendingFlush := fun g' p' =>
      if g' = g ∧ p' = p then l else s.pendingFlush g' p' }

def addNotification (s : MachineState cfg) (g : GuestId cfg)
    (n : Notice cfg) : MachineState cfg :=
  { s with notifications := fun g' => if g' = g then n :: s.notifications g' else s.notifications g' }

def setShare (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : Option (ShareCapability cfg)) : MachineState cfg :=
  { s with shares := fun c' => if c' = c then cap else s.shares c' }

def updateFrame (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg)
    (c : PageContents) (pin : Nat) (ep : Epoch) : MachineState cfg :=
  { s with status := fun f' => if f' = f then st else s.status f',
           contents := fun f' => if f' = f then c else s.contents f',
           pins := fun f' => if f' = f then pin else s.pins f',
           epoch := fun f' => if f' = f then ep else s.epoch f' }

def dropSharedMappingsFor (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : MachineState cfg :=
  { s with mappings := fun g p =>
      if g = holder then
        match s.mappings g p with
        | some m => if m.origin = .shared ∧ m.frame = frame then none else some m
        | none => none
      else s.mappings g p }

def recordRevokedFlush (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : MachineState cfg :=
  { s with pendingFlush := fun g p =>
      if g = holder then
        match s.mappings g p with
        | some m => if m.origin = .shared ∧ m.frame = frame then m.frame :: s.pendingFlush g p
                    else s.pendingFlush g p
        | none => s.pendingFlush g p
      else s.pendingFlush g p }

 
def translationOf (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    : Option (FrameId cfg × Permission) :=
  (s.mappings g p).map (fun m => (m.frame, m.perms))

def cachedTranslationOf (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    : Option (FrameId cfg × Permission) :=
  (s.tlb g p).map (fun e => (e.frame, e.perms))

def readVia (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg) : Option PageContents :=
  match s.tlb g p with
  | some e => if e.perms.read then some (s.contents e.frame) else none
  | none =>
    match s.mappings g p with
    | some m => if m.perms.read then some (s.contents m.frame) else none
    | none => none

def ownsFrame (s : MachineState cfg) (g : GuestId cfg) (f : FrameId cfg) : Prop :=
  s.status f = .owned g

def reachableFrame (s : MachineState cfg) (g : GuestId cfg) (f : FrameId cfg) : Prop :=
  (∃ p, ∃ m, s.mappings g p = some m ∧ m.frame = f) ∨
  (∃ p, ∃ e, s.tlb g p = some e ∧ e.frame = f)

def contentsAt (s : MachineState cfg) (a : MachineAddress cfg) : UInt8 :=
  s.contents a.frame a.offset

abbrev capNamesFrame (s : MachineState cfg) (actor : GuestId cfg) (frame : FrameId cfg)
    (c : CapabilityId cfg) : Prop :=
  match s.shares c with
  | some cap => cap.holder = actor ∧ cap.frame = frame ∧ cap.epoch = s.epoch frame
  | none => False

abbrev capGrants (s : MachineState cfg) (actor : GuestId cfg) (frame : FrameId cfg)
    (perms : Permission) (c : CapabilityId cfg) : Prop :=
  match s.shares c with
  | some cap => cap.holder = actor ∧ cap.frame = frame ∧
                cap.epoch = s.epoch frame ∧ perms.leq cap.perms
  | none => False

def capNamesFrameB (s : MachineState cfg) (actor : GuestId cfg) (frame : FrameId cfg)
    (c : CapabilityId cfg) : Bool :=
  match s.shares c with
  | some cap => decide (cap.holder = actor ∧ cap.frame = frame ∧ cap.epoch = s.epoch frame)
  | none => false

theorem capNamesFrameB_eq (s : MachineState cfg) (actor : GuestId cfg) (frame : FrameId cfg)
    (c : CapabilityId cfg) :
    capNamesFrame s actor frame c ↔ capNamesFrameB s actor frame c = true := by
  cases h : s.shares c <;> simp [capNamesFrame, capNamesFrameB, h, decide_eq_true_eq]

instance instDecidableCapNamesFrame (s : MachineState cfg) (actor : GuestId cfg)
    (frame : FrameId cfg) (c : CapabilityId cfg) : Decidable (capNamesFrame s actor frame c) :=
  decidable_of_iff (capNamesFrameB s actor frame c = true) (capNamesFrameB_eq s actor frame c).symm

def capGrantsB (s : MachineState cfg) (actor : GuestId cfg) (frame : FrameId cfg)
    (perms : Permission) (c : CapabilityId cfg) : Bool :=
  match s.shares c with
  | some cap => decide (cap.holder = actor ∧ cap.frame = frame ∧
                        cap.epoch = s.epoch frame ∧ perms.leq cap.perms)
  | none => false

theorem capGrantsB_eq (s : MachineState cfg) (actor : GuestId cfg) (frame : FrameId cfg)
    (perms : Permission) (c : CapabilityId cfg) :
    capGrants s actor frame perms c ↔ capGrantsB s actor frame perms c = true := by
  cases h : s.shares c <;> simp [capGrants, capGrantsB, h, decide_eq_true_eq]

instance instDecidableCapGrants (s : MachineState cfg) (actor : GuestId cfg) (frame : FrameId cfg)
    (perms : Permission) (c : CapabilityId cfg) : Decidable (capGrants s actor frame perms c) :=
  decidable_of_iff (capGrantsB s actor frame perms c = true) (capGrantsB_eq s actor frame perms c).symm

@[simp] theorem setStatus_self (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg) :
    (setStatus s f st).status f = st := by simp [setStatus]

@[simp] theorem setStatus_of_ne (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg)
    {f' : FrameId cfg} (h : f' ≠ f) : (setStatus s f st).status f' = s.status f' := by
  simp [setStatus, h]

@[simp] theorem setPins_self (s : MachineState cfg) (f : FrameId cfg) (n : Nat) :
    (setPins s f n).pins f = n := by simp [setPins]

@[simp] theorem setPins_of_ne (s : MachineState cfg) (f : FrameId cfg) (n : Nat)
    {f' : FrameId cfg} (h : f' ≠ f) : (setPins s f n).pins f' = s.pins f' := by
  simp [setPins, h]

@[simp] theorem setContents_self (s : MachineState cfg) (f : FrameId cfg) (c : PageContents) :
    (setContents s f c).contents f = c := by simp [setContents]

@[simp] theorem setContents_of_ne (s : MachineState cfg) (f : FrameId cfg) (c : PageContents)
    {f' : FrameId cfg} (h : f' ≠ f) : (setContents s f c).contents f' = s.contents f' := by
  simp [setContents, h]

@[simp] theorem setEpoch_self (s : MachineState cfg) (f : FrameId cfg) (e : Epoch) :
    (setEpoch s f e).epoch f = e := by simp [setEpoch]

@[simp] theorem setEpoch_of_ne (s : MachineState cfg) (f : FrameId cfg) (e : Epoch)
    {f' : FrameId cfg} (h : f' ≠ f) : (setEpoch s f e).epoch f' = s.epoch f' := by
  simp [setEpoch, h]

@[simp] theorem setMapping_self (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (m : Option (Mapping cfg)) : (setMapping s g p m).mappings g p = m := by simp [setMapping]

@[simp] theorem setMapping_of_guest_ne (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (m : Option (Mapping cfg)) {g' : GuestId cfg} (h : g' ≠ g) :
    (setMapping s g p m).mappings g' p' = s.mappings g' p' := by simp [setMapping, h]

@[simp] theorem setMapping_of_page_ne (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (m : Option (Mapping cfg)) {p' : GuestPage cfg} (h : p' ≠ p) :
    (setMapping s g p m).mappings g p' = s.mappings g p' := by simp [setMapping, h]

theorem setMapping_mappings_of_ne (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (m : Option (Mapping cfg)) {g' : GuestId cfg} {p' : GuestPage cfg}
    (h : ¬(g' = g ∧ p' = p)) :
    (setMapping s g p m).mappings g' p' = s.mappings g' p' := by
  by_cases hg : g' = g
  · have hp : p' ≠ p := fun hp => h ⟨hg, hp⟩
    subst hg; simp [setMapping, hp]
  · simp [setMapping, hg]

@[simp] theorem setTlb_self (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (e : Option (TlbEntry cfg)) : (setTlb s g p e).tlb g p = e := by simp [setTlb]

@[simp] theorem setTlb_of_guest_ne (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (e : Option (TlbEntry cfg)) {g' : GuestId cfg} (h : g' ≠ g) :
    (setTlb s g p e).tlb g' p' = s.tlb g' p' := by simp [setTlb, h]

@[simp] theorem setTlb_of_page_ne (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (e : Option (TlbEntry cfg)) {p' : GuestPage cfg} (h : p' ≠ p) :
    (setTlb s g p e).tlb g p' = s.tlb g p' := by simp [setTlb, h]

theorem setTlb_tlb_of_ne (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (e : Option (TlbEntry cfg)) {g' : GuestId cfg} {p' : GuestPage cfg}
    (h : ¬(g' = g ∧ p' = p)) : (setTlb s g p e).tlb g' p' = s.tlb g' p' := by
  by_cases hg : g' = g
  · have hp : p' ≠ p := fun hp => h ⟨hg, hp⟩
    subst hg; simp [setTlb, hp]
  · simp [setTlb, hg]

@[simp] theorem setPendingFlush_self (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (l : List (FrameId cfg)) : (setPendingFlush s g p l).pendingFlush g p = l := by
  simp [setPendingFlush]

@[simp] theorem setPendingFlush_of_guest_ne (s : MachineState cfg) (g : GuestId cfg)
    (p : GuestPage cfg) (l : List (FrameId cfg)) {g' : GuestId cfg} (h : g' ≠ g) :
    (setPendingFlush s g p l).pendingFlush g' p' = s.pendingFlush g' p' := by
  simp [setPendingFlush, h]

@[simp] theorem setPendingFlush_of_page_ne (s : MachineState cfg) (g : GuestId cfg)
    (p : GuestPage cfg) (l : List (FrameId cfg)) {p' : GuestPage cfg} (h : p' ≠ p) :
    (setPendingFlush s g p l).pendingFlush g p' = s.pendingFlush g p' := by
  simp [setPendingFlush, h]

@[simp] theorem addNotification_self (s : MachineState cfg) (g : GuestId cfg)
    (n : Notice cfg) : (addNotification s g n).notifications g = n :: s.notifications g := by
  simp [addNotification]

@[simp] theorem addNotification_of_ne (s : MachineState cfg) (g : GuestId cfg)
    (n : Notice cfg) {g' : GuestId cfg} (h : g' ≠ g) :
    (addNotification s g n).notifications g' = s.notifications g' := by
  simp [addNotification, h]

@[simp] theorem addNotification_status (s : MachineState cfg) (g : GuestId cfg) (n : Notice cfg) :
    (addNotification s g n).status = s.status := rfl
@[simp] theorem addNotification_mappings (s : MachineState cfg) (g : GuestId cfg) (n : Notice cfg) :
    (addNotification s g n).mappings = s.mappings := rfl
@[simp] theorem addNotification_shares (s : MachineState cfg) (g : GuestId cfg) (n : Notice cfg) :
    (addNotification s g n).shares = s.shares := rfl
@[simp] theorem addNotification_pins (s : MachineState cfg) (g : GuestId cfg) (n : Notice cfg) :
    (addNotification s g n).pins = s.pins := rfl
@[simp] theorem addNotification_epoch (s : MachineState cfg) (g : GuestId cfg) (n : Notice cfg) :
    (addNotification s g n).epoch = s.epoch := rfl
@[simp] theorem addNotification_contents (s : MachineState cfg) (g : GuestId cfg) (n : Notice cfg) :
    (addNotification s g n).contents = s.contents := rfl
@[simp] theorem addNotification_tlb (s : MachineState cfg) (g : GuestId cfg) (n : Notice cfg) :
    (addNotification s g n).tlb = s.tlb := rfl
@[simp] theorem addNotification_pendingFlush (s : MachineState cfg) (g : GuestId cfg) (n : Notice cfg) :
    (addNotification s g n).pendingFlush = s.pendingFlush := rfl

@[simp] theorem setShare_self (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : Option (ShareCapability cfg)) : (setShare s c cap).shares c = cap := by simp [setShare]

@[simp] theorem setShare_of_ne (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : Option (ShareCapability cfg)) {c' : CapabilityId cfg} (h : c' ≠ c) :
    (setShare s c cap).shares c' = s.shares c' := by simp [setShare, h]

@[simp] theorem updateFrame_status_self (s : MachineState cfg) (f : FrameId cfg)
    (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch) :
    (updateFrame s f st c pin ep).status f = st := by simp [updateFrame]

@[simp] theorem updateFrame_status_of_ne (s : MachineState cfg) (f : FrameId cfg)
    (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch) {f' : FrameId cfg}
    (h : f' ≠ f) : (updateFrame s f st c pin ep).status f' = s.status f' := by
  simp [updateFrame, h]

@[simp] theorem updateFrame_contents_self (s : MachineState cfg) (f : FrameId cfg)
    (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch) :
    (updateFrame s f st c pin ep).contents f = c := by simp [updateFrame]

@[simp] theorem updateFrame_contents_of_ne (s : MachineState cfg) (f : FrameId cfg)
    (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch) {f' : FrameId cfg}
    (h : f' ≠ f) : (updateFrame s f st c pin ep).contents f' = s.contents f' := by
  simp [updateFrame, h]

@[simp] theorem updateFrame_pins_self (s : MachineState cfg) (f : FrameId cfg)
    (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch) :
    (updateFrame s f st c pin ep).pins f = pin := by simp [updateFrame]

@[simp] theorem updateFrame_pins_of_ne (s : MachineState cfg) (f : FrameId cfg)
    (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch) {f' : FrameId cfg}
    (h : f' ≠ f) : (updateFrame s f st c pin ep).pins f' = s.pins f' := by
  simp [updateFrame, h]

@[simp] theorem updateFrame_epoch_self (s : MachineState cfg) (f : FrameId cfg)
    (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch) :
    (updateFrame s f st c pin ep).epoch f = ep := by simp [updateFrame]

@[simp] theorem updateFrame_epoch_of_ne (s : MachineState cfg) (f : FrameId cfg)
    (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch) {f' : FrameId cfg}
    (h : f' ≠ f) : (updateFrame s f st c pin ep).epoch f' = s.epoch f' := by
  simp [updateFrame, h]

@[simp] theorem updateFrame_mappings (s : MachineState cfg) (f : FrameId cfg)
    (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch) :
    (updateFrame s f st c pin ep).mappings = s.mappings := rfl

@[simp] theorem updateFrame_shares (s : MachineState cfg) (f : FrameId cfg)
    (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch) :
    (updateFrame s f st c pin ep).shares = s.shares := rfl

@[simp] theorem updateFrame_tlb (s : MachineState cfg) (f : FrameId cfg)
    (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch) :
    (updateFrame s f st c pin ep).tlb = s.tlb := rfl

@[simp] theorem updateFrame_pendingFlush (s : MachineState cfg) (f : FrameId cfg)
    (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch) :
    (updateFrame s f st c pin ep).pendingFlush = s.pendingFlush := rfl

@[simp] theorem updateFrame_notifications (s : MachineState cfg) (f : FrameId cfg)
    (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch) :
    (updateFrame s f st c pin ep).notifications = s.notifications := rfl

theorem updateFrame_contents_same (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg)
    (pin : Nat) (ep : Epoch) :
    (updateFrame s f st (s.contents f) pin ep).contents = s.contents := by
  funext f'
  by_cases h : f' = f <;> simp [updateFrame, h]

theorem ownsFrame_updateFrame_self (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg)
    (c : PageContents) (pin : Nat) (ep : Epoch) (g : GuestId cfg) :
    (ownsFrame (updateFrame s f st c pin ep) g f ↔ st = .owned g) := by
  unfold ownsFrame; rw [updateFrame_status_self]

theorem ownsFrame_updateFrame_ne (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg)
    (c : PageContents) (pin : Nat) (ep : Epoch) (g : GuestId cfg) {f' : FrameId cfg}
    (h : f' ≠ f) :
    (ownsFrame (updateFrame s f st c pin ep) g f' ↔ ownsFrame s g f') := by
  unfold ownsFrame; rw [updateFrame_status_of_ne s f st c pin ep h]

theorem dropSharedMappingsFor_mappings_holder (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) (p : GuestPage cfg) :
    (dropSharedMappingsFor s holder frame).mappings holder p =
      (match s.mappings holder p with
       | some m => if m.origin = .shared ∧ m.frame = frame then none else some m
       | none => none) := by
  simp [dropSharedMappingsFor]

theorem dropSharedMappingsFor_mappings_other (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) {g : GuestId cfg} (h : g ≠ holder) (p : GuestPage cfg) :
    (dropSharedMappingsFor s holder frame).mappings g p = s.mappings g p := by
  simp [dropSharedMappingsFor, h]

theorem dropSharedMappingsFor_mappings_some (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) {g : GuestId cfg} {p : GuestPage cfg} {m : Mapping cfg}
    (hm : (dropSharedMappingsFor s holder frame).mappings g p = some m) :
    s.mappings g p = some m ∧ (g = holder → ¬(m.origin = .shared ∧ m.frame = frame)) := by
  by_cases hg : g = holder
  · rw [hg] at hm ⊢
    rw [dropSharedMappingsFor_mappings_holder] at hm
    cases hs : s.mappings holder p with
    | none => simp [hs] at hm
    | some m0 =>
        simp only [hs] at hm
        by_cases hd : m0.origin = .shared ∧ m0.frame = frame
        · simp [hd] at hm
        · simp only [hd, if_false] at hm
          injection hm with hm'
          subst hm'
          exact ⟨rfl, fun _ => hd⟩
  · rw [dropSharedMappingsFor_mappings_other s holder frame hg] at hm
    exact ⟨hm, fun h => absurd h hg⟩

theorem recordRevokedFlush_pendingFlush_holder (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) (p : GuestPage cfg) :
    (recordRevokedFlush s holder frame).pendingFlush holder p =
      (match s.mappings holder p with
       | some m => if m.origin = .shared ∧ m.frame = frame then m.frame :: s.pendingFlush holder p
                   else s.pendingFlush holder p
       | none => s.pendingFlush holder p) := by
  simp [recordRevokedFlush]

theorem recordRevokedFlush_pendingFlush_other (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) {g : GuestId cfg} (h : g ≠ holder) (p : GuestPage cfg) :
    (recordRevokedFlush s holder frame).pendingFlush g p = s.pendingFlush g p := by
  simp [recordRevokedFlush, h]

@[simp] theorem setStatus_mappings (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg) :
    (setStatus s f st).mappings = s.mappings := rfl
@[simp] theorem setStatus_shares (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg) :
    (setStatus s f st).shares = s.shares := rfl
@[simp] theorem setStatus_pins (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg) :
    (setStatus s f st).pins = s.pins := rfl
@[simp] theorem setStatus_epoch (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg) :
    (setStatus s f st).epoch = s.epoch := rfl
@[simp] theorem setStatus_contents (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg) :
    (setStatus s f st).contents = s.contents := rfl
@[simp] theorem setStatus_tlb (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg) :
    (setStatus s f st).tlb = s.tlb := rfl
@[simp] theorem setStatus_pendingFlush (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg) :
    (setStatus s f st).pendingFlush = s.pendingFlush := rfl
@[simp] theorem setStatus_notifications (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg) :
    (setStatus s f st).notifications = s.notifications := rfl

@[simp] theorem setPins_status (s : MachineState cfg) (f : FrameId cfg) (n : Nat) :
    (setPins s f n).status = s.status := rfl
@[simp] theorem setPins_mappings (s : MachineState cfg) (f : FrameId cfg) (n : Nat) :
    (setPins s f n).mappings = s.mappings := rfl
@[simp] theorem setPins_shares (s : MachineState cfg) (f : FrameId cfg) (n : Nat) :
    (setPins s f n).shares = s.shares := rfl
@[simp] theorem setPins_epoch (s : MachineState cfg) (f : FrameId cfg) (n : Nat) :
    (setPins s f n).epoch = s.epoch := rfl
@[simp] theorem setPins_contents (s : MachineState cfg) (f : FrameId cfg) (n : Nat) :
    (setPins s f n).contents = s.contents := rfl
@[simp] theorem setPins_tlb (s : MachineState cfg) (f : FrameId cfg) (n : Nat) :
    (setPins s f n).tlb = s.tlb := rfl
@[simp] theorem setPins_pendingFlush (s : MachineState cfg) (f : FrameId cfg) (n : Nat) :
    (setPins s f n).pendingFlush = s.pendingFlush := rfl
@[simp] theorem setPins_notifications (s : MachineState cfg) (f : FrameId cfg) (n : Nat) :
    (setPins s f n).notifications = s.notifications := rfl

@[simp] theorem setContents_status (s : MachineState cfg) (f : FrameId cfg) (c : PageContents) :
    (setContents s f c).status = s.status := rfl
@[simp] theorem setContents_mappings (s : MachineState cfg) (f : FrameId cfg) (c : PageContents) :
    (setContents s f c).mappings = s.mappings := rfl
@[simp] theorem setContents_shares (s : MachineState cfg) (f : FrameId cfg) (c : PageContents) :
    (setContents s f c).shares = s.shares := rfl
@[simp] theorem setContents_pins (s : MachineState cfg) (f : FrameId cfg) (c : PageContents) :
    (setContents s f c).pins = s.pins := rfl
@[simp] theorem setContents_epoch (s : MachineState cfg) (f : FrameId cfg) (c : PageContents) :
    (setContents s f c).epoch = s.epoch := rfl
@[simp] theorem setContents_tlb (s : MachineState cfg) (f : FrameId cfg) (c : PageContents) :
    (setContents s f c).tlb = s.tlb := rfl
@[simp] theorem setContents_pendingFlush (s : MachineState cfg) (f : FrameId cfg) (c : PageContents) :
    (setContents s f c).pendingFlush = s.pendingFlush := rfl
@[simp] theorem setContents_notifications (s : MachineState cfg) (f : FrameId cfg) (c : PageContents) :
    (setContents s f c).notifications = s.notifications := rfl

@[simp] theorem setEpoch_status (s : MachineState cfg) (f : FrameId cfg) (e : Epoch) :
    (setEpoch s f e).status = s.status := rfl
@[simp] theorem setEpoch_mappings (s : MachineState cfg) (f : FrameId cfg) (e : Epoch) :
    (setEpoch s f e).mappings = s.mappings := rfl
@[simp] theorem setEpoch_shares (s : MachineState cfg) (f : FrameId cfg) (e : Epoch) :
    (setEpoch s f e).shares = s.shares := rfl
@[simp] theorem setEpoch_pins (s : MachineState cfg) (f : FrameId cfg) (e : Epoch) :
    (setEpoch s f e).pins = s.pins := rfl
@[simp] theorem setEpoch_contents (s : MachineState cfg) (f : FrameId cfg) (e : Epoch) :
    (setEpoch s f e).contents = s.contents := rfl
@[simp] theorem setEpoch_tlb (s : MachineState cfg) (f : FrameId cfg) (e : Epoch) :
    (setEpoch s f e).tlb = s.tlb := rfl
@[simp] theorem setEpoch_pendingFlush (s : MachineState cfg) (f : FrameId cfg) (e : Epoch) :
    (setEpoch s f e).pendingFlush = s.pendingFlush := rfl
@[simp] theorem setEpoch_notifications (s : MachineState cfg) (f : FrameId cfg) (e : Epoch) :
    (setEpoch s f e).notifications = s.notifications := rfl

@[simp] theorem setMapping_status (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (m : Option (Mapping cfg)) : (setMapping s g p m).status = s.status := rfl
@[simp] theorem setMapping_shares (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (m : Option (Mapping cfg)) : (setMapping s g p m).shares = s.shares := rfl
@[simp] theorem setMapping_pins (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (m : Option (Mapping cfg)) : (setMapping s g p m).pins = s.pins := rfl
@[simp] theorem setMapping_epoch (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (m : Option (Mapping cfg)) : (setMapping s g p m).epoch = s.epoch := rfl
@[simp] theorem setMapping_contents (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (m : Option (Mapping cfg)) : (setMapping s g p m).contents = s.contents := rfl
@[simp] theorem setMapping_tlb (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (m : Option (Mapping cfg)) : (setMapping s g p m).tlb = s.tlb := rfl
@[simp] theorem setMapping_pendingFlush (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (m : Option (Mapping cfg)) : (setMapping s g p m).pendingFlush = s.pendingFlush := rfl
@[simp] theorem setMapping_notifications (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (m : Option (Mapping cfg)) : (setMapping s g p m).notifications = s.notifications := rfl

@[simp] theorem setTlb_status (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (e : Option (TlbEntry cfg)) : (setTlb s g p e).status = s.status := rfl
@[simp] theorem setTlb_mappings (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (e : Option (TlbEntry cfg)) : (setTlb s g p e).mappings = s.mappings := rfl
@[simp] theorem setTlb_shares (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (e : Option (TlbEntry cfg)) : (setTlb s g p e).shares = s.shares := rfl
@[simp] theorem setTlb_pins (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (e : Option (TlbEntry cfg)) : (setTlb s g p e).pins = s.pins := rfl
@[simp] theorem setTlb_epoch (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (e : Option (TlbEntry cfg)) : (setTlb s g p e).epoch = s.epoch := rfl
@[simp] theorem setTlb_contents (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (e : Option (TlbEntry cfg)) : (setTlb s g p e).contents = s.contents := rfl
@[simp] theorem setTlb_pendingFlush (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (e : Option (TlbEntry cfg)) : (setTlb s g p e).pendingFlush = s.pendingFlush := rfl
@[simp] theorem setTlb_notifications (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (e : Option (TlbEntry cfg)) : (setTlb s g p e).notifications = s.notifications := rfl

@[simp] theorem setPendingFlush_status (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (l : List (FrameId cfg)) : (setPendingFlush s g p l).status = s.status := rfl
@[simp] theorem setPendingFlush_mappings (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (l : List (FrameId cfg)) : (setPendingFlush s g p l).mappings = s.mappings := rfl
@[simp] theorem setPendingFlush_shares (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (l : List (FrameId cfg)) : (setPendingFlush s g p l).shares = s.shares := rfl
@[simp] theorem setPendingFlush_pins (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (l : List (FrameId cfg)) : (setPendingFlush s g p l).pins = s.pins := rfl
@[simp] theorem setPendingFlush_epoch (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (l : List (FrameId cfg)) : (setPendingFlush s g p l).epoch = s.epoch := rfl
@[simp] theorem setPendingFlush_contents (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (l : List (FrameId cfg)) : (setPendingFlush s g p l).contents = s.contents := rfl
@[simp] theorem setPendingFlush_tlb (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg)
    (l : List (FrameId cfg)) : (setPendingFlush s g p l).tlb = s.tlb := rfl
@[simp] theorem setPendingFlush_notifications (s : MachineState cfg) (g : GuestId cfg)
    (p : GuestPage cfg) (l : List (FrameId cfg)) :
    (setPendingFlush s g p l).notifications = s.notifications := rfl

@[simp] theorem setShare_status (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : Option (ShareCapability cfg)) : (setShare s c cap).status = s.status := rfl
@[simp] theorem setShare_mappings (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : Option (ShareCapability cfg)) : (setShare s c cap).mappings = s.mappings := rfl
@[simp] theorem setShare_pins (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : Option (ShareCapability cfg)) : (setShare s c cap).pins = s.pins := rfl
@[simp] theorem setShare_epoch (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : Option (ShareCapability cfg)) : (setShare s c cap).epoch = s.epoch := rfl
@[simp] theorem setShare_contents (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : Option (ShareCapability cfg)) : (setShare s c cap).contents = s.contents := rfl
@[simp] theorem setShare_tlb (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : Option (ShareCapability cfg)) : (setShare s c cap).tlb = s.tlb := rfl
@[simp] theorem setShare_pendingFlush (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : Option (ShareCapability cfg)) : (setShare s c cap).pendingFlush = s.pendingFlush := rfl
@[simp] theorem setShare_notifications (s : MachineState cfg) (c : CapabilityId cfg)
    (cap : Option (ShareCapability cfg)) : (setShare s c cap).notifications = s.notifications := rfl

@[simp] theorem dropSharedMappingsFor_status (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (dropSharedMappingsFor s holder frame).status = s.status := rfl
@[simp] theorem dropSharedMappingsFor_shares (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (dropSharedMappingsFor s holder frame).shares = s.shares := rfl
@[simp] theorem dropSharedMappingsFor_pins (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (dropSharedMappingsFor s holder frame).pins = s.pins := rfl
@[simp] theorem dropSharedMappingsFor_epoch (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (dropSharedMappingsFor s holder frame).epoch = s.epoch := rfl
@[simp] theorem dropSharedMappingsFor_contents (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (dropSharedMappingsFor s holder frame).contents = s.contents := rfl
@[simp] theorem dropSharedMappingsFor_tlb (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (dropSharedMappingsFor s holder frame).tlb = s.tlb := rfl
@[simp] theorem dropSharedMappingsFor_pendingFlush (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (dropSharedMappingsFor s holder frame).pendingFlush = s.pendingFlush := rfl
@[simp] theorem dropSharedMappingsFor_notifications (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (dropSharedMappingsFor s holder frame).notifications = s.notifications := rfl

@[simp] theorem recordRevokedFlush_status (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (recordRevokedFlush s holder frame).status = s.status := rfl
@[simp] theorem recordRevokedFlush_mappings (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (recordRevokedFlush s holder frame).mappings = s.mappings := rfl
@[simp] theorem recordRevokedFlush_shares (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (recordRevokedFlush s holder frame).shares = s.shares := rfl
@[simp] theorem recordRevokedFlush_pins (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (recordRevokedFlush s holder frame).pins = s.pins := rfl
@[simp] theorem recordRevokedFlush_epoch (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (recordRevokedFlush s holder frame).epoch = s.epoch := rfl
@[simp] theorem recordRevokedFlush_contents (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (recordRevokedFlush s holder frame).contents = s.contents := rfl
@[simp] theorem recordRevokedFlush_tlb (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (recordRevokedFlush s holder frame).tlb = s.tlb := rfl
@[simp] theorem recordRevokedFlush_notifications (s : MachineState cfg) (holder : GuestId cfg)
    (frame : FrameId cfg) : (recordRevokedFlush s holder frame).notifications = s.notifications := rfl

end Romulus
