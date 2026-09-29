 

import romulus.Core.State

namespace Romulus

variable {cfg : Config}

def MappingJustified (s : MachineState cfg) (g : GuestId cfg) (m : Mapping cfg) : Prop :=
  match m.origin with
  | .ownership =>
      s.status m.frame = .owned g ∨ s.status m.frame = .reclaiming g
  | .shared =>
      ∃ c : CapabilityId cfg, capGrants s g m.frame m.perms c

def NoFrameRefs (s : MachineState cfg) (f : FrameId cfg) : Prop :=
  (∀ g p m, s.mappings g p = some m → m.frame ≠ f) ∧
  (∀ c cap, s.shares c = some cap → cap.frame ≠ f)

structure WellFormed (s : MachineState cfg) : Prop where
  mapping_authority :
    ∀ g p m, s.mappings g p = some m → MappingJustified s g m
  capability_epoch :
    ∀ c cap, s.shares c = some cap → cap.epoch = s.epoch cap.frame
  capability_allocated :
    ∀ c cap, s.shares c = some cap →
      ∃ g : GuestId cfg, s.status cap.frame = .owned g ∨ s.status cap.frame = .reclaiming g
  pins_owned :
    ∀ f, s.pins f > 0 → ∃ g : GuestId cfg, s.status f = .owned g
  reclaiming_unpinned :
    ∀ f g, s.status f = .reclaiming g → s.pins f = 0
  tlb_allocated :
    ∀ g p e, s.tlb g p = some e →
      ∃ h : GuestId cfg, s.status e.frame = .owned h ∨ s.status e.frame = .reclaiming h
  vacant_unreferenced :
    ∀ f, (s.status f = .free ∨ s.status f = .reserved) → NoFrameRefs s f

namespace WellFormed

theorem free_not_owned {s : MachineState cfg} (_h : WellFormed s) {f : FrameId cfg}
    {g : GuestId cfg} (hfree : s.status f = .free) : ¬ (s.status f = .owned g) := by
  rw [hfree]; intro hc; cases hc

theorem reserved_not_owned {s : MachineState cfg} (_h : WellFormed s) {f : FrameId cfg}
    {g : GuestId cfg} (hres : s.status f = .reserved) : ¬ (s.status f = .owned g) := by
  rw [hres]; intro hc; cases hc

theorem free_not_reclaiming {s : MachineState cfg} (_h : WellFormed s) {f : FrameId cfg}
    {g : GuestId cfg} (hfree : s.status f = .free) : ¬ (s.status f = .reclaiming g) := by
  rw [hfree]; intro hc; cases hc

theorem reserved_not_reclaiming {s : MachineState cfg} (_h : WellFormed s) {f : FrameId cfg}
    {g : GuestId cfg} (hres : s.status f = .reserved) : ¬ (s.status f = .reclaiming g) := by
  rw [hres]; intro hc; cases hc

theorem free_no_tlb {s : MachineState cfg} (h : WellFormed s) {f : FrameId cfg}
    (hfree : s.status f = .free) {g : GuestId cfg} {p : GuestPage cfg} {e : TlbEntry cfg}
    (he : s.tlb g p = some e) : e.frame ≠ f := by
  intro hf
  obtain ⟨h', hh'⟩ := h.tlb_allocated g p e he
  rw [hf] at hh'
  rcases hh' with hh' | hh'
  · exact h.free_not_owned hfree hh'
  · exact h.free_not_reclaiming hfree hh'

theorem reserved_no_tlb {s : MachineState cfg} (h : WellFormed s) {f : FrameId cfg}
    (hres : s.status f = .reserved) {g : GuestId cfg} {p : GuestPage cfg} {e : TlbEntry cfg}
    (he : s.tlb g p = some e) : e.frame ≠ f := by
  intro hf
  obtain ⟨h', hh'⟩ := h.tlb_allocated g p e he
  rw [hf] at hh'
  rcases hh' with hh' | hh'
  · exact h.reserved_not_owned hres hh'
  · exact h.reserved_not_reclaiming hres hh'

theorem free_no_cap {s : MachineState cfg} (h : WellFormed s) {f : FrameId cfg}
    (hfree : s.status f = .free) {c : CapabilityId cfg} {cap : ShareCapability cfg}
    (hc : s.shares c = some cap) : cap.frame ≠ f :=
  (h.vacant_unreferenced f (Or.inl hfree)).2 c cap hc

theorem reserved_no_cap {s : MachineState cfg} (h : WellFormed s) {f : FrameId cfg}
    (hres : s.status f = .reserved) {c : CapabilityId cfg} {cap : ShareCapability cfg}
    (hc : s.shares c = some cap) : cap.frame ≠ f :=
  (h.vacant_unreferenced f (Or.inr hres)).2 c cap hc

end WellFormed

theorem capGrants_congr {s t : MachineState cfg} {g : GuestId cfg} {F : FrameId cfg}
    {perms : Permission} {c : CapabilityId cfg}
    (hsh : t.shares c = s.shares c) (hep : t.epoch F = s.epoch F) :
    (capGrants t g F perms c) ↔ (capGrants s g F perms c) := by
  simp only [capGrants, hsh, hep]

theorem mappingJustified_congr {s t : MachineState cfg}
    (hst : t.status = s.status) (hsh : t.shares = s.shares) (hep : t.epoch = s.epoch)
    (g : GuestId cfg) (m : Mapping cfg) :
    (MappingJustified t g m) ↔ (MappingJustified s g m) := by
  cases hmo : m.origin <;> simp [MappingJustified, capGrants, hmo, hst, hsh, hep]

theorem WellFormed.setContents {s : MachineState cfg} (hwf : WellFormed s)
    (f : FrameId cfg) (c : PageContents) : WellFormed (setContents s f c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g p m hm; exact hwf.mapping_authority g p m (by simpa using hm)
  · intro c' cap hc; exact hwf.capability_epoch c' cap (by simpa using hc)
  · intro c' cap hc; exact hwf.capability_allocated c' cap (by simpa using hc)
  · intro f' hp; exact hwf.pins_owned f' (by simpa using hp)
  · intro f' g hst; exact hwf.reclaiming_unpinned f' g (by simpa using hst)
  · intro g p e he; exact hwf.tlb_allocated g p e (by simpa using he)
  · intro f' hv; exact hwf.vacant_unreferenced f' (by simpa using hv)

theorem wellFormed_emptyState (cfg : Config) : WellFormed (emptyState cfg) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g p m hm; simp [emptyState] at hm
  · intro c cap hc; simp [emptyState] at hc
  · intro c cap hc; simp [emptyState] at hc
  · intro f hp; simp [emptyState] at hp
  · intro f g hst; simp [emptyState] at hst
  · intro g p e he; simp [emptyState] at he
  · intro f hv
    refine ⟨?_, ?_⟩
    · intro g p m hm; simp [emptyState] at hm
    · intro c cap hc; simp [emptyState] at hc

theorem WellFormed.updateFrame {s : MachineState cfg} (hwf : WellFormed s)
    (f : FrameId cfg) (st : FrameStatus cfg) (c : PageContents) (pin : Nat) (ep : Epoch)
    (hMap : ∀ g p m, s.mappings g p = some m → m.frame = f →
              MappingJustified (updateFrame s f st c pin ep) g m)
    (hCapEpoch : ∀ c' cap, s.shares c' = some cap → cap.frame = f → cap.epoch = ep)
    (hCapAlloc : ∀ c' cap, s.shares c' = some cap → cap.frame = f →
              ∃ g : GuestId cfg, st = .owned g ∨ st = .reclaiming g)
    (hPin : pin > 0 → ∃ g : GuestId cfg, st = .owned g)
    (hRecl : (∃ g : GuestId cfg, st = .reclaiming g) → pin = 0)
    (hTlb : ∀ g p e, s.tlb g p = some e → e.frame = f →
              ∃ h : GuestId cfg, st = .owned h ∨ st = .reclaiming h)
    (hVacant : (st = .free ∨ st = .reserved) → NoFrameRefs s f) :
    WellFormed (updateFrame s f st c pin ep) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g p m hm
    have hs : s.mappings g p = some m := by simpa using hm
    obtain ⟨mf, mp, mo⟩ := m
    by_cases hmf : mf = f
    · exact hMap g p ⟨mf, mp, mo⟩ hs hmf
    · have hJ := hwf.mapping_authority g p ⟨mf, mp, mo⟩ hs
      unfold MappingJustified at hJ
      cases mo <;> simp at hJ
      · rcases hJ with hJ | hJ
        · left; rwa [updateFrame_status_of_ne s f st c pin ep hmf]
        · right; rwa [updateFrame_status_of_ne s f st c pin ep hmf]
      · obtain ⟨c', hc'⟩ := hJ
        exact ⟨c', (capGrants_congr (g := g) (F := mf) (perms := mp) (c := c')
          (by rfl) (updateFrame_epoch_of_ne s f st c pin ep hmf)).mpr hc'⟩
  · intro c' cap hc
    have hs : s.shares c' = some cap := by simpa using hc
    by_cases hcf : cap.frame = f
    · rw [hcf, updateFrame_epoch_self]
      exact hCapEpoch c' cap hs hcf
    · rw [hwf.capability_epoch c' cap hs]
      exact (updateFrame_epoch_of_ne s f st c pin ep hcf).symm
  · intro c' cap hc
    have hs : s.shares c' = some cap := by simpa using hc
    by_cases hcf : cap.frame = f
    · rw [hcf, updateFrame_status_self]
      exact hCapAlloc c' cap hs hcf
    · obtain ⟨g, hg⟩ := hwf.capability_allocated c' cap hs
      refine ⟨g, ?_⟩
      rw [updateFrame_status_of_ne s f st c pin ep hcf]
      exact hg
  · intro f' hp
    by_cases hff : f' = f
    · subst hff
      rw [updateFrame_status_self]
      exact hPin (by simpa using hp)
    · have hp' : s.pins f' > 0 := by
        rwa [updateFrame_pins_of_ne s f st c pin ep hff] at hp
      obtain ⟨g, hg⟩ := hwf.pins_owned f' hp'
      refine ⟨g, ?_⟩
      rw [updateFrame_status_of_ne s f st c pin ep hff]
      exact hg
  · intro f' g hst
    by_cases hff : f' = f
    · subst hff
      rw [updateFrame_pins_self]
      exact hRecl ⟨g, by simpa using hst⟩
    · have hs : s.status f' = .reclaiming g := by
        rwa [updateFrame_status_of_ne s f st c pin ep hff] at hst
      rw [updateFrame_pins_of_ne s f st c pin ep hff]
      exact hwf.reclaiming_unpinned f' g hs
  · intro g p e he
    have hs : s.tlb g p = some e := by simpa using he
    by_cases hef : e.frame = f
    · rw [hef, updateFrame_status_self]
      exact hTlb g p e hs hef
    · obtain ⟨h, hh⟩ := hwf.tlb_allocated g p e hs
      refine ⟨h, ?_⟩
      rw [updateFrame_status_of_ne s f st c pin ep hef]
      exact hh
  · intro f' hv
    by_cases hff : f' = f
    · subst hff
      exact hVacant (by simpa using hv)
    · have hs : s.status f' = .free ∨ s.status f' = .reserved := by
        rcases hv with hv | hv
        · left; rwa [updateFrame_status_of_ne s f st c pin ep hff] at hv
        · right; rwa [updateFrame_status_of_ne s f st c pin ep hff] at hv
      exact hwf.vacant_unreferenced f' hs

theorem WellFormed.setPins {s : MachineState cfg} (hwf : WellFormed s)
    (f : FrameId cfg) (n : Nat)
    (hPin : n > 0 → ∃ g : GuestId cfg, s.status f = .owned g)
    (hRecl : (∃ g : GuestId cfg, s.status f = .reclaiming g) → n = 0) :
    WellFormed (setPins s f n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g p m hm; exact hwf.mapping_authority g p m (by simpa using hm)
  · intro c cap hc; exact hwf.capability_epoch c cap (by simpa using hc)
  · intro c cap hc; exact hwf.capability_allocated c cap (by simpa using hc)
  · intro f' hp
    by_cases hff : f' = f
    · subst hff; exact hPin (by simpa using hp)
    · have hp' : s.pins f' > 0 := by
        rwa [setPins_of_ne s f n hff] at hp
      exact hwf.pins_owned f' hp'
  · intro f' g hst
    have hs : s.status f' = .reclaiming g := by simpa using hst
    by_cases hff : f' = f
    · subst hff; rw [setPins_self]; exact hRecl ⟨g, hs⟩
    · rw [setPins_of_ne s f n hff]
      exact hwf.reclaiming_unpinned f' g hs
  · intro g p e he; exact hwf.tlb_allocated g p e (by simpa using he)
  · intro f' hv; exact hwf.vacant_unreferenced f' (by simpa using hv)

end Romulus
