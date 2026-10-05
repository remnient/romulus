 

import romulus.Proofs.Preservation
import romulus.TLB.Model

namespace Romulus

variable {cfg : Config}

theorem readVia_of_tlb {s : MachineState cfg} {g : GuestId cfg} {p : GuestPage cfg} {e : TlbEntry cfg}
    (he : s.tlb g p = some e) (hr : e.perms.read = true) :
    readVia s g p = some (s.contents e.frame) := by
  simp [readVia, he, hr]

theorem readVia_of_mapping {s : MachineState cfg} {g : GuestId cfg} {p : GuestPage cfg} {m : Mapping cfg}
    (ht : s.tlb g p = none) (hm : s.mappings g p = some m) (hr : m.perms.read = true) :
    readVia s g p = some (s.contents m.frame) := by
  simp [readVia, ht, hm, hr]

theorem readVia_none {s : MachineState cfg} {g : GuestId cfg} {p : GuestPage cfg}
    (ht : s.tlb g p = none) (hm : s.mappings g p = none) : readVia s g p = none := by
  simp [readVia, ht, hm]

 
theorem reclaim_requires_invalidation {s t : MachineState cfg} {f : FrameId cfg}
    (h : step s (.reclaim f) = .ok t) :
    ¬ hasTlbRef s f ∧ ¬ hasPendingFlushFor s f := by
  obtain ⟨-, -, -, -, hTlb, hPf, -⟩ := (step_reclaim_iff s t f).mp h
  exact ⟨hTlb, hPf⟩

theorem reclaimed_frame_unreachable {s t : MachineState cfg} {f : FrameId cfg}
    (h : step s (.reclaim f) = .ok t) :
    (∀ g p m, t.mappings g p = some m → m.frame ≠ f) ∧
    (∀ g p e, t.tlb g p = some e → e.frame ≠ f) ∧
    t.contents f = zeroContents := by
  obtain ⟨-, hMto, -, -, hTlb, -, ht⟩ := (step_reclaim_iff s t f).mp h
  subst ht
  refine ⟨?_, ?_, ?_⟩
  · intro g p m hm
    have hs : s.mappings g p = some m := by simpa using hm
    intro hf
    exact absurd ⟨g, p, m, hs, hf⟩ hMto
  · intro g p e he
    have hs : s.tlb g p = some e := by simpa using he
    intro hf
    exact absurd ⟨g, p, e, hs, hf⟩ hTlb
  · simp

theorem reclaimed_then_allocated_contents {s s₁ s₂ : MachineState cfg} {f : FrameId cfg}
    {actor : GuestId cfg} (_hr : step s (.reclaim f) = .ok s₁)
    (ha : step s₁ (.allocate actor f) = .ok s₂) : s₂.contents f = zeroContents := by
  obtain ⟨-, ht⟩ := (step_allocate_iff s₁ s₂ actor f).mp ha
  subst ht
  simp

theorem reclaim_rejects_pinned {s : MachineState cfg} {f : FrameId cfg} {g : GuestId cfg}
    (_hrec : s.status f = .reclaiming g) (hpin : s.pins f > 0) :
    ∀ t : MachineState cfg, step s (.reclaim f) ≠ .ok t := by
  intro t h
  obtain ⟨-, -, -, hpin0, -, -, -⟩ := (step_reclaim_iff s t f).mp h
  omega

 
theorem revoke_clears_shared_mapping {s s₁ : MachineState cfg} {c : CapabilityId cfg}
    {cap : ShareCapability cfg} (hrev : step s (.revoke c) = .ok s₁)
    (hcap : s.shares c = some cap) {g : GuestId cfg} {p : GuestPage cfg} {m : Mapping cfg}
    (hm : s.mappings g p = some m) (hholder : g = cap.holder)
    (hshared : m.origin = .shared) (hframe : m.frame = cap.frame) :
    s₁.mappings g p = none := by
  obtain ⟨cap', hcap', hs₁⟩ := (step_revoke_iff s s₁ c).mp hrev
  have hcapEq : cap' = cap := by
    rw [hcap] at hcap'
    exact (Option.some.inj hcap').symm
  rw [hcapEq] at hs₁
  rw [hs₁, show (revokeState s c cap).mappings =
      (dropSharedMappingsFor (recordRevokedFlush (setShare s c none) cap.holder cap.frame)
        cap.holder cap.frame).mappings from rfl]
  rw [hholder] at hm ⊢
  rw [dropSharedMappingsFor_mappings_holder]
  rw [show (recordRevokedFlush (setShare s c none) cap.holder cap.frame).mappings cap.holder p = some m by
        simpa using hm]
  simp [hshared, hframe]

theorem revoke_stale_read_before_flush {s s₁ : MachineState cfg} {c : CapabilityId cfg}
    (hrev : step s (.revoke c) = .ok s₁) {g : GuestId cfg} {p : GuestPage cfg} {e : TlbEntry cfg}
    (htlb : s.tlb g p = some e) (hread : e.perms.read = true) :
    readVia s₁ g p = some (s.contents e.frame) := by
  obtain ⟨cap', -, hs₁⟩ := (step_revoke_iff s s₁ c).mp hrev
  rw [hs₁]
  exact readVia_of_tlb (by simpa using htlb) hread

theorem revoke_flush_no_read {s s₁ s₂ : MachineState cfg} {c : CapabilityId cfg}
    {cap : ShareCapability cfg} (hrev : step s (.revoke c) = .ok s₁)
    (hcap : s.shares c = some cap) {g : GuestId cfg} {p : GuestPage cfg} {m : Mapping cfg}
    (hm : s.mappings g p = some m) (hholder : g = cap.holder)
    (hshared : m.origin = .shared) (hframe : m.frame = cap.frame)
    (hflush : step s₁ (.flush g p) = .ok s₂) : readVia s₂ g p = none := by
  have hmap : s₁.mappings g p = none :=
    revoke_clears_shared_mapping hrev hcap hm hholder hshared hframe
  obtain hs₂ := (step_flush_iff s₁ s₂ g p).mp hflush
  subst hs₂
  exact readVia_none (by simp) (by simpa using hmap)

theorem reclaimed_access_not_frame {s s₁ : MachineState cfg} {f : FrameId cfg}
    {g : GuestId cfg} {op : AccessOp} {p : GuestPage cfg} {f' : FrameId cfg}
    (h : step s (.reclaim f) = .ok s₁) (ha : access s₁ g op p = .ok f') : f' ≠ f := by
  obtain ⟨hMap, hTlb, -⟩ := reclaimed_frame_unreachable h
  rcases access_ok_translation ha with ⟨e, he, hef, -⟩ | ⟨m, hm, hmf, -⟩
  · intro hf; exact hTlb g p e he (hef.trans hf)
  · intro hf; exact hMap g p m hm (hmf.trans hf)

end Romulus
