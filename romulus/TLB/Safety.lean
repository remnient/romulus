 

import romulus.Proofs.Preservation
import romulus.TLB.Model

namespace Romulus

variable {cfg : Config}

theorem accessWithFill_preserves {s t : MachineState cfg} (hwf : WellFormed s)
    {g : GuestId cfg} {p : GuestPage cfg} {op : AccessOp} {f : FrameId cfg}
    (h : accessWithFill s g op p = .ok (f, t)) : WellFormed t := by
  unfold accessWithFill at h
  split at h
  · split at h
    · cases h; exact hwf
    · contradiction
  · split at h
    · rename_i m hm
      split at h
      · cases h
        refine ⟨hwf.mapping_authority, hwf.capability_epoch, hwf.capability_allocated,
          hwf.pins_owned, hwf.reclaiming_unpinned, ?_, hwf.vacant_unreferenced⟩
        intro g' p' e he
        by_cases hslot : g' = g ∧ p' = p
        · obtain ⟨hg, hp⟩ := hslot
          subst g'
          subst p'
          simp only [setTlb_self, Option.some.injEq] at he
          subst e
          have hj := hwf.mapping_authority g p m hm
          cases ho : m.origin with
          | ownership => exact ⟨g, by simpa [MappingJustified, ho] using hj⟩
          | shared =>
              obtain ⟨c, hc⟩ := (show ∃ c, capGrants s g m.frame m.perms c from
                by simpa [MappingJustified, ho] using hj)
              unfold capGrants at hc
              cases hs : s.shares c with
              | none => simp [hs] at hc
              | some cap =>
                  obtain ⟨-, hf, -, -⟩ := (show cap.holder = g ∧ cap.frame = m.frame ∧
                    cap.epoch = s.epoch m.frame ∧ Permission.leq m.perms cap.perms from
                    by simpa [hs] using hc)
                  rw [← hf]
                  exact hwf.capability_allocated c cap hs
        · exact hwf.tlb_allocated g' p' e (by
            rwa [setTlb_tlb_of_ne s g p _ hslot] at he)
      · contradiction
    · contradiction

theorem accessWithFill_authorised {s t : MachineState cfg} (hwf : WellFormed s)
    {g : GuestId cfg} {p : GuestPage cfg} (hc : pageCoherent s g p)
    {op : AccessOp} {f : FrameId cfg} (h : accessWithFill s g op p = .ok (f, t)) :
    s.status f = .owned g ∨ s.status f = .reclaiming g ∨
      ∃ cap : ShareCapability cfg,
        (∃ c : CapabilityId cfg, s.shares c = some cap) ∧
        cap.holder = g ∧ cap.frame = f ∧ permAllows cap.perms op := by
  apply access_authorised hwf hc
  rw [← accessWithFill_result, h]
  rfl

theorem accessWithFill_miss_authorised {s t : MachineState cfg} (hwf : WellFormed s)
    {g : GuestId cfg} {p : GuestPage cfg} (ht : s.tlb g p = none)
    {op : AccessOp} {f : FrameId cfg} (h : accessWithFill s g op p = .ok (f, t)) :
    s.status f = .owned g ∨ s.status f = .reclaiming g ∨
      ∃ cap : ShareCapability cfg,
        (∃ c : CapabilityId cfg, s.shares c = some cap) ∧
        cap.holder = g ∧ cap.frame = f ∧ permAllows cap.perms op := by
  apply accessWithFill_authorised hwf _ h
  intro e he
  rw [ht] at he
  contradiction

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
