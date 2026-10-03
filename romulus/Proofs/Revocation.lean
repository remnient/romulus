 

import romulus.Semantics.Refinement

namespace Romulus

variable {cfg : Config}

theorem step_revoke_preserves {s t : MachineState cfg} (hwf : WellFormed s)
    {c : CapabilityId cfg} (hstep : step s (.revoke c) = .ok t) : WellFormed t := by
  obtain ⟨cap, hcap, ht⟩ := (step_revoke_iff s t c).mp hstep
  subst ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g' p' m hm
    obtain ⟨mf, mp, mo⟩ := m
    obtain ⟨hmS, hkeep⟩ :=
      dropSharedMappingsFor_mappings_some (recordRevokedFlush (setShare s c none) cap.holder cap.frame) cap.holder cap.frame
        (by simpa using hm)
    have hs : s.mappings g' p' = some ⟨mf, mp, mo⟩ := by simpa using hmS
    have hJ := hwf.mapping_authority g' p' ⟨mf, mp, mo⟩ hs
    unfold MappingJustified at hJ
    cases mo <;> simp at hJ
    · rcases hJ with hJ | hJ
      · left; rwa [revokeState_status]
      · right; rwa [revokeState_status]
    · obtain ⟨c', hc'⟩ := hJ
      by_cases hcc : c' = c
      · rw [hcc] at hc'
        simp only [capGrants, hcap] at hc'
        obtain ⟨hh, hf, -, -⟩ := hc'
        exact absurd ⟨rfl, hf.symm⟩ (hkeep hh.symm)
      · exact ⟨c', (capGrants_congr
          (by rw [revokeState_shares, setShare_of_ne _ _ _ hcc]) (by rfl)).mp hc'⟩
  · intro c' cap' hc
    by_cases hcc : c' = c
    · rw [hcc] at hc
      simp only [revokeState_shares, setShare_self] at hc
      exact absurd hc (by simp)
    · have hc' : s.shares c' = some cap' := by
        rw [revokeState_shares, setShare_of_ne _ _ _ hcc] at hc; exact hc
      simpa [revokeState_epoch] using hwf.capability_epoch c' cap' hc'
  · intro c' cap' hc
    by_cases hcc : c' = c
    · rw [hcc] at hc
      simp only [revokeState_shares, setShare_self] at hc
      exact absurd hc (by simp)
    · have hc' : s.shares c' = some cap' := by
        rw [revokeState_shares, setShare_of_ne _ _ _ hcc] at hc; exact hc
      obtain ⟨g, hg⟩ := hwf.capability_allocated c' cap' hc'
      refine ⟨g, ?_⟩
      rwa [revokeState_status]
  · intro f' hp; exact hwf.pins_owned f' (by simpa using hp)
  · intro f' g hst; exact hwf.reclaiming_unpinned f' g (by simpa using hst)
  · intro g' p' e he; exact hwf.tlb_allocated g' p' e (by simpa using he)
  · intro f' hv
    have hv' : s.status f' = .free ∨ s.status f' = .reserved := by simpa using hv
    have hnr := hwf.vacant_unreferenced f' hv'
    refine ⟨?_, ?_⟩
    · intro g' p' m hm
      obtain ⟨hmS, _⟩ :=
        dropSharedMappingsFor_mappings_some (recordRevokedFlush (setShare s c none) cap.holder cap.frame) cap.holder cap.frame
          (by simpa using hm)
      exact hnr.1 g' p' m (by simpa using hmS)
    · intro c' cap' hc
      by_cases hcc : c' = c
      · rw [hcc] at hc
        simp only [revokeState_shares, setShare_self] at hc
        exact absurd hc (by simp)
      · have hc' : s.shares c' = some cap' := by
          rw [revokeState_shares, setShare_of_ne _ _ _ hcc] at hc; exact hc
        exact hnr.2 c' cap' hc'

theorem step_flush_preserves {s t : MachineState cfg} (hwf : WellFormed s)
    {g : GuestId cfg} {p : GuestPage cfg} (hstep : step s (.flush g p) = .ok t) :
    WellFormed t := by
  obtain ht := (step_flush_iff s t g p).mp hstep
  subst ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g' p' m hm
    have hs : s.mappings g' p' = some m := by simpa using hm
    exact (mappingJustified_congr rfl rfl rfl g' m).mp (hwf.mapping_authority g' p' m hs)
  · intro c' cap hc; exact hwf.capability_epoch c' cap (by simpa using hc)
  · intro c' cap hc; exact hwf.capability_allocated c' cap (by simpa using hc)
  · intro f' hp; exact hwf.pins_owned f' (by simpa using hp)
  · intro f' g' hst; exact hwf.reclaiming_unpinned f' g' (by simpa using hst)
  · intro g' p' e he
    by_cases hgp : g' = g ∧ p' = p
    · rcases hgp with ⟨rfl, rfl⟩
      simp only [setPendingFlush_tlb, setTlb_self] at he
      exact absurd he (by simp)
    · rw [setPendingFlush_tlb, setTlb_tlb_of_ne _ _ _ _ hgp] at he
      exact hwf.tlb_allocated g' p' e he
  · intro f' hv
    have hv' : s.status f' = .free ∨ s.status f' = .reserved := by simpa using hv
    have hnr := hwf.vacant_unreferenced f' hv'
    exact ⟨fun g' p' m hm => hnr.1 g' p' m (by simpa using hm),
           fun c' cap hc => hnr.2 c' cap (by simpa using hc)⟩

end Romulus
