 

import romulus.Semantics.Refinement

namespace Romulus

variable {cfg : Config}

theorem step_share_preserves {s t : MachineState cfg} (hwf : WellFormed s)
    {grantor : GuestId cfg} {c : CapabilityId cfg} {f : FrameId cfg} {holder : GuestId cfg}
    {perms : Permission} (hstep : step s (.share grantor c f holder perms) = .ok t) :
    WellFormed t := by
  obtain ⟨hslot, hown, rfl⟩ := (step_share_iff s t grantor c f holder perms).mp hstep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g' p' m hm
    obtain ⟨mf, mp, mo⟩ := m
    have hs : s.mappings g' p' = some ⟨mf, mp, mo⟩ := by simpa using hm
    have hJ := hwf.mapping_authority g' p' ⟨mf, mp, mo⟩ hs
    unfold MappingJustified at hJ
    cases mo <;> simp at hJ
    · rcases hJ with hJ | hJ
      · left; rwa [setShare_status]
      · right; rwa [setShare_status]
    · obtain ⟨c', hc'⟩ := hJ
      by_cases hcc : c' = c
      · rw [hcc] at hc'
        simp only [capGrants, hslot] at hc'
      · exact ⟨c', (capGrants_congr (by rw [setShare_of_ne _ _ _ hcc]) (by rfl)).mp hc'⟩
  · intro c' cap hc
    by_cases hcc : c' = c
    · rw [hcc] at hc
      have hcap : cap = ⟨f, holder, perms, s.epoch f⟩ := by simpa [eq_comm] using hc
      rw [hcap]
      simp
    · have hc' : s.shares c' = some cap := by rwa [setShare_of_ne _ _ _ hcc] at hc
      simpa [setShare_epoch] using hwf.capability_epoch c' cap hc'
  · intro c' cap hc
    by_cases hcc : c' = c
    · rw [hcc] at hc
      have hcap : cap = ⟨f, holder, perms, s.epoch f⟩ := by simpa [eq_comm] using hc
      rw [hcap]
      exact ⟨grantor, Or.inl (by simpa using hown)⟩
    · have hc' : s.shares c' = some cap := by rwa [setShare_of_ne _ _ _ hcc] at hc
      obtain ⟨g, hg⟩ := hwf.capability_allocated c' cap hc'
      refine ⟨g, ?_⟩
      rwa [setShare_status]
  · intro f' hp; exact hwf.pins_owned f' (by simpa using hp)
  · intro f' g hst; exact hwf.reclaiming_unpinned f' g (by simpa using hst)
  · intro g' p' e he; exact hwf.tlb_allocated g' p' e (by simpa using he)
  · intro f' hv
    have hv' : s.status f' = .free ∨ s.status f' = .reserved := by simpa using hv
    have hnr := hwf.vacant_unreferenced f' hv'
    refine ⟨?_, ?_⟩
    · intro g' p' m hm; exact hnr.1 g' p' m (by simpa using hm)
    · intro c' cap hc
      by_cases hcc : c' = c
      · rw [hcc] at hc
        have hcap : cap = ⟨f, holder, perms, s.epoch f⟩ := by simpa [eq_comm] using hc
        rw [hcap]
        intro hf
        change f = f' at hf
        rw [hf] at hown
        rcases hv' with hv' | hv' <;> rw [hv'] at hown <;>
          exact absurd hown (by intro hc; cases hc)
      · have hc' : s.shares c' = some cap := by rwa [setShare_of_ne _ _ _ hcc] at hc
        exact hnr.2 c' cap hc'

end Romulus
