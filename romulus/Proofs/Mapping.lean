 

import romulus.Semantics.Refinement

namespace Romulus

variable {cfg : Config}

theorem step_map_preserves {s t : MachineState cfg} (hwf : WellFormed s)
    {actor : GuestId cfg} {p : GuestPage cfg} {f : FrameId cfg} {perms : Permission}
    (hstep : step s (.map actor p f perms) = .ok t) : WellFormed t := by
  obtain ⟨hmaps, hcase⟩ := (step_map_iff s t actor p f perms).mp hstep
  rcases hcase with ⟨hown, ht⟩ | ⟨hnown, hauth, ht⟩
  · subst ht
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g' p' m hm
      by_cases hgp : g' = actor ∧ p' = p
      · rcases hgp with ⟨rfl, rfl⟩
        have hm' : (⟨f, perms, .ownership⟩ : Mapping cfg) = m := by simpa using hm
        rw [← hm']
        exact Or.inl (by simpa using hown)
      · rw [installMapping_mappings_of_ne _ _ _ _ _ _ hgp] at hm
        exact (mappingJustified_congr rfl rfl rfl g' m).mp (hwf.mapping_authority g' p' m hm)
    · intro c' cap hc; exact hwf.capability_epoch c' cap (by simpa using hc)
    · intro c' cap hc; exact hwf.capability_allocated c' cap (by simpa using hc)
    · intro f' hp; exact hwf.pins_owned f' (by simpa using hp)
    · intro f' g hst; exact hwf.reclaiming_unpinned f' g (by simpa using hst)
    · intro g' p' e he
      by_cases hgp : g' = actor ∧ p' = p
      · rcases hgp with ⟨rfl, rfl⟩
        have he' : (⟨f, perms⟩ : TlbEntry cfg) = e := by simpa using he
        rw [← he']
        exact ⟨_, Or.inl (by simpa using hown)⟩
      · rw [installMapping_tlb_of_ne _ _ _ _ _ _ hgp] at he
        exact hwf.tlb_allocated g' p' e he
    · intro f' hv
      have hnr := hwf.vacant_unreferenced f' (by simpa using hv)
      refine ⟨?_, ?_⟩
      · intro g' p' m hm
        by_cases hgp : g' = actor ∧ p' = p
        · rcases hgp with ⟨rfl, rfl⟩
          have hm' : (⟨f, perms, .ownership⟩ : Mapping cfg) = m := by simpa using hm
          rw [← hm']
          intro hf
          change f = f' at hf
          have hv' : s.status f' = .free ∨ s.status f' = .reserved := by simpa using hv
          rw [← hf] at hv'
          rw [hown] at hv'
          rcases hv' with hv' | hv' <;> exact absurd hv' (by intro hc; cases hc)
        · rw [installMapping_mappings_of_ne _ _ _ _ _ _ hgp] at hm
          exact hnr.1 g' p' m hm
      · intro c' cap hc; exact hnr.2 c' cap (by simpa using hc)
  · subst ht
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g' p' m hm
      by_cases hgp : g' = actor ∧ p' = p
      · rcases hgp with ⟨rfl, rfl⟩
        have hm' : (⟨f, perms, .shared⟩ : Mapping cfg) = m := by simpa using hm
        rw [← hm']
        obtain ⟨c', hc'⟩ := hauth
        exact ⟨c', (capGrants_congr (by rfl) (by rfl)).mp hc'⟩
      · rw [installMapping_mappings_of_ne _ _ _ _ _ _ hgp] at hm
        exact (mappingJustified_congr rfl rfl rfl g' m).mp (hwf.mapping_authority g' p' m hm)
    · intro c' cap hc; exact hwf.capability_epoch c' cap (by simpa using hc)
    · intro c' cap hc; exact hwf.capability_allocated c' cap (by simpa using hc)
    · intro f' hp; exact hwf.pins_owned f' (by simpa using hp)
    · intro f' g hst; exact hwf.reclaiming_unpinned f' g (by simpa using hst)
    · intro g' p' e he
      by_cases hgp : g' = actor ∧ p' = p
      · rcases hgp with ⟨rfl, rfl⟩
        have he' : (⟨f, perms⟩ : TlbEntry cfg) = e := by simpa using he
        rw [← he']
        obtain ⟨h, hh⟩ := capAuthorizes_allocated hwf hauth
        exact ⟨h, by simpa using hh⟩
      · rw [installMapping_tlb_of_ne _ _ _ _ _ _ hgp] at he
        exact hwf.tlb_allocated g' p' e he
    · intro f' hv
      have hnr := hwf.vacant_unreferenced f' (by simpa using hv)
      refine ⟨?_, ?_⟩
      · intro g' p' m hm
        by_cases hgp : g' = actor ∧ p' = p
        · rcases hgp with ⟨rfl, rfl⟩
          have hm' : (⟨f, perms, .shared⟩ : Mapping cfg) = m := by simpa using hm
          rw [← hm']
          intro hf
          change f = f' at hf
          obtain ⟨h, hh⟩ := capAuthorizes_allocated hwf hauth
          have hv' : s.status f' = .free ∨ s.status f' = .reserved := by simpa using hv
          rw [← hf] at hv'
          rcases hv' with hv' | hv' <;> rw [hv'] at hh <;>
            (rcases hh with hh | hh <;> exact absurd hh (by intro hc; cases hc))
        · rw [installMapping_mappings_of_ne _ _ _ _ _ _ hgp] at hm
          exact hnr.1 g' p' m hm
      · intro c' cap hc; exact hnr.2 c' cap (by simpa using hc)

theorem step_unmap_preserves {s t : MachineState cfg} (hwf : WellFormed s)
    {actor : GuestId cfg} {p : GuestPage cfg} (hstep : step s (.unmap actor p) = .ok t) :
    WellFormed t := by
  obtain ⟨m, hm, rfl⟩ := (step_unmap_iff s t actor p).mp hstep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g' p' m' hm'
    by_cases hgp : g' = actor ∧ p' = p
    · rcases hgp with ⟨rfl, rfl⟩
      simp only [setPendingFlush_mappings, setMapping_self] at hm'
      exact absurd hm' (by simp)
    · simp only [setPendingFlush_mappings] at hm'
      rw [setMapping_mappings_of_ne _ _ _ _ hgp] at hm'
      exact hwf.mapping_authority g' p' m' hm'
  · intro c' cap hc; exact hwf.capability_epoch c' cap (by simpa using hc)
  · intro c' cap hc; exact hwf.capability_allocated c' cap (by simpa using hc)
  · intro f' hp; exact hwf.pins_owned f' (by simpa using hp)
  · intro f' g hst; exact hwf.reclaiming_unpinned f' g (by simpa using hst)
  · intro g' p' e he; exact hwf.tlb_allocated g' p' e (by simpa using he)
  · intro f' hv
    have hnr := hwf.vacant_unreferenced f' (by simpa using hv)
    refine ⟨?_, ?_⟩
    · intro g' p' m' hm'
      by_cases hgp : g' = actor ∧ p' = p
      · rcases hgp with ⟨rfl, rfl⟩
        simp only [setPendingFlush_mappings, setMapping_self] at hm'
        exact absurd hm' (by simp)
      · simp only [setPendingFlush_mappings] at hm'
        rw [setMapping_mappings_of_ne _ _ _ _ hgp] at hm'
        exact hnr.1 g' p' m' hm'
    · intro c' cap hc; exact hnr.2 c' cap (by simpa using hc)

theorem step_write_preserves {s t : MachineState cfg} (hwf : WellFormed s)
    {actor : GuestId cfg} {p : GuestPage cfg} {offset : Fin pageSize} {value : UInt8}
    (hstep : step s (.write actor p offset value) = .ok t) : WellFormed t := by
  obtain ⟨m, hm, hw, rfl⟩ := (step_write_iff s t actor p offset value).mp hstep
  exact hwf.setContents m.frame (setByte (s.contents m.frame) offset value)

end Romulus
