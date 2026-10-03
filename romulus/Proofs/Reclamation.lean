 

import romulus.Semantics.Refinement

namespace Romulus

variable {cfg : Config}

theorem step_beginReclaim_preserves {s t : MachineState cfg} (hwf : WellFormed s)
    {actor : GuestId cfg} {f : FrameId cfg} (hstep : step s (.beginReclaim actor f) = .ok t) :
    WellFormed t := by
  obtain ⟨hown, hpin0, rfl⟩ := (step_beginReclaim_iff s t actor f).mp hstep
  refine hwf.updateFrame f (.reclaiming actor) (s.contents f) (s.pins f) (s.epoch f) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro g p m hm hmf
    obtain ⟨mf, mp, mo⟩ := m
    change mf = f at hmf
    have hJ := hwf.mapping_authority g p ⟨mf, mp, mo⟩ hm
    unfold MappingJustified at hJ
    cases mo <;> simp at hJ
    · rcases hJ with hJ | hJ
      · rw [hmf, hown] at hJ
        injection hJ with hg
        rw [hmf, ← hg]
        right
        simp
      · rw [hmf, hown] at hJ
        exact absurd hJ (by intro hc; cases hc)
    · obtain ⟨c', hc'⟩ := hJ
      exact ⟨c', (capGrants_congr (by rfl) (by simp [hmf])).mpr hc'⟩
  · intro c' cap hc hcf
    have hce := hwf.capability_epoch c' cap hc
    rwa [hcf] at hce
  · intro c' cap hc hcf
    exact ⟨_, Or.inr rfl⟩
  · intro hpin; exact absurd hpin (by omega)
  · intro _; exact hpin0
  · intro g p e he hef
    exact ⟨_, Or.inr rfl⟩
  · intro hv; rcases hv with hv | hv <;> cases hv

theorem step_reclaim_preserves {s t : MachineState cfg} (hwf : WellFormed s)
    {f : FrameId cfg} (hstep : step s (.reclaim f) = .ok t) : WellFormed t := by
  obtain ⟨hrec, hMto, hCap, hpin, hTlb, hPf, rfl⟩ := (step_reclaim_iff s t f).mp hstep
  refine hwf.updateFrame f .free zeroContents 0 (s.epoch f + 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro g p m hm hmf
    exact absurd ⟨g, p, m, hm, hmf⟩ hMto
  · intro c' cap hc hcf
    exact absurd ⟨c', cap, hc, hcf⟩ hCap
  · intro c' cap hc hcf
    exact absurd ⟨c', cap, hc, hcf⟩ hCap
  · intro hpin'; exact absurd hpin' (by omega)
  · intro hrec'; obtain ⟨g, hg⟩ := hrec'; cases hg
  · intro g p e he hef
    exact absurd ⟨g, p, e, he, hef⟩ hTlb
  · intro _
    refine ⟨?_, ?_⟩
    · intro g p m hm hmf; exact absurd ⟨g, p, m, hm, hmf⟩ hMto
    · intro c' cap hc hcf; exact absurd ⟨c', cap, hc, hcf⟩ hCap

end Romulus
