 

import romulus.Semantics.Refinement

namespace Romulus

variable {cfg : Config}

theorem step_allocate_preserves {s t : MachineState cfg} (hwf : WellFormed s)
    {actor : GuestId cfg} {f : FrameId cfg} (hstep : step s (.allocate actor f) = .ok t) :
    WellFormed t := by
  obtain ⟨hfree, rfl⟩ := (step_allocate_iff s t actor f).mp hstep
  refine hwf.updateFrame f (.owned actor) zeroContents 0 (s.epoch f) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro g p m hm hmf
    exact absurd hmf ((hwf.vacant_unreferenced f (Or.inl hfree)).1 g p m hm)
  · intro c' cap hc hcf
    exact absurd hcf ((hwf.vacant_unreferenced f (Or.inl hfree)).2 c' cap hc)
  · intro c' cap hc hcf
    exact absurd hcf ((hwf.vacant_unreferenced f (Or.inl hfree)).2 c' cap hc)
  · intro hpin; exact absurd hpin (by omega)
  · intro hrec; obtain ⟨g, hg⟩ := hrec; cases hg
  · intro g p e he hef
    exact absurd hef (hwf.free_no_tlb hfree he)
  · intro hv; rcases hv with hv | hv <;> cases hv

theorem step_transfer_preserves {s t : MachineState cfg} (hwf : WellFormed s)
    {f : FrameId cfg} {src dst : GuestId cfg} (hstep : step s (.transfer f src dst) = .ok t) :
    WellFormed t := by
  obtain ⟨hne, hown, hmap, hpin, htlb, hcap, rfl⟩ :=
    (step_transfer_iff s t f src dst).mp hstep
  refine hwf.updateFrame f (.owned dst) (s.contents f) (s.pins f) (s.epoch f) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro g p m hm hmf
    obtain ⟨mf, mp, mo⟩ := m
    change mf = f at hmf
    have hJ := hwf.mapping_authority g p ⟨mf, mp, mo⟩ hm
    unfold MappingJustified at hJ
    cases mo <;> simp at hJ
    · rcases hJ with hJ | hJ
      · rw [hmf, hown] at hJ
        injection hJ with hg
        subst hg
        exact absurd ⟨p, ⟨mf, mp, .ownership⟩, hm, by simpa using hmf⟩ hmap
      · rw [hmf, hown] at hJ
        exact absurd hJ (by intro hc; cases hc)
    · obtain ⟨c', hc'⟩ := hJ
      exact ⟨c', (capGrants_congr (g := g) (F := mf) (perms := mp) (c := c')
        (by rfl) (by rw [hmf, updateFrame_epoch_self])).mpr hc'⟩
  · intro c' cap hc hcf
    have hce := hwf.capability_epoch c' cap hc
    rwa [hcf] at hce
  · intro c' cap hc hcf
    exact ⟨dst, Or.inl rfl⟩
  · intro hpin'
    exact absurd hpin' (by omega)
  · intro hrec; obtain ⟨g, hg⟩ := hrec; cases hg
  · intro g p e he hef
    exact ⟨dst, Or.inl rfl⟩
  · intro hv; rcases hv with hv | hv <;> cases hv

theorem step_pin_preserves {s t : MachineState cfg} (hwf : WellFormed s)
    {actor : GuestId cfg} {f : FrameId cfg} (hstep : step s (.pin actor f) = .ok t) :
    WellFormed t := by
  obtain ⟨hown, rfl⟩ := (step_pin_iff s t actor f).mp hstep
  refine hwf.setPins f (s.pins f + 1) ?_ ?_
  · intro _; exact ⟨actor, by rw [hown]⟩
  · intro hrec
    obtain ⟨g, hg⟩ := hrec
    rw [hown] at hg
    exact absurd hg (by intro hc; cases hc)

theorem step_unpin_preserves {s t : MachineState cfg} (hwf : WellFormed s)
    {actor : GuestId cfg} {f : FrameId cfg} (hstep : step s (.unpin actor f) = .ok t) :
    WellFormed t := by
  obtain ⟨hown, hpos, rfl⟩ := (step_unpin_iff s t actor f).mp hstep
  refine hwf.setPins f (s.pins f - 1) ?_ ?_
  · intro _; exact ⟨actor, by rw [hown]⟩
  · intro hrec
    obtain ⟨g, hg⟩ := hrec
    rw [hown] at hg
    exact absurd hg (by intro hc; cases hc)

end Romulus
