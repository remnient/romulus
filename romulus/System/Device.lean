import romulus.TLB.Safety

namespace Romulus

variable {cfg : Config}

abbrev DeviceId (cfg : Config) := GuestId cfg

def dma (s : MachineState cfg) (d : DeviceId cfg) (op : AccessOp) (p : GuestPage cfg) :
    Except AccessError (FrameId cfg) :=
  access s d op p

theorem dma_authorised {s : MachineState cfg} (hwf : WellFormed s) {d : DeviceId cfg}
    {p : GuestPage cfg} (hc : pageCoherent s d p) {op : AccessOp} {f : FrameId cfg}
    (h : dma s d op p = .ok f) :
    s.status f = .owned d ∨ s.status f = .reclaiming d ∨
      ∃ cap : ShareCapability cfg,
        (∃ c' : CapabilityId cfg, s.shares c' = some cap) ∧
        cap.holder = d ∧ cap.frame = f ∧ permAllows cap.perms op :=
  access_authorised hwf hc h

theorem dma_cannot_reach_unowned {s : MachineState cfg} (hwf : WellFormed s) {d : DeviceId cfg}
    {p : GuestPage cfg} (hc : pageCoherent s d p) {op : AccessOp} {f : FrameId cfg}
    (h : dma s d op p = .ok f)
    (hnotowner : ¬(s.status f = .owned d ∨ s.status f = .reclaiming d)) :
    ∃ cap : ShareCapability cfg,
      (∃ c' : CapabilityId cfg, s.shares c' = some cap) ∧
      cap.holder = d ∧ cap.frame = f ∧ permAllows cap.perms op := by
  rcases dma_authorised hwf hc h with h | h | h
  · exact absurd (Or.inl h) hnotowner
  · exact absurd (Or.inr h) hnotowner
  · exact h

theorem device_assignment_is_share {s : MachineState cfg} {grantor : GuestId cfg}
    {c : CapabilityId cfg} {f : FrameId cfg} {d : DeviceId cfg} {perms : Permission}
    {t : MachineState cfg} (h : step s (.share grantor c f d perms) = .ok t) :
    ∃ cap : ShareCapability cfg, t.shares c = some cap ∧ cap.holder = d ∧ cap.frame = f := by
  obtain ⟨-, -, ht⟩ := (step_share_iff s t grantor c f d perms).mp h
  refine ⟨⟨f, d, perms, s.epoch f⟩, ?_, rfl, rfl⟩
  rw [ht]; simp

end Romulus
