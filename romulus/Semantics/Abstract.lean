import romulus.Semantics.Refinement
import romulus.Semantics.Execution

namespace Romulus

variable {cfg : Config}

abbrev AbsState (cfg : Config) := FrameId cfg → FrameStatus cfg

inductive AbsOp (cfg : Config) where
  | allocate (g : GuestId cfg) (f : FrameId cfg)
  | transfer (f : FrameId cfg) (dst : GuestId cfg)
  | beginReclaim (g : GuestId cfg) (f : FrameId cfg)
  | reclaim (f : FrameId cfg)
  | other

def absOf (s : MachineState cfg) : AbsState cfg := s.status

def absOpOf {cfg : Config} : Hypercall cfg → AbsOp cfg
  | .allocate g f => .allocate g f
  | .transfer f _ dst => .transfer f dst
  | .beginReclaim g f => .beginReclaim g f
  | .reclaim f => .reclaim f
  | _ => .other

def absOwnerStep (σ : AbsState cfg) : AbsOp cfg → AbsState cfg
  | .allocate g f => fun f' => if f' = f then .owned g else σ f'
  | .transfer f dst => fun f' => if f' = f then .owned dst else σ f'
  | .beginReclaim g f => fun f' => if f' = f then .reclaiming g else σ f'
  | .reclaim f => fun f' => if f' = f then .free else σ f'
  | .other => σ

theorem absOwnerStep_updateFrame (s : MachineState cfg) (f : FrameId cfg) (st : FrameStatus cfg)
    (c : PageContents) (pin : Nat) (ep : Epoch) :
    (updateFrame s f st c pin ep).status
      = (fun f' => if f' = f then st else s.status f') := rfl

theorem absOf_step {s t : MachineState cfg} {h : Hypercall cfg} (hstep : Step s h t) :
    absOf t = absOwnerStep (absOf s) (absOpOf h) := by
  unfold Step at hstep
  unfold absOf
  cases h with
  | allocate actor f =>
      obtain ⟨hfree, ht⟩ := (step_allocate_iff s t actor f).mp hstep
      rw [ht]; rfl
  | map actor p f perms =>
      obtain ⟨hmaps, hcase⟩ := (step_map_iff s t actor p f perms).mp hstep
      rcases hcase with ⟨-, ht⟩ | ⟨-, -, ht⟩ <;> rw [ht] <;> rfl
  | unmap actor p =>
      obtain ⟨m, hm, ht⟩ := (step_unmap_iff s t actor p).mp hstep
      rw [ht]; rfl
  | share grantor c f holder perms =>
      obtain ⟨hslot, hown, ht⟩ := (step_share_iff s t grantor c f holder perms).mp hstep
      rw [ht]; rfl
  | revoke c =>
      obtain ⟨cap, hcap, ht⟩ := (step_revoke_iff s t c).mp hstep
      rw [ht]; rfl
  | transfer f src dst =>
      obtain ⟨hne, hown, hm, hp, ht, hc, ht2⟩ := (step_transfer_iff s t f src dst).mp hstep
      rw [ht2]; rfl
  | pin actor f =>
      obtain ⟨hown, ht⟩ := (step_pin_iff s t actor f).mp hstep
      rw [ht]; rfl
  | unpin actor f =>
      obtain ⟨hown, hp, ht⟩ := (step_unpin_iff s t actor f).mp hstep
      rw [ht]; rfl
  | beginReclaim actor f =>
      obtain ⟨hown, hp, ht⟩ := (step_beginReclaim_iff s t actor f).mp hstep
      rw [ht]; rfl
  | reclaim f =>
      obtain ⟨hrec, hm, hc, hp, ht, hpf, ht2⟩ := (step_reclaim_iff s t f).mp hstep
      rw [ht2]; rfl
  | flush g p =>
      obtain ht := (step_flush_iff s t g p).mp hstep
      rw [ht]; rfl
  | write actor p offset value =>
      obtain ⟨m, hm, hw, ht⟩ := (step_write_iff s t actor p offset value).mp hstep
      rw [ht]; rfl
  | acknowledge actor =>
      obtain ht := (step_acknowledge_iff s t actor).mp hstep
      rw [ht]; rfl

theorem absOf_executes {s s' : MachineState cfg} {trace : List (Hypercall cfg)}
    (h : Executes s trace s') :
    absOf s' = trace.foldl (fun σ h => absOwnerStep σ (absOpOf h)) (absOf s) := by
  induction h with
  | nil => rfl
  | cons hstep _ ih =>
      rw [List.foldl_cons, ← absOf_step hstep]
      exact ih

end Romulus
