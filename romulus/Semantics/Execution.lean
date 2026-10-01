 

import romulus.Semantics.Refinement

namespace Romulus

variable {cfg : Config}

inductive Executes : MachineState cfg → List (Hypercall cfg) → MachineState cfg → Prop where
  | nil (s : MachineState cfg) : Executes s [] s
  | cons {s s' s'' : MachineState cfg} {h : Hypercall cfg} {t : List (Hypercall cfg)} :
      Step s h s' → Executes s' t s'' → Executes s (h :: t) s''

theorem step_deterministic {s : MachineState cfg} {h : Hypercall cfg} {t₁ t₂ : MachineState cfg}
    (h₁ : Step s h t₁) (h₂ : Step s h t₂) : t₁ = t₂ := by
  unfold Step at h₁ h₂
  rw [h₁] at h₂
  exact Except.ok.inj h₂

end Romulus
