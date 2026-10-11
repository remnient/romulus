import romulus.Proofs.Isolation

namespace Romulus

variable {cfg : Config}

inductive Event (cfg : Config) where
  | hypercall (h : Hypercall cfg)
  | interrupt (target : GuestId cfg) (kind : InterruptKind)
  | timer (target : GuestId cfg)
  deriving DecidableEq, Repr

def stepEvent (s : MachineState cfg) : Event cfg → Except HypervisorError (MachineState cfg)
  | .hypercall h => step s h
  | .interrupt target kind => .ok (addNotification s target (.interrupt kind))
  | .timer target => .ok (addNotification s target (.interrupt .timer))

def EventStep (s : MachineState cfg) (e : Event cfg) (t : MachineState cfg) : Prop :=
  stepEvent s e = .ok t

abbrev AffectsEvent (g : GuestId cfg) (e : Event cfg) (s : MachineState cfg) : Prop :=
  match e with
  | .hypercall h => Affects g h s
  | .interrupt target _ => target = g
  | .timer target => target = g

theorem stepEvent_preserves {s t : MachineState cfg} {e : Event cfg}
    (hwf : WellFormed s) (h : EventStep s e t) : WellFormed t := by
  unfold EventStep at h
  cases e with
  | hypercall hc => exact step_preserves_wellFormed _ _ _ hwf h
  | interrupt target kind =>
      simp only [stepEvent] at h
      injection h with ht
      rw [← ht]
      exact hwf.addNotification target _
  | timer target =>
      simp only [stepEvent] at h
      injection h with ht
      rw [← ht]
      exact hwf.addNotification target _

theorem unrelated_event_preserves_view {s t : MachineState cfg} {g : GuestId cfg} {e : Event cfg}
    (hwf : WellFormed s) (hun : ¬ AffectsEvent g e s) (h : EventStep s e t) :
    Indistinguishable g s t := by
  unfold EventStep at h
  cases e with
  | hypercall hc => exact unrelated_preserves_view hwf hun h
  | interrupt target kind =>
      simp only [stepEvent] at h
      have hne : target ≠ g := hun
      have hne' : g ≠ target := fun hh => hne hh.symm
      injection h with ht
      rw [← ht]
      exact ⟨fun p => translationOf_congr (by simp), fun p => by simp [cachedTranslationOf],
             fun p => readVia_congr_page (by simp) (by simp) (by intro f0 _; rfl),
             fun f' => ownsFrame_congr (by rfl) f',
             by simp [addNotification, hne']⟩
  | timer target =>
      simp only [stepEvent] at h
      have hne : target ≠ g := hun
      have hne' : g ≠ target := fun hh => hne hh.symm
      injection h with ht
      rw [← ht]
      exact ⟨fun p => translationOf_congr (by simp), fun p => by simp [cachedTranslationOf],
             fun p => readVia_congr_page (by simp) (by simp) (by intro f0 _; rfl),
             fun f' => ownsFrame_congr (by rfl) f',
             by simp [addNotification, hne']⟩

theorem unrelated_event_step_preserves_indistinguishability (g : GuestId cfg)
    (s₁ s₂ t₁ t₂ : MachineState cfg) (e : Event cfg)
    (hW₁ : WellFormed s₁) (hW₂ : WellFormed s₂)
    (heq : Indistinguishable g s₁ s₂)
    (hleft : EventStep s₁ e t₁) (hright : EventStep s₂ e t₂)
    (hun : ¬ AffectsEvent g e s₁ ∧ ¬ AffectsEvent g e s₂) :
    Indistinguishable g t₁ t₂ := by
  have h1 := unrelated_event_preserves_view hW₁ hun.1 hleft
  have h2 := unrelated_event_preserves_view hW₂ hun.2 hright
  exact (h1.symm.trans heq).trans h2

end Romulus
