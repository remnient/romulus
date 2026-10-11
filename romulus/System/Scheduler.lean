import romulus.System.Events

namespace Romulus

variable {cfg : Config}

inductive ExecutesEvents : MachineState cfg → List (Event cfg) → MachineState cfg → Prop where
  | nil (s : MachineState cfg) : ExecutesEvents s [] s
  | cons {s s' s'' : MachineState cfg} {e : Event cfg} {t : List (Event cfg)} :
      EventStep s e s' → ExecutesEvents s' t s'' → ExecutesEvents s (e :: t) s''

inductive UnrelatedExec (g : GuestId cfg) :
    MachineState cfg → List (Event cfg) → MachineState cfg → Prop where
  | nil (s : MachineState cfg) : UnrelatedExec g s [] s
  | cons {s s' s'' : MachineState cfg} {e : Event cfg} {t : List (Event cfg)} :
      ¬ AffectsEvent g e s → EventStep s e s' →
      UnrelatedExec g s' t s'' → UnrelatedExec g s (e :: t) s''

abbrev Schedule (cfg : Config) := List (Event cfg)

theorem executesEvents_preserves {s s' : MachineState cfg} {trace : List (Event cfg)}
    (hwf : WellFormed s) (h : ExecutesEvents s trace s') : WellFormed s' := by
  revert hwf
  induction h with
  | nil => intro hwf; exact hwf
  | cons hstep _ ih =>
      intro hwf
      exact ih (stepEvent_preserves hwf hstep)

theorem unrelated_exec_indistinguishable {g : GuestId cfg} {s s' : MachineState cfg}
    {trace : List (Event cfg)} (hwf : WellFormed s) (h : UnrelatedExec g s trace s') :
    Indistinguishable g s s' := by
  induction h with
  | nil => exact Indistinguishable.refl g _
  | cons hun hstep _ ih =>
      exact (unrelated_event_preserves_view hwf hun hstep).trans
              (ih (stepEvent_preserves hwf hstep))

theorem no_timing_channel {g : GuestId cfg} {s s' s'' : MachineState cfg}
    {trace trace' : List (Event cfg)} (hwf : WellFormed s)
    (h1 : UnrelatedExec g s trace s') (h2 : UnrelatedExec g s trace' s'') :
    Indistinguishable g s' s'' :=
  (unrelated_exec_indistinguishable hwf h1).symm.trans
    (unrelated_exec_indistinguishable hwf h2)

end Romulus
