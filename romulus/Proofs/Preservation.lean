 

import romulus.Semantics.Execution
import romulus.Proofs.Ownership
import romulus.Proofs.Mapping
import romulus.Proofs.Sharing
import romulus.Proofs.Revocation
import romulus.Proofs.Reclamation

namespace Romulus

variable {cfg : Config}

theorem step_preserves_wellFormed (s s' : MachineState cfg) (h : Hypercall cfg)
    (hwf : WellFormed s) (hstep : Step s h s') : WellFormed s' := by
  unfold Step at hstep
  cases h with
  | allocate actor f => exact step_allocate_preserves hwf hstep
  | map actor p f perms => exact step_map_preserves hwf hstep
  | unmap actor p => exact step_unmap_preserves hwf hstep
  | share grantor c f holder perms => exact step_share_preserves hwf hstep
  | revoke c => exact step_revoke_preserves hwf hstep
  | transfer f src dst => exact step_transfer_preserves hwf hstep
  | pin actor f => exact step_pin_preserves hwf hstep
  | unpin actor f => exact step_unpin_preserves hwf hstep
  | beginReclaim actor f => exact step_beginReclaim_preserves hwf hstep
  | reclaim f => exact step_reclaim_preserves hwf hstep
  | flush g p => exact step_flush_preserves hwf hstep
  | write actor p offset value => exact step_write_preserves hwf hstep
  | acknowledge actor =>
      obtain ht := (step_acknowledge_iff s s' actor).mp hstep
      subst ht
      exact hwf.clearNotifications actor

theorem execution_preserves_wellFormed (s s' : MachineState cfg) (trace : List (Hypercall cfg))
    (hwf : WellFormed s) (hexec : Executes s trace s') : WellFormed s' := by
  revert hwf
  induction hexec with
  | nil => intro hwf; exact hwf
  | cons hstep _ ih =>
      intro hwf
      exact ih (step_preserves_wellFormed _ _ _ hwf hstep)

end Romulus
