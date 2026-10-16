import romulus.System.Device
import romulus.System.Scheduler
import romulus.MMU.PageTable
import romulus.Semantics.Abstract
import romulus.Examples.Scenarios

namespace Romulus
namespace Tests

open Examples

example : WellFormed
    (addNotification (emptyState C) (1 : GuestId C) (.interrupt InterruptKind.timer)) :=
  stepEvent_preserves (wellFormed_emptyState C)
    (rfl : EventStep (emptyState C) (.interrupt (1 : GuestId C) InterruptKind.timer)
      (addNotification (emptyState C) (1 : GuestId C) (.interrupt InterruptKind.timer)))

abbrev s₁ : MachineState C :=
  addNotification (emptyState C) (1 : GuestId C) (.interrupt InterruptKind.ipi)

abbrev s₂ : MachineState C :=
  addNotification s₁ (1 : GuestId C) (.interrupt InterruptKind.timer)

example : Indistinguishable (0 : GuestId C) (emptyState C) s₂ :=
  unrelated_exec_indistinguishable (wellFormed_emptyState C)
    (UnrelatedExec.cons (by decide)
      (rfl : EventStep (emptyState C) (.interrupt (1 : GuestId C) InterruptKind.ipi) s₁)
      (UnrelatedExec.cons (by decide)
        (rfl : EventStep s₁ (.interrupt (1 : GuestId C) InterruptKind.timer) s₂)
        (UnrelatedExec.nil s₂)))

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .map (0 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite]).bind
        (fun s => (dma s 0 AccessOp.read 0).toOption) = some 0 := by decide

example : (walk (ofMappings (emptyState C)) (0 : GuestId C) (0 : GuestPage C)).toOption = none := by
  decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .map (0 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite]).map
        (fun s => (walk (ofMappings s) 0 0).toOption) = some (some (0, Permission.readWrite)) := by
  decide

example : absOf (updateFrame (emptyState C) (0 : FrameId C) (.owned (0 : GuestId C))
      zeroContents 0 0)
    = absOwnerStep (absOf (emptyState C)) (.allocate (0 : GuestId C) (0 : FrameId C)) :=
  absOf_step ((step_allocate_iff (emptyState C) _ 0 0).mpr ⟨rfl, rfl⟩)

end Tests
end Romulus
