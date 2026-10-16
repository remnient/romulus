 

import romulus.Proofs.Preservation
import romulus.Examples.Scenarios

namespace Romulus
namespace Tests

open Examples

example :
    (run? (emptyState C) [.allocate (0 : GuestId C) (2 : FrameId C)]).map
      (fun s => (s.status (2 : FrameId C), s.contents (2 : FrameId C) (0 : Fin pageSize))) =
      some (.owned 0, 0) := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .map (0 : GuestId C) (1 : GuestPage C) (0 : FrameId C) Permission.readWrite]).map
      (fun s => s.mappings 0 1) = some (some ⟨0, Permission.readWrite, .ownership⟩) := by decide

example :
    (run? (emptyState C) [.allocate (0 : GuestId C) (3 : FrameId C)]).map
      (fun s => (s.status (3 : FrameId C), s.mappings 0 0)) = some (.owned 0, none) := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly]).map
      (fun s => (s.status (0 : FrameId C), s.shares (0 : CapabilityId C))) =
      some (.owned 0, some ⟨0, 1, Permission.readOnly, 0⟩) := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .map (0 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite,
       .write (0 : GuestId C) (0 : GuestPage C) 0 7,
       .unmap (0 : GuestId C) (0 : GuestPage C),
       .flush (0 : GuestId C) (0 : GuestPage C),
       .transfer (0 : FrameId C) 0 1]).map
      (fun s => (s.status (0 : FrameId C), s.contents (0 : FrameId C) (0 : Fin pageSize))) =
      some (.owned 1, 7) := by decide

example :
    WellFormed
      (updateFrame (emptyState C) (0 : FrameId C) (.owned (0 : GuestId C)) zeroContents 0
        ((emptyState C).epoch 0)) :=
  execution_preserves_wellFormed (emptyState C) _ [.allocate (0 : GuestId C) (0 : FrameId C)]
    (wellFormed_emptyState C)
    (Executes.cons ((step_allocate_iff (emptyState C) _ 0 0).mpr ⟨rfl, rfl⟩) (Executes.nil _))

end Tests
end Romulus
