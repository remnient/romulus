 

import romulus.Examples.Scenarios

namespace Romulus
namespace Examples

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .map (1 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite]).isNone = true := by
  decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .map (0 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite,
       .transfer (0 : FrameId C) 0 1]).isNone = true := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
       .beginReclaim (0 : GuestId C) (0 : FrameId C),
       .reclaim (0 : FrameId C)]).isNone = true := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .allocate (1 : GuestId C) (0 : FrameId C)]).isNone = true := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .pin (1 : GuestId C) (0 : FrameId C)]).isNone = true := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .unpin (0 : GuestId C) (0 : FrameId C)]).isNone = true := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .map (0 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite,
       .write (0 : GuestId C) (0 : GuestPage C) 0 42,
       .unmap (0 : GuestId C) (0 : GuestPage C)]).bind
        (fun s => (readVia s 0 0).map (fun c => c (0 : Fin pageSize))) = some 42 := by decide

example :
    ((run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .map (0 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite,
       .write (0 : GuestId C) (0 : GuestPage C) 0 42,
       .unmap (0 : GuestId C) (0 : GuestPage C),
       .flush (0 : GuestId C) (0 : GuestPage C)]).bind
        (fun s => readVia s 0 0)).isNone = true := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
       .map (1 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readOnly,
       .revoke (0 : CapabilityId C)]).bind
        (fun s => s.tlb 1 0) = some ⟨0, Permission.readOnly⟩ := by decide

end Examples
end Romulus
