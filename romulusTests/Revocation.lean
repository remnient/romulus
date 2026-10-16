 

import romulus.Examples.Counterexamples

namespace Romulus
namespace Tests

open Examples

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
       .revoke (0 : CapabilityId C)]).map (fun s => s.shares (0 : CapabilityId C)) = some none := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
       .map (1 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readOnly,
       .revoke (0 : CapabilityId C)]).map
      (fun s => s.pendingFlush 1 0) = some [0] := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
       .map (1 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readOnly,
       .revoke (0 : CapabilityId C),
       .flush (1 : GuestId C) (0 : GuestPage C)]).map
      (fun s => (s.pendingFlush 1 0, s.tlb 1 0)) = some ([], none) := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
       .map (1 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readOnly,
       .revoke (0 : CapabilityId C),
       .beginReclaim (0 : GuestId C) (0 : FrameId C),
       .reclaim (0 : FrameId C)]).isNone = true := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
       .map (1 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readOnly,
       .revoke (0 : CapabilityId C),
       .flush (1 : GuestId C) (0 : GuestPage C),
       .beginReclaim (0 : GuestId C) (0 : FrameId C),
       .reclaim (0 : FrameId C)]).map
      (fun s => (s.status (0 : FrameId C), s.epoch (0 : FrameId C))) = some (.free, 1) := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
       .revoke (0 : CapabilityId C)]).map
      (fun s => s.notifications 1) = some [Notice.revocation 0 0 0] := by decide

end Tests
end Romulus
