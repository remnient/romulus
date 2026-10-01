 

import romulus.Core.State

namespace Romulus

variable {cfg : Config}

inductive HypervisorError where
  | frameNotFree
  | frameNotOwned
  | framePinned
  | frameNotPinned
  | frameMapped
  | frameShared
  | frameNotReclaiming
  | pageAlreadyMapped
  | pageNotMapped
  | capabilitySlotOccupied
  | capabilityUnknown
  | notAuthorized
  | insufficientPermission
  | invalidTransfer
  | staleTranslation
  | invalidationPending
  deriving DecidableEq, Repr

inductive Hypercall (cfg : Config) where
  | allocate (actor : GuestId cfg) (frame : FrameId cfg)
  | map (actor : GuestId cfg) (page : GuestPage cfg) (frame : FrameId cfg) (perms : Permission)
  | unmap (actor : GuestId cfg) (page : GuestPage cfg)
  | share (grantor : GuestId cfg) (cap : CapabilityId cfg) (frame : FrameId cfg)
      (holder : GuestId cfg) (perms : Permission)
  | revoke (cap : CapabilityId cfg)
  | transfer (frame : FrameId cfg) (src dst : GuestId cfg)
  | pin (actor : GuestId cfg) (frame : FrameId cfg)
  | unpin (actor : GuestId cfg) (frame : FrameId cfg)
  | beginReclaim (actor : GuestId cfg) (frame : FrameId cfg)
  | reclaim (frame : FrameId cfg)
  | flush (guest : GuestId cfg) (page : GuestPage cfg)
  | write (actor : GuestId cfg) (page : GuestPage cfg) (offset : Fin pageSize) (value : UInt8)
  | acknowledge (actor : GuestId cfg)
  deriving DecidableEq, Repr

end Romulus
