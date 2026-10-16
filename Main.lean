 

import romulus.Examples.Scenarios

open Romulus Romulus.Examples

def describeFrame (s : MachineState C) (f : FrameId C) : String :=
  s!"frame {f.val}: status = {repr (s.status f)}, pins = {s.pins f}, epoch = {s.epoch f}"

def main : IO Unit := do
  let trace : List (Hypercall C) :=
    [.allocate (0 : GuestId C) (0 : FrameId C),
     .map (0 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite,
     .write (0 : GuestId C) (0 : GuestPage C) 0 42,
     .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
     .map (1 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readOnly,
     .unmap (0 : GuestId C) (0 : GuestPage C),
     .revoke (0 : CapabilityId C),
     .beginReclaim (0 : GuestId C) (0 : FrameId C),
     .flush (0 : GuestId C) (0 : GuestPage C),
     .flush (1 : GuestId C) (0 : GuestPage C),
     .reclaim (0 : FrameId C)]
  match run? (emptyState C) trace with
  | none => IO.println "trace failed"
  | some s =>
      IO.println "private allocate, map, write, share read-only, cross-guest map, revoke, reclaim"
      IO.println (describeFrame s 0)
      IO.println s!"contents byte 0 = {contentsAt s ⟨0, 0⟩}"
      IO.println s!"guest 1 translation of page 0 = {repr (translationOf s 1 0)}"
      IO.println s!"guest 1 read of page 0 after reclaim = {repr ((readVia s 1 0).map (fun c => c (0 : Fin pageSize)))}"
      IO.println s!"guest 1 access of page 0 after reclaim = {repr (access s 1 AccessOp.read 0)}"

  let bad : List (Hypercall C) :=
    [.allocate (0 : GuestId C) (0 : FrameId C),
     .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
     .map (1 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite]
  IO.println s!"unauthorised writable map rejected = {((run? (emptyState C) bad).isNone)}"
