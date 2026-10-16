 

import romulus.Proofs.Isolation

namespace Romulus
namespace Examples

abbrev C : Config := referenceConfig

def run? {cfg : Config} : MachineState cfg → List (Hypercall cfg) → Option (MachineState cfg)
  | s, [] => some s
  | s, h :: t => (step s h).toOption.bind (fun s' => run? s' t)

theorem allocate_changes_ownership :
    ∃ s : MachineState C, step (emptyState C) (.allocate (0 : GuestId C) (0 : FrameId C)) = .ok s ∧
      s.status (0 : FrameId C) = .owned 0 :=
  ⟨_, rfl, rfl⟩

theorem map_installs_translation :
    ∃ s : MachineState C, step (emptyState C) (.allocate (0 : GuestId C) (0 : FrameId C)) = .ok s ∧
      ∃ s', step s (.map (0 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite) = .ok s' ∧
        s'.mappings (0 : GuestId C) (0 : GuestPage C) = some ⟨0, Permission.readWrite, .ownership⟩ ∧
        s'.tlb (0 : GuestId C) (0 : GuestPage C) = some ⟨0, Permission.readWrite⟩ := by
  refine ⟨_, rfl, _, rfl, rfl, rfl⟩

theorem share_grants_capability :
    ∃ s : MachineState C, step (emptyState C) (.allocate (0 : GuestId C) (0 : FrameId C)) = .ok s ∧
      ∃ s', step s (.share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly) = .ok s' ∧
        s'.shares (0 : CapabilityId C) = some ⟨0, 1, Permission.readOnly, 0⟩ := by
  refine ⟨_, rfl, _, rfl, rfl⟩

theorem transfer_moves_ownership :
    ∃ s : MachineState C, step (emptyState C) (.allocate (0 : GuestId C) (0 : FrameId C)) = .ok s ∧
      ∃ s', step s (.transfer (0 : FrameId C) 0 1) = .ok s' ∧
        s'.status (0 : FrameId C) = .owned 1 := by
  refine ⟨_, rfl, _, rfl, rfl⟩

theorem reclaim_succeeds :
    ∃ s : MachineState C, step (emptyState C) (.allocate (0 : GuestId C) (0 : FrameId C)) = .ok s ∧
      ∃ s', step s (.beginReclaim (0 : GuestId C) (0 : FrameId C)) = .ok s' ∧
        ∃ s'', step s' (.reclaim (0 : FrameId C)) = .ok s'' ∧
          s''.status (0 : FrameId C) = .free ∧ s''.contents (0 : FrameId C) = zeroContents ∧
          s''.epoch (0 : FrameId C) = 1 := by
  refine ⟨_, rfl, _, rfl, _, rfl, rfl, rfl, rfl⟩

 
example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .map (0 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite]).map
        (fun s => (s.status (0 : FrameId C), s.mappings 0 0)) =
      some (.owned 0, some ⟨0, Permission.readWrite, .ownership⟩) := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
       .map (1 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readOnly]).map
        (fun s => (s.shares (0 : CapabilityId C), s.mappings 1 0)) =
      some (some ⟨0, 1, Permission.readOnly, 0⟩, some ⟨0, Permission.readOnly, .shared⟩) := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
       .map (1 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite]).isNone = true := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .transfer (0 : FrameId C) 0 1]).map (fun s => s.status (0 : FrameId C)) = some (.owned 1) := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
       .map (1 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readOnly,
       .revoke (0 : CapabilityId C)]).map
        (fun s => (s.shares (0 : CapabilityId C), s.mappings 1 0)) = some (none, none) := by decide

example :
    (step { emptyState C with
              status := fun f => if f = (0 : FrameId C) then .owned 0 else .free
              epoch := fun f => if f = (0 : FrameId C) then 5 else 0
              shares := fun c => if c = (0 : CapabilityId C) then
                  some ⟨0, 1, Permission.readOnly, 3⟩ else none }
            (.map (1 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readOnly)).toOption.isNone = true := by
  decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .pin (0 : GuestId C) (0 : FrameId C),
       .beginReclaim (0 : GuestId C) (0 : FrameId C)]).isNone = true := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .map (0 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite,
       .write (0 : GuestId C) (0 : GuestPage C) 0 42,
       .unmap (0 : GuestId C) (0 : GuestPage C),
       .beginReclaim (0 : GuestId C) (0 : FrameId C),
       .flush (0 : GuestId C) (0 : GuestPage C),
       .reclaim (0 : FrameId C)]).map
        (fun s => (s.status (0 : FrameId C), s.contents (0 : FrameId C) (0 : Fin pageSize), s.epoch (0 : FrameId C))) =
      some (.free, 0, 1) := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .map (0 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite,
       .unmap (0 : GuestId C) (0 : GuestPage C),
       .beginReclaim (0 : GuestId C) (0 : FrameId C),
       .reclaim (0 : FrameId C)]).isNone = true := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .allocate (1 : GuestId C) (1 : FrameId C),
       .map (0 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite,
       .map (1 : GuestId C) (0 : GuestPage C) (1 : FrameId C) Permission.readWrite]).map
        (fun s => (translationOf s 0 0, translationOf s 1 0)) =
      some (some (0, Permission.readWrite), some (1, Permission.readWrite)) := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
       .revoke (0 : CapabilityId C),
       .acknowledge (1 : GuestId C)]).map
        (fun s => s.notifications 1) = some [] := by decide

end Examples
end Romulus
