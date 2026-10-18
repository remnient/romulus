import romulus.Proofs.ReclamationProgress
import romulus.Examples.Scenarios

namespace Romulus
namespace Tests

open Examples

private def reclaimSetup : Option (MachineState C) :=
  run? (emptyState C)
    [.allocate 0 0, .map 0 0 0 Permission.readWrite, .write 0 0 0 42,
     .share 0 0 0 1 Permission.readOnly, .share 0 1 0 2 Permission.readWrite,
     .map 1 1 0 Permission.readOnly, .map 2 7 0 Permission.readWrite, .unmap 2 7,
     .allocate 2 1, .map 2 1 1 Permission.readWrite, .write 2 1 0 55,
     .share 2 7 1 1 Permission.readOnly]

example : reclaimSetup.isSome = true := by decide

example : reclaimSetup.bind (fun s =>
    (reclaimFrame s 0 0).toOption.map (fun (_, t) =>
      (t.shares 0, t.shares 1, t.tlb 2 7, t.pendingFlush 2 7))) =
    some (none, none, none, []) := by decide

example : reclaimSetup.bind (fun s =>
    (reclaimFrame s 0 0).toOption.map (fun (_, t) =>
      (t.status 1, t.mappings 2 1, t.shares 7, t.contents 1 0))) =
    some (.owned 2, some ⟨1, Permission.readWrite, .ownership⟩,
      some ⟨1, 1, Permission.readOnly, 0⟩, 55) := by decide

example : reclaimSetup.bind (fun s =>
    (reclaimFrame s 0 0).toOption.bind (fun (trace, _) =>
      (run? s trace).map (fun t => (t.status 0, t.contents 0 0, t.epoch 0)))) =
    some (.free, 0, 1) := by decide

example : reclaimSetup.map (fun s =>
    match reclaimFrame s 1 0 with
    | .error e => some e
    | .ok _ => none) = some (some .frameNotOwned) := by decide

example : reclaimSetup.bind (fun s =>
    (step s (.pin 0 0)).toOption.map (fun t =>
      match reclaimFrame t 0 0 with
      | .error e => some e
      | .ok _ => none)) = some (some .framePinned) := by decide

example : reclaimSetup.bind (fun s =>
    (reclaimFrame s 0 0).toOption.map (fun (trace, _) => trace.length)) = some 29 := by decide

end Tests
end Romulus
