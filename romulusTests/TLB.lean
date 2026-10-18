import romulus.TLB.Safety
import romulus.Examples.Scenarios

namespace Romulus
namespace Tests

open Examples

private def cacheFillSetup : List (Hypercall C) :=
  [.allocate 0 0, .share 0 0 0 1 Permission.readOnly,
   .map 1 2 0 Permission.readOnly, .flush 1 2]

example :
    (run? (emptyState C) cacheFillSetup).bind (fun s =>
      (accessWithFill s 1 .read 2).toOption.map (fun (f, t) =>
        (f, t.tlb 1 2, t.tlb 0 2, t.mappings 1 2))) =
      some (0, some ⟨0, Permission.readOnly⟩, none,
        some ⟨0, Permission.readOnly, .shared⟩) := by decide

example :
    (run? (emptyState C) cacheFillSetup).map (fun s =>
      (accessWithFill s 1 .write 2).toOption.isNone) = some true := by decide

example :
    (run? (emptyState C) cacheFillSetup).map (fun s =>
      (accessWithFill s 1 .execute 2).toOption.isNone) = some true := by decide

example : accessWithFill (emptyState C) 0 .read 0 = .error .noTranslation := rfl

example :
    (run? (emptyState C) cacheFillSetup).bind (fun s =>
      (accessWithFill s 1 .read 2).toOption.bind (fun (_, t) =>
        (accessWithFill t 1 .read 2).toOption.map (fun (f, u) => (f, u.tlb 1 2)))) =
      some (0, some ⟨0, Permission.readOnly⟩) := by decide

example :
    (run? (emptyState C) (cacheFillSetup ++ [.revoke 0])).map (fun s =>
      (accessWithFill s 1 .read 2).toOption.isNone) = some true := by decide

example :
    (run? (emptyState C) cacheFillSetup).bind (fun s =>
      (accessWithFill s 1 .read 2).toOption.bind (fun (_, t) =>
        (run? t [.revoke 0]).map (fun u =>
          ((accessWithFill u 1 .read 2).toOption.map Prod.fst,
           (run? u [.flush 1 2]).bind (fun v =>
             (accessWithFill v 1 .read 2).toOption.map Prod.fst))))) =
      some (some 0, none) := by decide

example {s : MachineState C} {g : GuestId C} {p : GuestPage C} {m : Mapping C}
    (ht : s.tlb g p = none) (hm : s.mappings g p = some m)
    (hp : permAllows m.perms .read) {g' : GuestId C} {p' : GuestPage C}
    (hne : ¬ (g' = g ∧ p' = p)) :
    (accessWithFill s g .read p).toOption.map (fun (_, t) => t.tlb g' p') =
      some (s.tlb g' p') := by
  rw [accessWithFill_miss ht hm hp]
  change some ((setTlb s g p (some ⟨m.frame, m.perms⟩)).tlb g' p') = _
  rw [setTlb_tlb_of_ne s g p _ hne]

end Tests
end Romulus
