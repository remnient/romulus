 

import romulus.Proofs.Isolation
import romulus.Examples.Scenarios

namespace Romulus
namespace Tests

open Examples

def accessOutcome {cfg : Config} (r : Except AccessError (FrameId cfg)) :
    Option (FrameId cfg) × Option AccessError :=
  (r.toOption, match r with | .error e => some e | .ok _ => none)

def sB : MachineState C :=
  updateFrame (emptyState C) (4 : FrameId C) (.owned (1 : GuestId C)) zeroContents 0 ((emptyState C).epoch 4)

theorem wellFormed_sB : WellFormed sB :=
  step_allocate_preserves (wellFormed_emptyState C)
    ((step_allocate_iff (emptyState C) sB 1 4).mpr ⟨rfl, rfl⟩)

theorem indist_empty_sB : Indistinguishable (0 : GuestId C) (emptyState C) sB := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p; simp [translationOf, emptyState, sB, updateFrame]
  · intro p; simp [cachedTranslationOf, emptyState, sB, updateFrame]
  · intro p; simp [readVia, emptyState, sB, updateFrame]
  · intro f
    unfold ownsFrame
    by_cases hf : f = (4 : FrameId C)
    · subst hf; decide
    · simp [emptyState, sB, updateFrame, hf]
  · simp [emptyState, sB, updateFrame]

example (s : MachineState C) :
    Affects (0 : GuestId C) (.share (1 : GuestId C) (0 : CapabilityId C) (4 : FrameId C)
      (2 : GuestId C) Permission.readOnly) s = False := by
  rfl

example :
    Indistinguishable (0 : GuestId C)
      ((step (emptyState C) (.allocate (1 : GuestId C) (5 : FrameId C))).toOption.getD (emptyState C))
      ((step sB (.allocate (1 : GuestId C) (5 : FrameId C))).toOption.getD sB) := by
  refine unrelated_step_preserves_indistinguishability (g := 0) (s₁ := emptyState C) (s₂ := sB)
    (t₁ := (step (emptyState C) (.allocate (1 : GuestId C) (5 : FrameId C))).toOption.getD (emptyState C))
    (t₂ := (step sB (.allocate (1 : GuestId C) (5 : FrameId C))).toOption.getD sB)
    (h := .allocate (1 : GuestId C) (5 : FrameId C)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact wellFormed_emptyState C
  · exact wellFormed_sB
  · exact indist_empty_sB
  · exact (step_allocate_iff (emptyState C) _ 1 5).mpr ⟨rfl, rfl⟩
  · exact (step_allocate_iff sB _ 1 5).mpr ⟨rfl, rfl⟩
  · exact ⟨by decide, by decide⟩

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .map (0 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readWrite]).bind
        (fun s => (accessOutcome (access s 0 AccessOp.read 0),
                   accessOutcome (access s 1 AccessOp.read 0))) =
      (some ((some (0 : FrameId C), (none : Option AccessError)),
             ((none : Option (FrameId C)), some AccessError.noTranslation)) :
        Option ((Option (FrameId C) × Option AccessError) ×
                (Option (FrameId C) × Option AccessError))) := by decide

example :
    (run? (emptyState C)
      [.allocate (0 : GuestId C) (0 : FrameId C),
       .share (0 : GuestId C) (0 : CapabilityId C) (0 : FrameId C) 1 Permission.readOnly,
       .map (1 : GuestId C) (0 : GuestPage C) (0 : FrameId C) Permission.readOnly]).bind
        (fun s => (accessOutcome (access s 1 AccessOp.read 0),
                   accessOutcome (access s 1 AccessOp.write 0))) =
      (some ((some (0 : FrameId C), (none : Option AccessError)),
             ((none : Option (FrameId C)), some AccessError.permissionDenied)) :
        Option ((Option (FrameId C) × Option AccessError) ×
                (Option (FrameId C) × Option AccessError))) := by decide

end Tests
end Romulus
