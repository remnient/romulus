 

import romulus.TLB.Model
import romulus.TLB.Safety

namespace Romulus

variable {cfg : Config}

abbrev Indistinguishable (g : GuestId cfg) (s₁ s₂ : MachineState cfg) : Prop :=
  (∀ p, translationOf s₁ g p = translationOf s₂ g p) ∧
  (∀ p, cachedTranslationOf s₁ g p = cachedTranslationOf s₂ g p) ∧
  (∀ p, readVia s₁ g p = readVia s₂ g p) ∧
  (∀ f, ownsFrame s₁ g f ↔ ownsFrame s₂ g f) ∧
  s₁.notifications g = s₂.notifications g

theorem Indistinguishable.refl (g : GuestId cfg) (s : MachineState cfg) :
    Indistinguishable g s s :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => Iff.rfl, rfl⟩

theorem Indistinguishable.symm {g : GuestId cfg} {s₁ s₂ : MachineState cfg}
    (h : Indistinguishable g s₁ s₂) : Indistinguishable g s₂ s₁ :=
  ⟨fun p => (h.1 p).symm, fun p => (h.2.1 p).symm, fun p => (h.2.2.1 p).symm,
   fun f => (h.2.2.2.1 f).symm, (h.2.2.2.2).symm⟩

theorem Indistinguishable.trans {g : GuestId cfg} {s₁ s₂ s₃ : MachineState cfg}
    (h₁ : Indistinguishable g s₁ s₂) (h₂ : Indistinguishable g s₂ s₃) :
    Indistinguishable g s₁ s₃ :=
  ⟨fun p => (h₁.1 p).trans (h₂.1 p),
   fun p => (h₁.2.1 p).trans (h₂.2.1 p),
   fun p => (h₁.2.2.1 p).trans (h₂.2.2.1 p),
   fun f => (h₁.2.2.2.1 f).trans (h₂.2.2.2.1 f),
   h₁.2.2.2.2.trans h₂.2.2.2.2⟩

theorem translationOf_congr {s t : MachineState cfg} {g : GuestId cfg} {p : GuestPage cfg}
    (h : t.mappings g p = s.mappings g p) :
    translationOf t g p = translationOf s g p := by
  simp [translationOf, h]

theorem ownsFrame_congr {s t : MachineState cfg} {g : GuestId cfg} (h : t.status = s.status)
    (f : FrameId cfg) : (ownsFrame t g f ↔ ownsFrame s g f) := by
  unfold ownsFrame; rw [h]

theorem readVia_congr_page {a b : MachineState cfg} {g : GuestId cfg} {p : GuestPage cfg}
    (htlb : b.tlb g p = a.tlb g p) (hmap : b.mappings g p = a.mappings g p)
    (hcont : ∀ f, ((∃ e, a.tlb g p = some e ∧ e.frame = f) ∨
                   (∃ m, a.mappings g p = some m ∧ m.frame = f)) →
             b.contents f = a.contents f) :
    readVia b g p = readVia a g p := by
  cases hs : a.tlb g p with
  | some e =>
      have ht' : b.tlb g p = some e := by rw [htlb, hs]
      by_cases hr : e.perms.read = true
      · rw [readVia_of_tlb ht' hr, readVia_of_tlb hs hr]
        exact congrArg some (hcont e.frame (Or.inl ⟨e, hs, rfl⟩))
      · simp [readVia, ht', hs, hr]
  | none =>
      have ht' : b.tlb g p = none := by rw [htlb, hs]
      cases hm : a.mappings g p with
      | none =>
          have hm' : b.mappings g p = none := by rw [hmap, hm]
          rw [readVia_none ht' hm', readVia_none hs hm]
      | some m =>
          have hm' : b.mappings g p = some m := by rw [hmap, hm]
          by_cases hr : m.perms.read = true
          · rw [readVia_of_mapping ht' hm' hr, readVia_of_mapping hs hm hr]
            exact congrArg some (hcont m.frame (Or.inr ⟨m, hm, rfl⟩))
          · simp [readVia, ht', hs, hm', hm, hr]

 
abbrev Affects (g : GuestId cfg) (h : Hypercall cfg) (s : MachineState cfg) : Prop :=
  match h with
  | .allocate actor _ => actor = g
  | .map actor _ _ _ => actor = g
  | .unmap actor _ => actor = g
  | .share _ _ _ _ _ => False
  | .revoke c => ∃ cap, s.shares c = some cap ∧ cap.holder = g
  | .transfer _ src dst => src = g ∨ dst = g
  | .pin _ _ => False
  | .unpin _ _ => False
  | .beginReclaim actor _ => actor = g
  | .reclaim _ => False
  | .flush g' _ => g' = g
  | .write actor p _ _ =>
      actor = g ∨ ∃ m, s.mappings actor p = some m ∧ reachableFrame s g m.frame
  | .acknowledge actor => actor = g

abbrev UnrelatedTo (g : GuestId cfg) (h : Hypercall cfg) (s₁ s₂ : MachineState cfg) : Prop :=
  ¬ Affects g h s₁ ∧ ¬ Affects g h s₂

theorem unrelated_preserves_view {s t : MachineState cfg} {g : GuestId cfg} {h : Hypercall cfg}
    (hwf : WellFormed s) (hun : ¬ Affects g h s) (hstep : Step s h t) :
    Indistinguishable g s t := by
  unfold Step at hstep
  cases h with
  | allocate actor f =>
      obtain ⟨hfree, ht⟩ := (step_allocate_iff s t actor f).mp hstep
      subst ht
      have hne : actor ≠ g := hun
      refine ⟨fun p => translationOf_congr (by simp), fun p => by simp [cachedTranslationOf],
             fun p => ?_, fun f' => ?_, by simp⟩
      · refine readVia_congr_page (by simp) (by simp) ?_
        intro f0 hname
        rcases hname with ⟨e, he, hf0⟩ | ⟨m, hm, hf0⟩
        · have hef : e.frame ≠ f := hwf.free_no_tlb hfree he
          rw [← hf0, updateFrame_contents_of_ne s f _ _ _ _ hef]
        · have hmf : m.frame ≠ f := (hwf.vacant_unreferenced f (Or.inl hfree)).1 g p m hm
          rw [← hf0, updateFrame_contents_of_ne s f _ _ _ _ hmf]
      · by_cases hf0 : f' = f
        · subst hf0
          unfold ownsFrame
          rw [hfree, updateFrame_status_self]
          exact ⟨(fun h => by cases h), (fun h => absurd (FrameStatus.owned.inj h) hne)⟩
        · unfold ownsFrame
          rw [updateFrame_status_of_ne s f _ _ _ _ hf0]
  | map actor p f perms =>
      obtain ⟨hmaps, hcase⟩ := (step_map_iff s t actor p f perms).mp hstep
      have hne : actor ≠ g := hun
      have hne' : g ≠ actor := fun h => hne h.symm
      have hnot : ∀ p' : GuestPage cfg, ¬(g = actor ∧ p' = p) := fun _ h => hne' h.1
      rcases hcase with ⟨-, ht⟩ | ⟨-, -, ht⟩
      · subst ht
        exact ⟨fun p' => by simp only [translationOf, installMapping_mappings_of_ne _ _ _ _ _ _ (hnot p')],
               fun p' => by simp only [cachedTranslationOf, installMapping_tlb_of_ne _ _ _ _ _ _ (hnot p')],
               fun p' => readVia_congr_page (by rw [installMapping_tlb_of_ne _ _ _ _ _ _ (hnot p')])
                                              (by rw [installMapping_mappings_of_ne _ _ _ _ _ _ (hnot p')])
                                              (by intro f0 _; rfl),
               fun f' => ownsFrame_congr (by rfl) f', by simp⟩
      · subst ht
        exact ⟨fun p' => by simp only [translationOf, installMapping_mappings_of_ne _ _ _ _ _ _ (hnot p')],
               fun p' => by simp only [cachedTranslationOf, installMapping_tlb_of_ne _ _ _ _ _ _ (hnot p')],
               fun p' => readVia_congr_page (by rw [installMapping_tlb_of_ne _ _ _ _ _ _ (hnot p')])
                                              (by rw [installMapping_mappings_of_ne _ _ _ _ _ _ (hnot p')])
                                              (by intro f0 _; rfl),
               fun f' => ownsFrame_congr (by rfl) f', by simp⟩
  | unmap actor p =>
      obtain ⟨m, hm, ht⟩ := (step_unmap_iff s t actor p).mp hstep
      subst ht
      have hne : actor ≠ g := hun
      have hne' : g ≠ actor := fun h => hne h.symm
      refine ⟨fun p' => translationOf_congr ?_, fun p' => by simp [cachedTranslationOf],
             fun p' => ?_, fun f' => ownsFrame_congr (by rfl) f', by simp⟩
      · by_cases hgp : g = actor ∧ p' = p
        · exact absurd hgp.1 hne'
        · rw [setPendingFlush_mappings, setMapping_mappings_of_ne _ _ _ _ hgp]
      · refine readVia_congr_page ?_ ?_ (by intro f0 _; rfl)
        · rw [setPendingFlush_tlb, setMapping_tlb]
        · rw [setPendingFlush_mappings]
          by_cases hgp : g = actor ∧ p' = p
          · exact absurd hgp.1 hne'
          · rw [setMapping_mappings_of_ne _ _ _ _ hgp]
  | share grantor c f holder perms =>
      obtain ⟨-, -, ht⟩ := (step_share_iff s t grantor c f holder perms).mp hstep
      subst ht
      exact ⟨fun p => translationOf_congr (by simp), fun p => by simp [cachedTranslationOf],
             fun p => readVia_congr_page (by simp) (by simp) (by intro f0 _; rfl),
             fun f' => ownsFrame_congr (by rfl) f', by simp⟩
  | revoke c =>
      obtain ⟨cap, hcap, ht⟩ := (step_revoke_iff s t c).mp hstep
      subst ht
      have hne : g ≠ cap.holder := fun h => hun ⟨cap, hcap, h.symm⟩
      refine ⟨fun p => translationOf_congr ?_, fun p => by simp [cachedTranslationOf],
             fun p => ?_, fun f' => ownsFrame_congr (by rfl) f', ?_⟩
      · rw [revokeState_mappings, dropSharedMappingsFor_mappings_other _ _ _ hne,
            recordRevokedFlush_mappings, setShare_mappings]
      · refine readVia_congr_page ?_ ?_ (by intro f0 _; rfl)
        · rw [revokeState_tlb]
        · rw [revokeState_mappings, dropSharedMappingsFor_mappings_other _ _ _ hne,
              recordRevokedFlush_mappings, setShare_mappings]
      · simp [revokeState, addNotification, hne]
  | transfer f src dst =>
      obtain ⟨-, hown, -, -, -, -, ht⟩ := (step_transfer_iff s t f src dst).mp hstep
      subst ht
      have hsrc : src ≠ g := fun h => hun (Or.inl h)
      have hdst : dst ≠ g := fun h => hun (Or.inr h)
      refine ⟨fun p => translationOf_congr (by simp), fun p => by simp [cachedTranslationOf],
             fun p => readVia_congr_page (by simp) (by simp)
                        (by intro f0 _; simp only [updateFrame_contents_same]),
             fun f' => ?_, by simp⟩
      by_cases hf0 : f' = f
      · subst hf0
        unfold ownsFrame
        rw [hown, updateFrame_status_self]
        exact ⟨(fun h => absurd (FrameStatus.owned.inj h) hsrc),
               (fun h => absurd (FrameStatus.owned.inj h) hdst)⟩
      · unfold ownsFrame
        rw [updateFrame_status_of_ne s f _ _ _ _ hf0]
  | pin actor f =>
      obtain ⟨-, ht⟩ := (step_pin_iff s t actor f).mp hstep
      subst ht
      exact ⟨fun p => translationOf_congr (by simp), fun p => by simp [cachedTranslationOf],
             fun p => readVia_congr_page (by simp) (by simp) (by intro f0 _; rfl),
             fun f' => ownsFrame_congr (by rfl) f', by simp⟩
  | unpin actor f =>
      obtain ⟨-, -, ht⟩ := (step_unpin_iff s t actor f).mp hstep
      subst ht
      exact ⟨fun p => translationOf_congr (by simp), fun p => by simp [cachedTranslationOf],
             fun p => readVia_congr_page (by simp) (by simp) (by intro f0 _; rfl),
             fun f' => ownsFrame_congr (by rfl) f', by simp⟩
  | beginReclaim actor f =>
      obtain ⟨hown, -, ht⟩ := (step_beginReclaim_iff s t actor f).mp hstep
      subst ht
      have hne : actor ≠ g := hun
      refine ⟨fun p => translationOf_congr (by simp), fun p => by simp [cachedTranslationOf],
             fun p => readVia_congr_page (by simp) (by simp)
                        (by intro f0 _; simp only [updateFrame_contents_same]),
             fun f' => ?_, by simp⟩
      by_cases hf0 : f' = f
      · subst hf0
        unfold ownsFrame
        rw [hown, updateFrame_status_self]
        exact ⟨(fun h => absurd (FrameStatus.owned.inj h) hne), (fun h => by cases h)⟩
      · unfold ownsFrame
        rw [updateFrame_status_of_ne s f _ _ _ _ hf0]
  | reclaim f =>
      obtain ⟨hrec, hMto, -, -, hTlb, -, ht⟩ := (step_reclaim_iff s t f).mp hstep
      subst ht
      refine ⟨fun p => translationOf_congr (by simp), fun p => by simp [cachedTranslationOf],
             fun p => ?_, fun f' => ?_, by simp⟩
      · refine readVia_congr_page (by simp) (by simp) ?_
        intro f0 hname
        have hf0ne : f0 ≠ f := by
          intro hf0
          rcases hname with ⟨e, he, hef⟩ | ⟨m, hm, hmf⟩
          · exact absurd ⟨g, p, e, he, hef.trans hf0⟩ hTlb
          · exact absurd ⟨g, p, m, hm, hmf.trans hf0⟩ hMto
        rw [updateFrame_contents_of_ne s f _ _ _ _ hf0ne]
      · by_cases hf0 : f' = f
        · subst hf0
          obtain ⟨g', hg'⟩ := hrec
          unfold ownsFrame
          rw [hg', updateFrame_status_self]
          exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
        · unfold ownsFrame
          rw [updateFrame_status_of_ne s f _ _ _ _ hf0]
  | flush g' p =>
      obtain ht := (step_flush_iff s t g' p).mp hstep
      subst ht
      have hne : g' ≠ g := hun
      have hne' : g ≠ g' := fun h => hne h.symm
      refine ⟨fun p' => translationOf_congr (by simp), fun p' => ?_, fun p' => ?_,
             fun f' => ownsFrame_congr (by rfl) f', by simp⟩
      · by_cases hgp : g = g' ∧ p' = p
        · exact absurd hgp.1 hne'
        · simp only [cachedTranslationOf, setPendingFlush_tlb, setTlb_tlb_of_ne _ _ _ _ hgp]
      · refine readVia_congr_page ?_ ?_ (by intro f0 _; rfl)
        · rw [setPendingFlush_tlb]
          by_cases hgp : g = g' ∧ p' = p
          · exact absurd hgp.1 hne'
          · rw [setTlb_tlb_of_ne _ _ _ _ hgp]
        · rw [setPendingFlush_mappings, setTlb_mappings]
  | write actor p offset value =>
      obtain ⟨m, hm, hw, ht⟩ := (step_write_iff s t actor p offset value).mp hstep
      subst ht
      have hne : actor ≠ g := fun h => hun (Or.inl h)
      have hun2 : ¬ (∃ m, s.mappings actor p = some m ∧ reachableFrame s g m.frame) :=
        fun h => hun (Or.inr h)
      refine ⟨fun p' => by simp [translationOf], fun p' => by simp [cachedTranslationOf],
             fun p' => ?_, fun f' => ownsFrame_congr (by rfl) f', by simp⟩
      refine readVia_congr_page
        (a := setContents s m.frame (setByte (s.contents m.frame) offset value)) (b := s)
        (by simp) (by simp) ?_
      intro f0 hname
      have hf0ne : f0 ≠ m.frame := by
        intro hf0
        rcases hname with ⟨e, he, hef⟩ | ⟨m', hm', hmf⟩
        · rw [setContents_tlb] at he
          exact absurd ⟨m, hm, Or.inr ⟨p', e, he, hef.trans hf0⟩⟩ hun2
        · rw [setContents_mappings] at hm'
          exact absurd ⟨m, hm, Or.inl ⟨p', m', hm', hmf.trans hf0⟩⟩ hun2
      rw [setContents_of_ne s m.frame (setByte (s.contents m.frame) offset value) hf0ne]
  | acknowledge actor =>
      obtain ht := (step_acknowledge_iff s t actor).mp hstep
      subst ht
      have hne : g ≠ actor := fun h => hun h.symm
      exact ⟨fun p => translationOf_congr (by simp), fun p => by simp [cachedTranslationOf],
             fun p => readVia_congr_page (by simp) (by simp) (by intro f0 _; rfl),
             fun f' => ownsFrame_congr (by rfl) f',
             by simp [clearNotifications, hne]⟩

theorem unrelated_preserves_access {s t : MachineState cfg} {g : GuestId cfg} {h : Hypercall cfg}
    (hwf : WellFormed s) (hun : ¬ Affects g h s) (hstep : Step s h t) :
    ∀ op p, access s g op p = access t g op p := by
  have hview := unrelated_preserves_view hwf hun hstep
  intro op p
  exact (access_congr (fun p => (hview.2.1 p).symm) (fun p => (hview.1 p).symm) op p).symm

theorem observable_change_requires_affects {s t : MachineState cfg} {g : GuestId cfg}
    {h : Hypercall cfg} (hwf : WellFormed s) (hstep : Step s h t) {p : GuestPage cfg}
    (hchange : readVia t g p ≠ readVia s g p) : Affects g h s := by
  by_cases hun : Affects g h s
  · exact hun
  · exact absurd ((unrelated_preserves_view hwf hun hstep).2.2.1 p).symm hchange

theorem unrelated_step_preserves_indistinguishability (g : GuestId cfg)
    (s₁ s₂ t₁ t₂ : MachineState cfg) (h : Hypercall cfg)
    (hW₁ : WellFormed s₁) (hW₂ : WellFormed s₂)
    (heq : Indistinguishable g s₁ s₂)
    (hleft : Step s₁ h t₁) (hright : Step s₂ h t₂)
    (hun : UnrelatedTo g h s₁ s₂) :
    Indistinguishable g t₁ t₂ := by
  have h1 := unrelated_preserves_view hW₁ hun.1 hleft
  have h2 := unrelated_preserves_view hW₂ hun.2 hright
  exact (h1.symm.trans heq).trans h2

end Romulus
