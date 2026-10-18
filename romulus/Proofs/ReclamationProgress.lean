import romulus.Proofs.Preservation

namespace Romulus

variable {cfg : Config}

def revokeFrameCaps (s : MachineState cfg) (f : FrameId cfg) :
    List (CapabilityId cfg) → List (Hypercall cfg) × MachineState cfg
  | [] => ([], s)
  | c :: cs =>
      match s.shares c with
      | some cap =>
          if cap.frame = f then
            let (trace, t) := revokeFrameCaps (revokeState s c cap) f cs
            (.revoke c :: trace, t)
          else revokeFrameCaps s f cs
      | none => revokeFrameCaps s f cs

def unmapFramePages (s : MachineState cfg) (f : FrameId cfg) :
    List (GuestId cfg × GuestPage cfg) → List (Hypercall cfg) × MachineState cfg
  | [] => ([], s)
  | (g, p) :: pages =>
      match s.mappings g p with
      | some m =>
          if m.frame = f then
            let t := setPendingFlush (setMapping s g p none) g p (f :: s.pendingFlush g p)
            let (trace, u) := unmapFramePages t f pages
            (.unmap g p :: trace, u)
          else unmapFramePages s f pages
      | none => unmapFramePages s f pages

def flushPages (s : MachineState cfg) :
    List (GuestId cfg × GuestPage cfg) → List (Hypercall cfg) × MachineState cfg
  | [] => ([], s)
  | (g, p) :: pages =>
      let (trace, t) := flushPages (setPendingFlush (setTlb s g p none) g p []) pages
      (.flush g p :: trace, t)

def allGuestPages (cfg : Config) : List (GuestId cfg × GuestPage cfg) :=
  (List.finRange cfg.numGuests).flatMap (fun g =>
    (List.finRange cfg.numPages).map (fun p => (g, p)))

def reclaimFrame (s : MachineState cfg) (g : GuestId cfg) (f : FrameId cfg) :
    Except HypervisorError (List (Hypercall cfg) × MachineState cfg) := do
  let started ← step s (.beginReclaim g f)
  let (revokes, revoked) := revokeFrameCaps started f (List.finRange cfg.numCaps)
  let (unmaps, unmapped) := unmapFramePages revoked f (allGuestPages cfg)
  let (flushes, flushed) := flushPages unmapped (allGuestPages cfg)
  let reclaimed ← step flushed (.reclaim f)
  return (.beginReclaim g f :: revokes ++ unmaps ++ flushes ++ [.reclaim f], reclaimed)

private def SameFrameData (s t : MachineState cfg) : Prop :=
  t.status = s.status ∧ t.pins = s.pins ∧ t.epoch = s.epoch ∧ t.contents = s.contents

private theorem SameFrameData.trans {s t u : MachineState cfg}
    (hst : SameFrameData s t) (htu : SameFrameData t u) : SameFrameData s u :=
  ⟨htu.1.trans hst.1, htu.2.1.trans hst.2.1,
    htu.2.2.1.trans hst.2.2.1, htu.2.2.2.trans hst.2.2.2⟩

private theorem revokeFrameCaps_spec (s : MachineState cfg) (f : FrameId cfg)
    (cs : List (CapabilityId cfg)) :
    Executes s (revokeFrameCaps s f cs).1 (revokeFrameCaps s f cs).2 ∧
    SameFrameData s (revokeFrameCaps s f cs).2 ∧
    (∀ c cap, (revokeFrameCaps s f cs).2.shares c = some cap →
      s.shares c = some cap ∧ (c ∈ cs → cap.frame ≠ f)) := by
  induction cs generalizing s with
  | nil => exact ⟨.nil s, ⟨rfl, rfl, rfl, rfl⟩, fun _ _ h => ⟨h, by simp⟩⟩
  | cons c cs ih =>
      cases hs : s.shares c with
      | none =>
          simp only [revokeFrameCaps, hs]
          obtain ⟨he, hd, hc⟩ := ih s
          refine ⟨he, hd, ?_⟩
          intro c' cap h
          obtain ⟨hcap, hclear⟩ := hc c' cap h
          refine ⟨hcap, ?_⟩
          intro hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · rw [hs] at hcap; contradiction
          · exact hclear hmem
      | some cap =>
          by_cases hf : cap.frame = f
          · simp only [revokeFrameCaps, hs, hf, if_true]
            obtain ⟨he, hd, hc⟩ := ih (revokeState s c cap)
            refine ⟨.cons ((step_revoke_iff s _ c).mpr ⟨cap, hs, rfl⟩) he, ?_, ?_⟩
            · simpa [SameFrameData] using hd
            · intro c' cap' h
              obtain ⟨hcap, hclear⟩ := hc c' cap' h
              by_cases hcc : c' = c
              · subst c'; simp at hcap
              · refine ⟨by simpa [setShare, hcc] using hcap, ?_⟩
                intro hmem
                exact hclear ((List.mem_cons.mp hmem).resolve_left hcc)
          · simp only [revokeFrameCaps, hs, hf, if_false]
            obtain ⟨he, hd, hc⟩ := ih s
            refine ⟨he, hd, ?_⟩
            intro c' cap' h
            obtain ⟨hcap, hclear⟩ := hc c' cap' h
            refine ⟨hcap, ?_⟩
            intro hmem
            rcases List.mem_cons.mp hmem with rfl | hmem
            · rw [hs] at hcap
              cases hcap
              exact hf
            · exact hclear hmem

private theorem unmapFramePages_spec (s : MachineState cfg) (f : FrameId cfg)
    (pages : List (GuestId cfg × GuestPage cfg)) :
    Executes s (unmapFramePages s f pages).1 (unmapFramePages s f pages).2 ∧
    SameFrameData s (unmapFramePages s f pages).2 ∧
    (unmapFramePages s f pages).2.shares = s.shares ∧
    (∀ g p m, (unmapFramePages s f pages).2.mappings g p = some m →
      s.mappings g p = some m ∧ ((g, p) ∈ pages → m.frame ≠ f)) := by
  induction pages generalizing s with
  | nil => exact ⟨.nil s, ⟨rfl, rfl, rfl, rfl⟩, rfl, fun _ _ _ h => ⟨h, by simp⟩⟩
  | cons slot pages ih =>
      obtain ⟨g, p⟩ := slot
      cases hs : s.mappings g p with
      | none =>
          simp only [unmapFramePages, hs]
          obtain ⟨he, hd, hc, hm⟩ := ih s
          refine ⟨he, hd, hc, ?_⟩
          intro g' p' m h
          obtain ⟨hmap, hclear⟩ := hm g' p' m h
          refine ⟨hmap, ?_⟩
          intro hmem
          rcases List.mem_cons.mp hmem with hslot | hmem
          · cases hslot; rw [hs] at hmap; contradiction
          · exact hclear hmem
      | some m =>
          by_cases hf : m.frame = f
          · simp only [unmapFramePages, hs, hf, if_true]
            obtain ⟨he, hd, hc, hm⟩ := ih
              (setPendingFlush (setMapping s g p none) g p (f :: s.pendingFlush g p))
            refine ⟨.cons ((step_unmap_iff s _ g p).mpr ⟨m, hs, by rw [hf]⟩) he,
              by simpa [SameFrameData] using hd, by simpa using hc, ?_⟩
            intro g' p' m' h
            obtain ⟨hmap, hclear⟩ := hm g' p' m' h
            by_cases hslot : g' = g ∧ p' = p
            · obtain ⟨hg, hp⟩ := hslot
              subst g'; subst p'; simp at hmap
            · refine ⟨by simpa [setMapping, hslot] using hmap, ?_⟩
              intro hmem
              exact hclear ((List.mem_cons.mp hmem).resolve_left (by
                intro h; exact hslot (Prod.mk.inj h)))
          · simp only [unmapFramePages, hs, hf, if_false]
            obtain ⟨he, hd, hc, hm⟩ := ih s
            refine ⟨he, hd, hc, ?_⟩
            intro g' p' m' h
            obtain ⟨hmap, hclear⟩ := hm g' p' m' h
            refine ⟨hmap, ?_⟩
            intro hmem
            rcases List.mem_cons.mp hmem with hslot | hmem
            · cases hslot
              rw [hs] at hmap
              cases hmap
              exact hf
            · exact hclear hmem

private theorem flushPages_spec (s : MachineState cfg)
    (pages : List (GuestId cfg × GuestPage cfg)) :
    Executes s (flushPages s pages).1 (flushPages s pages).2 ∧
    SameFrameData s (flushPages s pages).2 ∧
    (flushPages s pages).2.shares = s.shares ∧
    (flushPages s pages).2.mappings = s.mappings ∧
    (∀ g p, (flushPages s pages).2.tlb g p =
      if (g, p) ∈ pages then none else s.tlb g p) ∧
    (∀ g p, (flushPages s pages).2.pendingFlush g p =
      if (g, p) ∈ pages then [] else s.pendingFlush g p) := by
  induction pages generalizing s with
  | nil => exact ⟨.nil s, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl,
      by simp [flushPages], by simp [flushPages]⟩
  | cons slot pages ih =>
      obtain ⟨g, p⟩ := slot
      obtain ⟨he, hd, hc, hm, ht, hp⟩ := ih (setPendingFlush (setTlb s g p none) g p [])
      refine ⟨.cons rfl he, by simpa [flushPages, SameFrameData] using hd,
        by simpa [flushPages] using hc, by simpa [flushPages] using hm, ?_, ?_⟩
      · intro g' p'
        by_cases hmem : (g', p') ∈ pages <;> by_cases hslot : g' = g ∧ p' = p <;>
          simpa [flushPages, List.mem_cons, setTlb, Prod.mk.injEq, hmem, hslot] using ht g' p'
      · intro g' p'
        by_cases hmem : (g', p') ∈ pages <;> by_cases hslot : g' = g ∧ p' = p <;>
          simpa [flushPages, List.mem_cons, setPendingFlush, Prod.mk.injEq, hmem, hslot] using hp g' p'

theorem mem_allGuestPages (g : GuestId cfg) (p : GuestPage cfg) :
    (g, p) ∈ allGuestPages cfg := by
  simp [allGuestPages, List.mem_flatMap, List.finRange]

theorem reclaimFrame_succeeds {s : MachineState cfg} (hwf : WellFormed s)
    {g : GuestId cfg} {f : FrameId cfg} (hown : s.status f = .owned g)
    (hpin : s.pins f = 0) :
    ∃ trace t, reclaimFrame s g f = .ok (trace, t) ∧ Executes s trace t ∧
      WellFormed t ∧ t.status f = .free ∧ t.contents f = zeroContents ∧
      t.epoch f = s.epoch f + 1 := by
  let started := updateFrame s f (.reclaiming g) (s.contents f) (s.pins f) (s.epoch f)
  have hb : Step s (.beginReclaim g f) started :=
    (step_beginReclaim_iff s started g f).mpr ⟨hown, hpin, rfl⟩
  let r := revokeFrameCaps started f (List.finRange cfg.numCaps)
  let u := unmapFramePages r.2 f (allGuestPages cfg)
  let v := flushPages u.2 (allGuestPages cfg)
  obtain ⟨hr, hdr, hcaps⟩ := revokeFrameCaps_spec started f (List.finRange cfg.numCaps)
  obtain ⟨hu, hdu, hshares, hmaps⟩ := unmapFramePages_spec r.2 f (allGuestPages cfg)
  obtain ⟨hv, hdv, hvshares, hvmaps, htlb, hpending⟩ := flushPages_spec u.2 (allGuestPages cfg)
  have hd : SameFrameData started v.2 := (hdr.trans hdu).trans hdv
  have hrec : v.2.status f = .reclaiming g := by rw [hd.1]; simp [started]
  have hpin0 : v.2.pins f = 0 := by rw [hd.2.1]; simpa [started] using hpin
  have hnocaps : ¬ hasCapsOn v.2 f := by
    rintro ⟨c, cap, hc, hf⟩
    rw [hvshares, hshares] at hc
    exact (hcaps c cap hc).2 (by simp [List.finRange]) hf
  have hnomaps : ¬ hasMappingsTo v.2 f := by
    rintro ⟨g', p, m, hm, hf⟩
    rw [hvmaps] at hm
    exact (hmaps g' p m hm).2 (mem_allGuestPages g' p) hf
  have hnotlb : ¬ hasTlbRef v.2 f := by
    rintro ⟨g', p, e, he, -⟩
    rw [htlb, if_pos (mem_allGuestPages g' p)] at he
    contradiction
  have hnopending : ¬ hasPendingFlushFor v.2 f := by
    rintro ⟨g', p, hp⟩
    rw [hpending, if_pos (mem_allGuestPages g' p)] at hp
    contradiction
  let t := updateFrame v.2 f .free zeroContents 0 (v.2.epoch f + 1)
  have he : Step v.2 (.reclaim f) t :=
    (step_reclaim_iff v.2 t f).mpr
      ⟨⟨g, hrec⟩, hnomaps, hnocaps, hpin0, hnotlb, hnopending, rfl⟩
  let trace := .beginReclaim g f :: r.1 ++ u.1 ++ v.1 ++ [.reclaim f]
  have hexec : Executes s trace t :=
    ((((Executes.cons hb (.nil started)).append hr).append hu).append hv).append
      (.cons he (.nil t))
  refine ⟨trace, t, ?_, hexec, execution_preserves_wellFormed s t trace hwf hexec,
    by simp [t], by simp [t], ?_⟩
  · change reclaimFrame s g f = .ok (trace, t)
    unfold reclaimFrame
    rw [show step s (.beginReclaim g f) = .ok started from hb]
    change (step v.2 (.reclaim f) >>= fun reclaimed => .ok (trace, reclaimed)) = _
    rw [show step v.2 (.reclaim f) = .ok t from he]
    rfl
  · simp only [t, updateFrame_epoch_self]
    rw [hd.2.2.1]
    simp [started]

end Romulus
