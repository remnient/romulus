 

import romulus.Core.Invariants

namespace Romulus

variable {cfg : Config}

inductive AccessOp where
  | read
  | write
  | execute
  deriving DecidableEq, Repr

inductive AccessError where
  | noTranslation
  | permissionDenied
  deriving DecidableEq, Repr

def permAllows (p : Permission) : AccessOp → Prop
  | .read => p.read = true
  | .write => p.write = true
  | .execute => p.execute = true

instance (p : Permission) (op : AccessOp) : Decidable (permAllows p op) := by
  cases op <;> unfold permAllows <;> infer_instance

def access (s : MachineState cfg) (g : GuestId cfg) (op : AccessOp) (p : GuestPage cfg) :
    Except AccessError (FrameId cfg) :=
  match s.tlb g p with
  | some e =>
      if permAllows e.perms op then .ok e.frame else .error .permissionDenied
  | none =>
    match s.mappings g p with
    | some m =>
        if permAllows m.perms op then .ok m.frame else .error .permissionDenied
    | none => .error .noTranslation

def pageCoherent (s : MachineState cfg) (g : GuestId cfg) (p : GuestPage cfg) : Prop :=
  ∀ e, s.tlb g p = some e → ∃ m, s.mappings g p = some m ∧ m.frame = e.frame ∧ m.perms = e.perms

def accessWithFill (s : MachineState cfg) (g : GuestId cfg) (op : AccessOp) (p : GuestPage cfg) :
    Except AccessError (FrameId cfg × MachineState cfg) :=
  match s.tlb g p with
  | some e =>
      if permAllows e.perms op then .ok (e.frame, s) else .error .permissionDenied
  | none =>
      match s.mappings g p with
      | some m =>
          if permAllows m.perms op then
            .ok (m.frame, setTlb s g p (some ⟨m.frame, m.perms⟩))
          else .error .permissionDenied
      | none => .error .noTranslation

theorem accessWithFill_result (s : MachineState cfg) (g : GuestId cfg) (op : AccessOp)
    (p : GuestPage cfg) : (accessWithFill s g op p).map Prod.fst = access s g op p := by
  unfold accessWithFill access
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · rfl

theorem accessWithFill_miss {s : MachineState cfg} {g : GuestId cfg} {p : GuestPage cfg}
    {m : Mapping cfg} {op : AccessOp} (ht : s.tlb g p = none)
    (hm : s.mappings g p = some m) (hp : permAllows m.perms op) :
    accessWithFill s g op p = .ok (m.frame, setTlb s g p (some ⟨m.frame, m.perms⟩)) := by
  simp [accessWithFill, ht, hm, hp]

theorem accessWithFill_hit {s : MachineState cfg} {g : GuestId cfg} {p : GuestPage cfg}
    {e : TlbEntry cfg} {op : AccessOp} (ht : s.tlb g p = some e)
    (hp : permAllows e.perms op) : accessWithFill s g op p = .ok (e.frame, s) := by
  simp [accessWithFill, ht, hp]

theorem accessWithFill_coherent {s t : MachineState cfg} {g : GuestId cfg}
    {p : GuestPage cfg} {op : AccessOp} {f : FrameId cfg} (hc : pageCoherent s g p)
    (h : accessWithFill s g op p = .ok (f, t)) : pageCoherent t g p := by
  unfold accessWithFill at h
  split at h
  · split at h
    · cases h; exact hc
    · contradiction
  · split at h
    · rename_i m hm
      split at h
      · cases h
        intro e he
        simp only [setTlb_self, Option.some.injEq] at he
        subst e
        exact ⟨m, hm, rfl, rfl⟩
      · contradiction
    · contradiction

theorem access_congr {s t : MachineState cfg} {g : GuestId cfg}
    (htlb : ∀ p, cachedTranslationOf t g p = cachedTranslationOf s g p)
    (hmap : ∀ p, translationOf t g p = translationOf s g p) :
    ∀ op p, access t g op p = access s g op p := by
  intro op p
  cases htt : t.tlb g p with
  | some e =>
      cases hss : s.tlb g p with
      | some e' =>
          have hce := htlb p
          simp only [cachedTranslationOf, htt, hss] at hce
          injection hce with hpair
          injection hpair with hf hp
          simp only [access, htt, hss, hf, hp]
      | none =>
          have hce := htlb p
          simp only [cachedTranslationOf, htt, hss] at hce
          exact absurd hce (by simp)
  | none =>
      cases hss : s.tlb g p with
      | some e' =>
          have hce := htlb p
          simp only [cachedTranslationOf, htt, hss] at hce
          exact absurd hce (by simp)
      | none =>
          have hme := hmap p
          cases hmt : t.mappings g p with
          | some m =>
              cases hms : s.mappings g p with
              | some m' =>
                  simp only [translationOf, hmt, hms] at hme
                  injection hme with hpair
                  injection hpair with hf hp
                  simp only [access, htt, hss, hmt, hms, hf, hp]
              | none =>
                  simp only [translationOf, hmt, hms] at hme
                  exact absurd hme (by simp)
          | none =>
              cases hms : s.mappings g p with
              | some m' =>
                  simp only [translationOf, hmt, hms] at hme
                  exact absurd hme (by simp)
              | none => simp only [access, htt, hss, hmt, hms]

theorem access_ok_translation {s : MachineState cfg} {g : GuestId cfg} {op : AccessOp}
    {p : GuestPage cfg} {f : FrameId cfg} (h : access s g op p = .ok f) :
    (∃ e, s.tlb g p = some e ∧ e.frame = f ∧ permAllows e.perms op) ∨
    (∃ m, s.mappings g p = some m ∧ m.frame = f ∧ permAllows m.perms op) := by
  unfold access at h
  cases ht : s.tlb g p with
  | some e =>
      by_cases hp : permAllows e.perms op
      · simp only [ht, hp, if_true] at h
        exact Or.inl ⟨e, rfl, Except.ok.inj h, hp⟩
      · simp only [ht, hp, if_false] at h
        exact absurd h (by simp)
  | none =>
      cases hm : s.mappings g p with
      | none => simp only [ht, hm] at h; exact absurd h (by simp)
      | some m =>
          by_cases hp : permAllows m.perms op
          · simp only [ht, hm, hp, if_true] at h
            exact Or.inr ⟨m, rfl, Except.ok.inj h, hp⟩
          · simp only [ht, hm, hp, if_false] at h
            exact absurd h (by simp)

theorem mapping_authorised {s : MachineState cfg} (hwf : WellFormed s)
    {g : GuestId cfg} {p : GuestPage cfg} {m : Mapping cfg}
    (hm : s.mappings g p = some m) {op : AccessOp} (hperm : permAllows m.perms op) :
    s.status m.frame = .owned g ∨ s.status m.frame = .reclaiming g ∨
      ∃ cap : ShareCapability cfg,
        (∃ c' : CapabilityId cfg, s.shares c' = some cap) ∧
        cap.holder = g ∧ cap.frame = m.frame ∧ permAllows cap.perms op := by
  have hJ := hwf.mapping_authority g p m hm
  unfold MappingJustified at hJ
  cases hmo : m.origin <;> simp [hmo] at hJ
  · rcases hJ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · obtain ⟨c', hc'⟩ := hJ
    simp only [capGrants] at hc'
    cases hsh : s.shares c' with
    | none => simp only [hsh] at hc'
    | some cap =>
        simp only [hsh] at hc'
        obtain ⟨hholder, hframe, -, hleq⟩ := hc'
        refine Or.inr (Or.inr ⟨cap, ⟨c', hsh⟩, hholder, hframe, ?_⟩)
        cases op <;> simp only [permAllows] at hperm ⊢
        · exact hleq.1 hperm
        · exact hleq.2.1 hperm
        · exact hleq.2.2 hperm

theorem access_authorised {s : MachineState cfg} (hwf : WellFormed s)
    {g : GuestId cfg} {p : GuestPage cfg} (hc : pageCoherent s g p)
    {op : AccessOp} {f : FrameId cfg} (h : access s g op p = .ok f) :
    s.status f = .owned g ∨ s.status f = .reclaiming g ∨
      ∃ cap : ShareCapability cfg,
        (∃ c' : CapabilityId cfg, s.shares c' = some cap) ∧
        cap.holder = g ∧ cap.frame = f ∧ permAllows cap.perms op := by
  rcases access_ok_translation h with ⟨e, he, hef, hperm⟩ | ⟨m, hm, hmf, hperm⟩
  · obtain ⟨m, hm, hframe, hperms⟩ := hc e he
    have hperm' : permAllows m.perms op := by rw [hperms]; exact hperm
    have hmf' : m.frame = f := by rw [hframe, hef]
    rcases mapping_authorised hwf hm hperm' with h | h | h
    · exact Or.inl (by rwa [hmf'] at h)
    · exact Or.inr (Or.inl (by rwa [hmf'] at h))
    · obtain ⟨cap, hslot, hholder, hcapframe, hcapPerm⟩ := h
      exact Or.inr (Or.inr ⟨cap, hslot, hholder, by rwa [hmf'] at hcapframe, hcapPerm⟩)
  · rcases mapping_authorised hwf hm hperm with h | h | h
    · exact Or.inl (by rwa [hmf] at h)
    · exact Or.inr (Or.inl (by rwa [hmf] at h))
    · obtain ⟨cap, hslot, hholder, hcapframe, hcapPerm⟩ := h
      exact Or.inr (Or.inr ⟨cap, hslot, hholder, by rwa [hmf] at hcapframe, hcapPerm⟩)

theorem access_none_of_no_translation {s : MachineState cfg} {g : GuestId cfg} {op : AccessOp}
    {p : GuestPage cfg} (ht : s.tlb g p = none) (hm : s.mappings g p = none) :
    access s g op p = .error .noTranslation := by
  simp [access, ht, hm]

theorem pageCoherent_after_flush {s : MachineState cfg} {g : GuestId cfg} {p : GuestPage cfg} :
    pageCoherent (setPendingFlush (setTlb s g p none) g p []) g p := by
  intro e he
  simp [setTlb] at he

end Romulus
