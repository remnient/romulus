import romulus.TLB.Model

namespace Romulus

variable {cfg : Config}

inductive WalkError where
  | notPresent
  deriving DecidableEq, Repr

structure PageTable (cfg : Config) where
  entries : GuestId cfg → Fin cfg.l1Size → Fin cfg.l2Size → Option (Mapping cfg)

def decodeL1 (p : GuestPage cfg) : Fin cfg.l1Size :=
  ⟨p.val / cfg.l2Size,
   (Nat.div_lt_iff_lt_mul cfg.l2Pos).mpr (by rw [cfg.tableShape]; exact p.isLt)⟩

def decodeL2 (p : GuestPage cfg) : Fin cfg.l2Size :=
  ⟨p.val % cfg.l2Size, Nat.mod_lt _ cfg.l2Pos⟩

def encode (l1 : Fin cfg.l1Size) (l2 : Fin cfg.l2Size) : GuestPage cfg :=
  ⟨l1.val * cfg.l2Size + l2.val, by
    rw [← cfg.tableShape]
    calc l1.val * cfg.l2Size + l2.val
        < l1.val * cfg.l2Size + cfg.l2Size := Nat.add_lt_add_left l2.isLt _
      _ = (l1.val + 1) * cfg.l2Size := (Nat.succ_mul l1.val cfg.l2Size).symm
      _ ≤ cfg.l1Size * cfg.l2Size := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt l1.isLt)⟩

theorem decodeL1_encode (l1 : Fin cfg.l1Size) (l2 : Fin cfg.l2Size) :
    decodeL1 (encode l1 l2) = l1 := by
  apply Fin.ext
  simp only [decodeL1, encode]
  exact Nat.div_eq_of_lt_le (Nat.le_add_right _ _) (by
    calc l1.val * cfg.l2Size + l2.val
        < l1.val * cfg.l2Size + cfg.l2Size := Nat.add_lt_add_left l2.isLt _
      _ = (l1.val + 1) * cfg.l2Size := (Nat.succ_mul l1.val cfg.l2Size).symm)

theorem decodeL2_encode (l1 : Fin cfg.l1Size) (l2 : Fin cfg.l2Size) :
    decodeL2 (encode l1 l2) = l2 := by
  apply Fin.ext
  simp only [decodeL2, encode]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt l2.isLt

theorem encode_decode (p : GuestPage cfg) : encode (decodeL1 p) (decodeL2 p) = p := by
  apply Fin.ext
  simp only [encode, decodeL1, decodeL2]
  simpa [Nat.mul_comm] using Nat.div_add_mod p.val cfg.l2Size

def walk (pt : PageTable cfg) (g : GuestId cfg) (p : GuestPage cfg) :
    Except WalkError (FrameId cfg × Permission) :=
  match pt.entries g (decodeL1 p) (decodeL2 p) with
  | some m => .ok (m.frame, m.perms)
  | none => .error .notPresent

def Represents (pt : PageTable cfg) (s : MachineState cfg) : Prop :=
  ∀ g p, s.mappings g p = pt.entries g (decodeL1 p) (decodeL2 p)

def ofMappings (s : MachineState cfg) : PageTable cfg :=
  ⟨fun g l1 l2 => s.mappings g (encode l1 l2)⟩

theorem ofMappings_represents (s : MachineState cfg) : Represents (ofMappings s) s := by
  intro g p
  simp only [ofMappings, encode_decode]

theorem walk_eq {pt : PageTable cfg} {s : MachineState cfg} (hr : Represents pt s)
    (g : GuestId cfg) (p : GuestPage cfg) :
    walk pt g p = (match s.mappings g p with
      | some m => .ok (m.frame, m.perms)
      | none => .error .notPresent) := by
  unfold walk
  rw [← hr g p]

theorem walk_authorised {pt : PageTable cfg} {s : MachineState cfg} (hwf : WellFormed s)
    (hr : Represents pt s) {g : GuestId cfg} {p : GuestPage cfg} {f : FrameId cfg}
    {perms : Permission} (h : walk pt g p = .ok (f, perms)) {op : AccessOp}
    (hop : permAllows perms op) :
    s.status f = .owned g ∨ s.status f = .reclaiming g ∨
      ∃ cap : ShareCapability cfg,
        (∃ c' : CapabilityId cfg, s.shares c' = some cap) ∧
        cap.holder = g ∧ cap.frame = f ∧ permAllows cap.perms op := by
  rw [walk_eq hr g p] at h
  cases hm : s.mappings g p with
  | none => simp only [hm] at h; exact absurd h (by simp)
  | some m =>
      simp only [hm, Except.ok.injEq, Prod.mk.injEq] at h
      have hperm : permAllows m.perms op := by rw [h.2]; exact hop
      rcases mapping_authorised hwf hm hperm with hh | hh | hh
      · exact Or.inl (by rwa [h.1] at hh)
      · exact Or.inr (Or.inl (by rwa [h.1] at hh))
      · obtain ⟨cap, hslot, hholder, hframe, hcapPerm⟩ := hh
        exact Or.inr (Or.inr ⟨cap, hslot, hholder, by rwa [h.1] at hframe, hcapPerm⟩)

end Romulus
