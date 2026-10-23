import LuRazFullGuarded
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

inductive FixedGen where
  | A | B | C | D | E | Z | K1 | K2
  deriving DecidableEq, Repr

def FixedGen.index (q : Nat) : FixedGen → Nat
  | .A => 4*q+2 | .B => 4*q+1 | .C => 4*q | .D => 1
  | .E => 4 | .Z => 2 | .K1 => 2*q+1 | .K2 => 2*q+2
def FixedGen.eval (q : Nat) : FixedGen → Nat → Prop
  | .A => ARow q | .B => BRow q | .C => CRow q | .D => DRow q
  | .E => ERow q | .Z => ZRow q | .K1 => K1Row q | .K2 => K2Row q

theorem FixedGen.source (q : Nat) (hq : 4≤q) (k : FixedGen) (e : Nat) :
    LuRazParametric.Row q (k.index q) e ↔ k.eval q e := by
  cases k with
  | A => exact A_source q e hq
  | B => exact B_source q e hq
  | C => exact C_source q e hq
  | D => exact D_source q e hq
  | E => exact E_source q e hq
  | Z => exact Z_source q e hq
  | K1 => exact K1_source q e hq
  | K2 => exact K2_source q e hq

theorem row_nonTop_parts (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2) (hn : i≠0) :
    (∃ k : FixedGen, i=k.index q) ∨
    (∃ a, (5≤a ∧ a≤2*q+1) ∧ i=JIndex a) ∨ ∃ p, P q p ∧ i=LIndex q p := by
  classical
  by_cases h1 : LuRazParametric.Row q i 1
  · have h2 := nonTop_one_excludes_two q i hq hi hn h1
    rcases row_excluding_two q i hq hi h2 with h | h | h | h | h | h
    · exact Or.inl ⟨.A,h⟩
    · exact Or.inl ⟨.B,h⟩
    · exact Or.inl ⟨.C,h⟩
    · exact Or.inl ⟨.E,h⟩
    · exact Or.inl ⟨.Z,h⟩
    · exact Or.inr (Or.inl h)
  · rcases row_excluding_one q i hq hi h1 with h | h | h | h | h | h
    · exact Or.inl ⟨.C,h⟩
    · exact Or.inl ⟨.D,h⟩
    · exact Or.inl ⟨.B,h⟩
    · exact Or.inl ⟨.K1,h⟩
    · exact Or.inl ⟨.K2,h⟩
    · exact Or.inr (Or.inr h)

abbrev JPart := Option (Nat × Nat)
abbrev LPart := Option (Nat × Nat)
def JPart.Valid (q : Nat) : JPart → Prop
  | none => True | some (a,b) => JReachable q a b
def JPart.eval : JPart → Nat → Prop
  | none => fun _ => False | some (a,b) => JRow a b
def LPart.Valid (q : Nat) : LPart → Prop
  | none => True | some (t,p) => P q t ∧ P q p ∧ t≤p
def LPart.eval (q : Nat) : LPart → Nat → Prop
  | none => fun _ => False | some (t,p) => LRow q t p

theorem jPart_add (q a : Nat) (hq : 4≤q) (ha : 5≤a ∧ a≤2*q+1)
    (j : JPart) (hj : JPart.Valid q j) :
    ∃ j', JPart.Valid q j' ∧ ∀ e, (JRow a (g q a) e ∨ JPart.eval j e) ↔ JPart.eval j' e := by
  have ha' := J_single_reachable q a hq ha
  cases j with
  | none =>
    exact ⟨some (a,g q a),ha',fun e => by simp only [JPart.eval,or_false]⟩
  | some ab =>
    rcases ab with ⟨b,c⟩
    refine ⟨some (min a b,max (g q a) c),JReachable_join q a (g q a) b c hq ha' hj,?_⟩
    intro e
    exact JRow_join q a (g q a) b c e hq ha' hj

theorem lPart_add (q a : Nat) (hq : 4≤q) (ha : P q a)
    (l : LPart) (hl : LPart.Valid q l) :
    ∃ l', LPart.Valid q l' ∧ ∀ e, (LRow q a a e ∨ LPart.eval q l e) ↔ LPart.eval q l' e := by
  cases l with
  | none => exact ⟨some (a,a),⟨ha,ha,by omega⟩,fun e => by simp only [LPart.eval,or_false]⟩
  | some tp =>
    rcases tp with ⟨t,p⟩
    have ht := hl.1
    have hp := hl.2.1
    have htp := hl.2.2
    refine ⟨some (min a t,max a p),⟨P_min q a t ha ht,P_max q a p ha hp,by omega⟩,?_⟩
    intro e
    exact LRow_join q a a t p e hq ha ha ht hp (by omega) htp

def FixedBag (q : Nat) (f : FixedGen → Prop) (e : Nat) : Prop := ∃ k, f k ∧ k.eval q e

theorem fixedBag_update (q : Nat) (k : FixedGen) (f : FixedGen → Prop) (e : Nat) :
    FixedBag q (fun j => j=k ∨ f j) e ↔ k.eval q e ∨ FixedBag q f e := by
  constructor
  · rintro ⟨j,hj,he⟩
    rcases hj with h | h
    · subst j; exact Or.inl he
    · exact Or.inr ⟨j,h,he⟩
  · rintro (h | ⟨j,hj,he⟩)
    · exact ⟨k,Or.inl rfl,h⟩
    · exact ⟨j,Or.inr hj,he⟩

def RawFull (q : Nat) (j : JPart) (l : LPart) (f : FixedGen → Prop) (e : Nat) : Prop :=
  JPart.eval j e ∨ LPart.eval q l e ∨ FixedBag q f e

theorem raw_parts_list (q : Nat) (hq : 4≤q) (ls : List Nat)
    (hv : ∀ i∈ls, i≠0 ∧ i≤4*q+2) :
    ∃ j : JPart, JPart.Valid q j ∧ ∃ l : LPart, LPart.Valid q l ∧ ∃ f : FixedGen → Prop,
      ∀ e, ListUnion (LuRazParametric.Row q) ls e ↔ RawFull q j l f e := by
  induction ls with
  | nil =>
    refine ⟨none,True.intro,none,True.intro,(fun _ => False),?_⟩
    intro e
    simp [ListUnion,RawFull,JPart.eval,LPart.eval,FixedBag]
  | cons i rest ih =>
    have hi := hv i (by simp)
    have hr : ∀ k∈rest, k≠0 ∧ k≤4*q+2 := by
      intro k hk; exact hv k (by simp only [List.mem_cons]; exact Or.inr hk)
    obtain ⟨j,hj,l,hl,f,hn⟩ := ih hr
    rcases row_nonTop_parts q i hq hi.2 hi.1 with ⟨k,he⟩ | ⟨a,ha,he⟩ | ⟨p,hp,he⟩
    · subst i
      refine ⟨j,hj,l,hl,(fun v => v=k ∨ f v),?_⟩
      intro e
      rw [listUnion_cons,FixedGen.source q hq k e,hn]
      simp only [RawFull]
      rw [fixedBag_update]
      simp only [JRow,or_assoc,or_left_comm,or_comm]
    · subst i
      obtain ⟨j',hj',heq⟩ := jPart_add q a hq ha j hj
      refine ⟨j',hj',l,hl,f,?_⟩
      intro e
      rw [listUnion_cons,J_is_source_row q a e hq ha,hn]
      simp only [RawFull]
      rw [←heq e]
      simp only [JRow,or_assoc,or_left_comm,or_comm]
    · subst i
      obtain ⟨l',hl',heq⟩ := lPart_add q p hq hp l hl
      refine ⟨j,hj,l',hl',f,?_⟩
      intro e
      rw [listUnion_cons,LRow_source q p e hq hp,hn]
      simp only [RawFull]
      rw [←heq e]
      simp only [JRow,or_assoc,or_left_comm,or_comm]

theorem fixedBag_explicit (q : Nat) (f : FixedGen → Prop) (e : Nat) :
    FixedBag q f e ↔ (f .A∧ARow q e) ∨ (f .B∧BRow q e) ∨ (f .C∧CRow q e) ∨ (f .D∧DRow q e) ∨
      (f .E∧ERow q e) ∨ (f .Z∧ZRow q e) ∨ (f .K1∧K1Row q e) ∨ (f .K2∧K2Row q e) := by
  constructor
  · rintro ⟨k,hf,he⟩
    cases k <;> simp only [FixedGen.eval] at he <;> simp only [hf,true_and,he,true_or,or_true]
  · rintro (h | h | h | h | h | h | h | h)
    · exact ⟨.A,h.1,h.2⟩
    · exact ⟨.B,h.1,h.2⟩
    · exact ⟨.C,h.1,h.2⟩
    · exact ⟨.D,h.1,h.2⟩
    · exact ⟨.E,h.1,h.2⟩
    · exact ⟨.Z,h.1,h.2⟩
    · exact ⟨.K1,h.1,h.2⟩
    · exact ⟨.K2,h.1,h.2⟩

theorem rawFull_explicit (q : Nat) (j : JPart) (l : LPart) (f : FixedGen → Prop) (e : Nat) :
    RawFull q j l f e ↔ FixedAug q (fun e => JPart.eval j e ∨ LPart.eval q l e)
      (f .A) (f .B) (f .C) (f .D) (f .E) (f .Z) (f .K1) (f .K2) e := by
  simp only [RawFull,FixedAug,fixedBag_explicit,or_assoc]
end LuRazClosure
