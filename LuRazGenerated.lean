import LuRazVariableUnions

namespace LuRazClosure

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Nonempty finite unions of the entire explicit source family. -/
def Generated (q : Nat) (R : Nat → Prop) : Prop :=
  ∃ l : List Nat, l ≠ [] ∧ (∀ i ∈ l, i ≤ 4*q+2) ∧
    ∀ e, ListUnion (LuRazParametric.Row q) l e ↔ R e

def ARow (q e : Nat) : Prop := e=1 ∨ I 5 (q+2) e
def BRow (q e : Nat) : Prop := I (3*q+2) (4*q) e
def JRow (a b e : Nat) : Prop := e=1 ∨ e=4 ∨ I a b e

theorem A_source (q e : Nat) (hq : 4 ≤ q) :
    LuRazParametric.Row q (4*q+2) e ↔ ARow q e := by
  rw [LuRazParametric.row_case_15 q (4*q+2) e (by omega) rfl]
  rfl

theorem B_source (q e : Nat) (hq : 4 ≤ q) :
    LuRazParametric.Row q (4*q+1) e ↔ BRow q e := by
  rw [LuRazParametric.row_case_14 q (4*q+1) e (by omega) rfl]
  rfl

theorem listUnion_append (f : Nat → Nat → Prop) (l k : List Nat) (e : Nat) :
    ListUnion f (l++k) e ↔ ListUnion f l e ∨ ListUnion f k e := by
  constructor
  · rintro ⟨a,ha,he⟩
    rcases List.mem_append.mp ha with h | h
    · exact Or.inl ⟨a,h,he⟩
    · exact Or.inr ⟨a,h,he⟩
  · intro h
    rcases h with h | h
    · obtain ⟨a,ha,he⟩ := h
      exact ⟨a,List.mem_append.mpr (Or.inl ha),he⟩
    · obtain ⟨a,ha,he⟩ := h
      exact ⟨a,List.mem_append.mpr (Or.inr ha),he⟩

theorem generated_congr (q : Nat) {R T : Nat → Prop}
    (hR : Generated q R) (heq : ∀ e, R e ↔ T e) : Generated q T := by
  obtain ⟨l,hne,hvalid,h⟩ := hR
  exact ⟨l,hne,hvalid,fun e => (h e).trans (heq e)⟩

theorem generated_row (q i : Nat) (hi : i ≤ 4*q+2) :
    Generated q (LuRazParametric.Row q i) := by
  refine ⟨[i],by simp,?_,?_⟩
  · intro j hj
    have hji : j=i := by simpa using hj
    subst j; exact hi
  · intro e
    constructor
    · rintro ⟨j,hj,he⟩
      have hji : j=i := by simpa using hj
      subst j; exact he
    · intro he
      exact ⟨i,by simp,he⟩

theorem generated_join (q : Nat) {R T : Nat → Prop}
    (hR : Generated q R) (hT : Generated q T) :
    Generated q (fun e => R e ∨ T e) := by
  obtain ⟨l,hne,hv,heq⟩ := hR
  obtain ⟨k,_,hkv,hkeq⟩ := hT
  refine ⟨l++k,?_,?_,?_⟩
  · intro h
    exact hne (List.append_eq_nil_iff.mp h).1
  · intro i hi
    rcases List.mem_append.mp hi with h | h
    · exact hv i h
    · exact hkv i h
  · intro e
    rw [listUnion_append,heq,hkeq]

theorem generated_optional (q : Nat) {R T : Nat → Prop}
    (hR : Generated q R) (hT : Generated q T) (u : Prop) :
    Generated q (fun e => R e ∨ (u ∧ T e)) := by
  classical
  by_cases hu : u
  · apply generated_congr q (generated_join q hR hT)
    intro e
    simp only [hu,true_and]
  · apply generated_congr q hR
    intro e
    simp only [hu,false_and,or_false]

theorem generated_A (q : Nat) (hq : 4 ≤ q) : Generated q (ARow q) :=
  generated_congr q (generated_row q (4*q+2) (by omega)) (fun e => A_source q e hq)

theorem generated_B (q : Nat) (hq : 4 ≤ q) : Generated q (BRow q) :=
  generated_congr q (generated_row q (4*q+1) (by omega)) (fun e => B_source q e hq)

theorem generated_J (q a b : Nat) (hq : 4 ≤ q) (hab : JReachable q a b) :
    Generated q (JRow a b) := by
  obtain ⟨l,hne,hvalid,heq⟩ := J_source_attainable q a b hq hab
  refine ⟨l.map JIndex,?_,?_,?_⟩
  · intro h
    exact hne (List.map_eq_nil_iff.mp h)
  · intro i hi
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
    have hv := hvalid a ha
    unfold JIndex
    split <;> omega
  · intro e
    constructor
    · rintro ⟨i,hi,hie⟩
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
      exact (heq e).mp ⟨a,ha,hie⟩
    · intro h
      obtain ⟨a,ha,hae⟩ := (heq e).mpr h
      exact ⟨JIndex a,List.mem_map.mpr ⟨a,ha,rfl⟩,hae⟩

/-- Absence of 2 and 3 excludes every generator except A, B and J. -/
theorem row_excluding_two_three (q i : Nat) (hq : 4 ≤ q)
    (hi : i ≤ 4*q+2)
    (h2 : ¬LuRazParametric.Row q i 2) (h3 : ¬LuRazParametric.Row q i 3) :
    i=4*q+2 ∨ i=4*q+1 ∨ ∃ a, (5 ≤ a ∧ a ≤ 2*q+1) ∧ i=JIndex a := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
      (5 ≤ i ∧ i ≤ q+2) ∨ (q+3 ≤ i ∧ i ≤ 2*q) ∨
      i=2*q+1 ∨ i=2*q+2 ∨ i=2*q+3 ∨
      (2*q+4 ≤ i ∧ i ≤ 3*q) ∨ i=3*q+1 ∨
      (3*q+2 ≤ i ∧ i+1 ≤ 4*q) ∨ i=4*q ∨ i=4*q+1 ∨ i=4*q+2 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact False.elim (h2 ((LuRazParametric.row_case_0 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((LuRazParametric.row_case_1 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h3 ((LuRazParametric.row_case_2 q i 3 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inr ⟨5,by omega,h⟩)
  · exact False.elim (h3 ((LuRazParametric.row_case_4 q i 3 (by omega) h).mpr (by omega)))
  · refine Or.inr (Or.inr ⟨i+1,by omega,?_⟩)
    unfold JIndex
    split <;> omega
  · refine Or.inr (Or.inr ⟨i+1,by omega,?_⟩)
    unfold JIndex
    split <;> omega
  · exact False.elim (h2 ((LuRazParametric.row_case_7 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((LuRazParametric.row_case_8 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((LuRazParametric.row_case_9 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((LuRazParametric.row_case_10 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((LuRazParametric.row_case_11 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((LuRazParametric.row_case_12 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h3 ((LuRazParametric.row_case_13 q i 3 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inl h)
  · exact Or.inl h

end LuRazClosure
