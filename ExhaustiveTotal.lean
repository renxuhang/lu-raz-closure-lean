import Exhaustive123Count
import Exhaustive134Count
import ExhaustiveFullCount

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- Exactly the seven core patterns affected by the three changed rows. -/
def Changed (R : Nat → Prop) : Prop := R 3 ∧ (R 1 ∨ R 2 ∨ R 4)

theorem unchanged_outside_changed (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hc : ¬Changed R) : Generated q R ↔ LuRazClosure.Generated q R := by
  classical
  by_cases h3 : R 3
  · have h1 : ¬R 1 := fun h => hc ⟨h3,Or.inl h⟩
    have h2 : ¬R 2 := fun h => hc ⟨h3,Or.inr (Or.inl h)⟩
    have h4 : ¬R 4 := fun h => hc ⟨h3,Or.inr (Or.inr h)⟩
    exact no_one_two_four_unchanged q hq R h1 h2 h4
  · exact no_three_unchanged q hq R h3

theorem old_core12_empty (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    ¬(LuRazClosure.Generated q R ∧ Core12 R) := by
  rintro ⟨⟨l,hn,hv,he⟩,hc⟩
  obtain ⟨i,hi,hi4⟩ := (he 4).mpr hc.2.2.2
  rcases row_four_implies_one_or_two q i hq (hv i hi) hi4 with h | h
  · exact hc.1 ((he 1).mp ⟨i,hi,h⟩)
  · exact hc.2.1 ((he 2).mp ⟨i,hi,h⟩)

theorem append_enumerations (G P Q : (Nat → Prop) → Prop)
    (a b : List (Nat → Prop)) (ha : a.Nodup) (hb : b.Nodup)
    (hea : ∀ R, R∈a ↔ G R ∧ P R) (heb : ∀ R, R∈b ↔ G R ∧ Q R)
    (hd : ∀ R, P R → Q R → False) :
    (a++b).Nodup ∧ (∀ R, R∈a++b ↔ G R ∧ (P R ∨ Q R)) := by
  constructor
  · rw [List.nodup_append]
    refine ⟨ha,hb,?_⟩
    intro R hR T hT he
    subst T
    exact hd R ((hea R).mp hR).2 ((heb R).mp hT).2
  · intro R
    rw [List.mem_append,hea R,heb R]
    constructor
    · rintro (⟨hg,h⟩ | ⟨hg,h⟩)
      · exact ⟨hg,Or.inl h⟩
      · exact ⟨hg,Or.inr h⟩
    · rintro ⟨hg,h | h⟩
      · exact Or.inl ⟨hg,h⟩
      · exact Or.inr ⟨hg,h⟩

theorem seven_enumerations (G : (Nat → Prop) → Prop)
    (l0 : List (Nat → Prop)) (hn0 : l0.Nodup)
    (he0 : ∀ R, R∈l0 ↔ G R ∧ Core5 R)
    (l1 : List (Nat → Prop)) (hn1 : l1.Nodup)
    (he1 : ∀ R, R∈l1 ↔ G R ∧ Core23 R)
    (l2 : List (Nat → Prop)) (hn2 : l2.Nodup)
    (he2 : ∀ R, R∈l2 ↔ G R ∧ Core123 R)
    (l3 : List (Nat → Prop)) (hn3 : l3.Nodup)
    (he3 : ∀ R, R∈l3 ↔ G R ∧ Core12 R)
    (l4 : List (Nat → Prop)) (hn4 : l4.Nodup)
    (he4 : ∀ R, R∈l4 ↔ G R ∧ Core134 R)
    (l5 : List (Nat → Prop)) (hn5 : l5.Nodup)
    (he5 : ∀ R, R∈l5 ↔ G R ∧ Core234 R)
    (l6 : List (Nat → Prop)) (hn6 : l6.Nodup)
    (he6 : ∀ R, R∈l6 ↔ G R ∧ CoreFull R)
    : (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6).Nodup ∧
      (∀ R, R∈(l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6) ↔ G R ∧ Changed R) := by
  have h1 := append_enumerations G Core5 Core23 l0 l1 hn0 hn1 he0 he1 (by
    intro R h h'
    simp_all [Core5,Core23,Core123,Core12,Core134,Core234,CoreFull])
  have h2 := append_enumerations G (fun R => (Core5 R ∨ Core23 R)) Core123 (l0 ++ l1) l2 h1.1 hn2 h1.2 he2 (by
    intro R h h'
    simp_all [Core5,Core23,Core123,Core12,Core134,Core234,CoreFull])
  have h3 := append_enumerations G (fun R => ((Core5 R ∨ Core23 R) ∨ Core123 R)) Core12 (l0 ++ l1 ++ l2) l3 h2.1 hn3 h2.2 he3 (by
    intro R h h'
    simp_all [Core5,Core23,Core123,Core12,Core134,Core234,CoreFull])
  have h4 := append_enumerations G (fun R => (((Core5 R ∨ Core23 R) ∨ Core123 R) ∨ Core12 R)) Core134 (l0 ++ l1 ++ l2 ++ l3) l4 h3.1 hn4 h3.2 he4 (by
    intro R h h'
    simp_all [Core5,Core23,Core123,Core12,Core134,Core234,CoreFull])
  have h5 := append_enumerations G (fun R => ((((Core5 R ∨ Core23 R) ∨ Core123 R) ∨ Core12 R) ∨ Core134 R)) Core234 (l0 ++ l1 ++ l2 ++ l3 ++ l4) l5 h4.1 hn5 h4.2 he5 (by
    intro R h h'
    simp_all [Core5,Core23,Core123,Core12,Core134,Core234,CoreFull])
  have h6 := append_enumerations G (fun R => (((((Core5 R ∨ Core23 R) ∨ Core123 R) ∨ Core12 R) ∨ Core134 R) ∨ Core234 R)) CoreFull (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5) l6 h5.1 hn6 h5.2 he6 (by
    intro R h h'
    simp_all [Core5,Core23,Core123,Core12,Core134,Core234,CoreFull])
  refine ⟨h6.1,?_⟩
  intro R
  rw [h6.2 R]
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;> by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp_all [Changed,Core5,Core23,Core123,Core12,Core134,Core234,CoreFull]

theorem old_changed_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ LuRazClosure.Generated q R ∧ Changed R) ∧
      2*(l.length : Int)=17*(q:Int)*(q:Int)+27*(q:Int)-52 := by
  obtain ⟨l0,hn0,he0,hl0⟩ := LuRazClosure.small_cardinality q hq 5 (by omega)
  obtain ⟨l1,hn1,he1,hl1⟩ := LuRazClosure.core23_cardinality q hq
  obtain ⟨l2,hn2,he2,hl2⟩ := LuRazClosure.core123_cardinality q hq
  let l3 : List (Nat → Prop) := []
  have hn3 : l3.Nodup := List.nodup_nil
  have he3 : ∀ R, R∈l3 ↔ LuRazClosure.Generated q R ∧ Core12 R := by
    intro R; simp [l3,old_core12_empty q hq R]
  have hl3 : l3.length=0 := rfl
  obtain ⟨l4,hn4,he4,hl4⟩ := LuRazClosure.core134_cardinality q hq
  obtain ⟨l5,hn5,he5,hl5⟩ := LuRazClosure.core234_cardinality q hq
  obtain ⟨l6,hn6,he6,hl6⟩ := LuRazClosure.full_cardinality q hq
  have he0' : ∀ R, R∈l0 ↔ LuRazClosure.Generated q R ∧ Core5 R := by
    intro R; simpa [CoreSmallAt,Core5] using he0 R
  have hl0' : l0.length=5 := by simpa [smallCount] using hl0
  have h := seven_enumerations (LuRazClosure.Generated q) l0 hn0 he0' l1 hn1 he1 l2 hn2 he2 l3 hn3 he3 l4 hn4 he4 l5 hn5 he5 l6 hn6 he6
  refine ⟨l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6,h.1,h.2,?_⟩
  simp only [List.length_append,Int.natCast_add]
  simp only [Int.mul_assoc] at *
  omega

theorem new_changed_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ Changed R) ∧
      2*(l.length : Int)=17*(q:Int)*(q:Int)+23*(q:Int)-40 := by
  obtain ⟨l0,hn0,he0,hl0⟩ := core5_cardinality q hq
  obtain ⟨l1,hn1,he1,hl1⟩ := LuRazThreeRow.core23_cardinality q hq
  obtain ⟨l2,hn2,he2,hl2⟩ := core123_new_cardinality q hq
  obtain ⟨l3,hn3,he3,hl3⟩ := core12_cardinality q hq
  obtain ⟨l4,hn4,he4,hl4⟩ := core134_new_cardinality q hq
  obtain ⟨l5,hn5,he5,hl5⟩ := LuRazThreeRow.core234_cardinality q hq
  obtain ⟨l6,hn6,he6,hl6⟩ := full_new_cardinality q hq
  have h := seven_enumerations (Generated q) l0 hn0 he0 l1 hn1 he1 l2 hn2 he2 l3 hn3 he3 l4 hn4 he4 l5 hn5 he5 l6 hn6 he6
  refine ⟨l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6,h.1,h.2,?_⟩
  simp only [List.length_append,Int.natCast_add]
  simp only [Int.mul_assoc] at *
  omega


theorem closure_new_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R) ∧
      2*(l.length : Int)=23*(q:Int)*(q:Int)+31*(q:Int)-30 := by
  classical
  obtain ⟨o,hon,hoe,hol⟩ := old_changed_cardinality q hq
  obtain ⟨n,hnn,hne,hnl⟩ := new_changed_cardinality q hq
  let u := (closureMembers q).filter (fun R => decide (¬Changed R))
  have hun : u.Nodup := List.Nodup.sublist List.filter_sublist (closure_members_nodup q hq)
  have hue : ∀ R, R∈u ↔ LuRazClosure.Generated q R ∧ ¬Changed R := by
    intro R
    simp only [u,List.mem_filter,decide_eq_true_eq,closure_members_exact q hq R]
  have huen : ∀ R, R∈u ↔ Generated q R ∧ ¬Changed R := by
    intro R
    rw [hue R]
    by_cases hc : Changed R
    · simp [hc]
    · rw [unchanged_outside_changed q hq R hc]
  have ho := append_enumerations (LuRazClosure.Generated q) (fun R => ¬Changed R) Changed
    u o hun hon hue hoe (fun R h h' => h h')
  have hn := append_enumerations (Generated q) (fun R => ¬Changed R) Changed
    u n hun hnn huen hne (fun R h h' => h h')
  have hp : (u++o).Perm (closureMembers q) := by
    apply (List.perm_ext_iff_of_nodup ho.1 (closure_members_nodup q hq)).mpr
    intro R
    rw [ho.2 R,closure_members_exact q hq R]
    by_cases hc : Changed R <;> simp [hc]
  have hlen := hp.length_eq
  have htotal := closure_members_length q hq
  refine ⟨u++n,hn.1,?_,?_⟩
  · intro R
    rw [hn.2 R]
    by_cases hc : Changed R <;> simp [hc]
  · simp only [List.length_append,Int.natCast_add] at hlen ⊢
    simp only [Int.mul_assoc] at *
    omega

end LuRazThreeRow
