import SixRowClosureDefs
import SixRowDifferenceForms
import Exhaustive134Parts

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def CPrime (q e : Nat) : Prop := e=3 ∨ I 5 (2*q+1) e ∨ e=3*q+1 ∨ e=4*q-1

def LNew (q e : Nat) : Prop := e=1 ∨ e=3 ∨ I 5 (2*q+2) e

def Restricted13 (q i : Nat) : Prop := LuRazThreeRow.Restricted134V q i

def Fixed13 (q : Nat) (u v d l z : Prop) (e : Nat) : Prop :=
  (u∧ARow q e) ∨ (v∧LuRazClosure.BRow q e) ∨ (d∧CPrime q e) ∨
  (l∧LNew q e) ∨ (z∧LuRazThreeRow.ZPrime q e)

def Mixed13 (q a b : Nat) (u v d l z : Prop) (e : Nat) : Prop :=
  JRow a b e ∨ Fixed13 q u v d l z e

theorem a_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (4*q+2) e ↔ ARow q e := by
  rw [LuRazSixRow.unchanged_row q (4*q+2) e (by unfold LuRazSixRow.Special; omega),
    LuRazFourRow.unchanged_row q (4*q+2) e (by unfold LuRazFourRow.Special; omega)]
  exact LuRazThreeRow.a_source q e hq

theorem b_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (4*q+1) e ↔ LuRazClosure.BRow q e := by
  rw [LuRazSixRow.unchanged_row q (4*q+1) e (by unfold LuRazSixRow.Special; omega),
    LuRazFourRow.unchanged_row q (4*q+1) e (by unfold LuRazFourRow.Special; omega)]
  exact LuRazThreeRow.b_source q e hq

theorem c_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (4*q) e ↔ CPrime q e := by
  rw [LuRazSixRow.row_n q e hq]
  rfl

theorem last_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q (4*q-1) e ↔ LNew q e := by
  rw [LuRazSixRow.row_last q e hq]
  rfl

theorem z_source (q e : Nat) (hq : 4≤q) : LuRazSixRow.BRow q 2 e ↔ LuRazThreeRow.ZPrime q e := by
  rw [LuRazSixRow.unchanged_row q 2 e (by unfold LuRazSixRow.Special; omega),
    LuRazFourRow.row_two q e hq]
  unfold LuRazThreeRow.ZPrime I
  omega

theorem j_source (q t e : Nat) (hq : 4≤q) (ht : 5≤t ∧ t≤2*q+1) :
    LuRazSixRow.BRow q (JIndex t) e ↔ (e=1 ∨ e=4 ∨ I t (g q t) e) := by
  rw [LuRazSixRow.unchanged_row q (JIndex t) e
    (by unfold LuRazSixRow.Special JIndex; split <;> omega),
    LuRazFourRow.unchanged_row q (JIndex t) e
    (by unfold LuRazFourRow.Special JIndex; split <;> omega)]
  exact LuRazThreeRow.j_source_v q t e hq ht

theorem row_no2 (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h2 : ¬LuRazSixRow.BRow q i 2) : Restricted13 q i := by
  by_cases hs : LuRazSixRow.Special q i
  · rcases hs with rfl | rfl | rfl
    · exact False.elim (h2 ((LuRazSixRow.row_middle q 2 hq).mpr (by omega)))
    · unfold Restricted13 LuRazThreeRow.Restricted134V
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · unfold Restricted13 LuRazThreeRow.Restricted134V
      exact Or.inr (Or.inr (Or.inl rfl))
  rw [LuRazSixRow.unchanged_row q i 2 hs] at h2
  by_cases hs' : LuRazFourRow.Special q i
  · rcases hs' with rfl | rfl | rfl
    · exact False.elim (h2 ((LuRazFourRow.row_one q 2 hq).mpr (by omega)))
    · exact False.elim (h2 ((LuRazFourRow.row_four q 2 hq).mpr (by omega)))
    · exact False.elim (hs (Or.inr (Or.inl rfl)))
  rw [LuRazFourRow.unchanged_row q i 2 hs'] at h2
  exact LuRazThreeRow.row_no2_v q i hq hi h2

theorem restricted13_list (q : Nat) (hq : 4≤q) (l : List Nat)
    (hvalid : ∀ i∈l, Restricted13 q i) :
    ∃ u v d k1 k2 : Prop,
      (∀ e, ListUnion (LuRazSixRow.BRow q) l e ↔ Fixed13 q u v d k1 k2 e) ∨
      ∃ a b, JReachable q a b ∧
        ∀ e, ListUnion (LuRazSixRow.BRow q) l e ↔ Mixed13 q a b u v d k1 k2 e := by
  induction l with
  | nil =>
    refine ⟨False,False,False,False,False,Or.inl ?_⟩
    intro e
    simp [ListUnion,Fixed13]
  | cons i rest ih =>
    have hi := hvalid i (by simp)
    have hrest : ∀ j∈rest, Restricted13 q j := by
      intro j hj
      exact hvalid j (by simp only [List.mem_cons]; exact Or.inr hj)
    obtain ⟨u,v,d,k1,k2,hnorm⟩ := ih hrest
    unfold Restricted13 LuRazThreeRow.Restricted134V at hi
    rcases hi with hi | hi | hi | hi | hi | ⟨t,ht,hi⟩
    · subst i
      refine ⟨True,v,d,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,a_source q e hq,hn]
        unfold Fixed13
        by_cases h : ARow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,a_source q e hq,hn]
        unfold Mixed13 Fixed13
        by_cases h : ARow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,True,d,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,b_source q e hq,hn]
        unfold Fixed13
        by_cases h : BRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,b_source q e hq,hn]
        unfold Mixed13 Fixed13
        by_cases h : BRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,True,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,c_source q e hq,hn]
        unfold Fixed13
        by_cases h : CPrime q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,c_source q e hq,hn]
        unfold Mixed13 Fixed13
        by_cases h : CPrime q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,d,True,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,last_source q e hq,hn]
        unfold Fixed13
        by_cases h : LNew q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,last_source q e hq,hn]
        unfold Mixed13 Fixed13
        by_cases h : LNew q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,d,k1,True,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,z_source q e hq,hn]
        unfold Fixed13
        by_cases h : LuRazThreeRow.ZPrime q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,z_source q e hq,hn]
        unfold Mixed13 Fixed13
        by_cases h : LuRazThreeRow.ZPrime q e <;> simp [h,or_assoc]
    · subst i
      have htj := J_single_reachable q t hq ht
      refine ⟨u,v,d,k1,k2,Or.inr ?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · refine ⟨t,g q t,htj,?_⟩
        intro e
        rw [listUnion_cons,j_source q t e hq ht,hn]
        simp only [Mixed13,JRow,or_assoc]
      · refine ⟨min t a,max (g q t) b,JReachable_join q t (g q t) a b hq htj hab,?_⟩
        intro e
        rw [listUnion_cons,j_source q t e hq ht,hn]
        change (JRow t (g q t) e ∨ (JRow a b e ∨ Fixed13 q u v d k1 k2 e)) ↔ _
        exact or_assoc.symm.trans (or_congr (JRow_join q t (g q t) a b e hq htj hab) Iff.rfl)


theorem core13_parts (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core134 R) :
    ∃ a b, JReachable q a b ∧ ∃ u v d l z : Prop, (d∨l∨z) ∧
      ∀ e, R e ↔ Mixed13 q a b u v d l z e := by
  obtain ⟨ls,_,hv,hR⟩ := hg
  have hr : ∀ i∈ls, Restricted13 q i := by
    intro i hi
    exact row_no2 q i hq (hv i hi) (fun h => hc.2.1 ((hR 2).mp ⟨i,hi,h⟩))
  obtain ⟨u,v,d,l,z,hn⟩ := restricted13_list q hq ls hr
  rcases hn with hn | ⟨a,b,hab,hn⟩
  · have h4 := (hn 4).mp ((hR 4).mpr hc.2.2.2)
    unfold Fixed13 ARow LuRazClosure.BRow CPrime LNew LuRazThreeRow.ZPrime I at h4
    omega
  · have h3 := (hn 3).mp ((hR 3).mpr hc.2.2.1)
    have hguard : d∨l∨z := by
      rcases h3 with h | ⟨_,h⟩ | ⟨_,h⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩
      · unfold JRow I at h
        have ha := hab.1
        omega
      · unfold ARow I at h; omega
      · unfold LuRazClosure.BRow I at h; omega
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact ⟨a,b,hab,u,v,d,l,z,hguard,fun e => (hR e).symm.trans (hn e)⟩

end LuRazSixRowClosure
