import SixRowCore14Exact
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

def Restricted11 (q i : Nat) : Prop := Restricted124 q i

def Fixed11 (q : Nat) (u v d k1 k2 : Prop) (e : Nat) : Prop :=
  (u∧ARow q e) ∨ (v∧LuRazClosure.BRow q e) ∨ (d∧DPrime14 q e) ∨
  (k1∧K1Row q e) ∨ (k2∧KPrime14 q e)

def Mixed11 (q a b : Nat) (u v d k1 k2 : Prop) (e : Nat) : Prop :=
  JRow a b e ∨ Fixed11 q u v d k1 k2 e

theorem row_no3_11 (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h3 : ¬LuRazSixRow.BRow q i 3) : Restricted11 q i := by
  by_cases h1 : i=1
  · unfold Restricted11 Restricted124; omega
  by_cases h2 : i=2
  · subst i; exact False.elim (h3 ((z_source q 3 hq).mpr (by unfold LuRazThreeRow.ZPrime I; omega)))
  by_cases h4 : i=4
  · subst i; exact False.elim (h3 ((e_source14 q 3 hq).mpr (by unfold E14 I; omega)))
  by_cases hm : i=2*q+2
  · unfold Restricted11 Restricted124; omega
  by_cases hl : i=4*q-1
  · subst i; exact False.elim (h3 ((last_source q 3 hq).mpr (by unfold LNew I; omega)))
  by_cases hn : i=4*q
  · subst i; exact False.elim (h3 ((c_source q 3 hq).mpr (by unfold CPrime I; omega)))
  have hix := original_row14 q i 3 ⟨h1,h2,h4,hm,hl,hn⟩
  exact row_excluding_three q i hq hi (fun h => h3 (hix.mpr h))

theorem restricted11_list (q : Nat) (hq : 4≤q) (l : List Nat)
    (hvalid : ∀ i∈l, Restricted11 q i) :
    ∃ u v d k1 k2 : Prop,
      (∀ e, ListUnion (LuRazSixRow.BRow q) l e ↔ Fixed11 q u v d k1 k2 e) ∨
      ∃ a b, JReachable q a b ∧
        ∀ e, ListUnion (LuRazSixRow.BRow q) l e ↔ Mixed11 q a b u v d k1 k2 e := by
  induction l with
  | nil =>
    refine ⟨False,False,False,False,False,Or.inl ?_⟩
    intro e
    simp [ListUnion,Fixed11]
  | cons i rest ih =>
    have hi := hvalid i (by simp)
    have hrest : ∀ j∈rest, Restricted11 q j := by
      intro j hj
      exact hvalid j (by simp only [List.mem_cons]; exact Or.inr hj)
    obtain ⟨u,v,d,k1,k2,hnorm⟩ := ih hrest
    unfold Restricted11 Restricted124 at hi
    rcases hi with hi | hi | hi | hi | hi | ⟨t,ht,hi⟩
    · subst i
      refine ⟨True,v,d,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,a_source q e hq,hn]
        unfold Fixed11
        by_cases h : ARow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,a_source q e hq,hn]
        unfold Mixed11 Fixed11
        by_cases h : ARow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,True,d,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,b_source q e hq,hn]
        unfold Fixed11
        by_cases h : BRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,b_source q e hq,hn]
        unfold Mixed11 Fixed11
        by_cases h : BRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,True,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,d_source14 q e hq,hn]
        unfold Fixed11
        by_cases h : DPrime14 q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,d_source14 q e hq,hn]
        unfold Mixed11 Fixed11
        by_cases h : DPrime14 q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,d,True,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,k1_source14 q e hq,hn]
        unfold Fixed11
        by_cases h : K1Row q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,k1_source14 q e hq,hn]
        unfold Mixed11 Fixed11
        by_cases h : K1Row q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,d,k1,True,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,k2_source14 q e hq,hn]
        unfold Fixed11
        by_cases h : KPrime14 q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,k2_source14 q e hq,hn]
        unfold Mixed11 Fixed11
        by_cases h : KPrime14 q e <;> simp [h,or_assoc]
    · subst i
      have htj := J_single_reachable q t hq ht
      refine ⟨u,v,d,k1,k2,Or.inr ?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · refine ⟨t,g q t,htj,?_⟩
        intro e
        rw [listUnion_cons,j_source q t e hq ht,hn]
        simp only [Mixed11,JRow,or_assoc]
      · refine ⟨min t a,max (g q t) b,JReachable_join q t (g q t) a b hq htj hab,?_⟩
        intro e
        rw [listUnion_cons,j_source q t e hq ht,hn]
        change (JRow t (g q t) e ∨ (JRow a b e ∨ Fixed11 q u v d k1 k2 e)) ↔ _
        exact or_assoc.symm.trans (or_congr (JRow_join q t (g q t) a b e hq htj hab) Iff.rfl)

theorem core11_parts (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core124 R) :
    (∃ v d k1 k2 : Prop,(d∨k1∨k2) ∧ ∀ e,R e ↔ Fixed11 q True v d k1 k2 e) ∨
    ∃ a b,JReachable q a b ∧ ∃ u v d k1 k2 : Prop,(d∨k1∨k2) ∧
      ∀ e,R e ↔ Mixed11 q a b u v d k1 k2 e := by
  obtain ⟨l,_,hv,hR⟩ := hg
  have hr : ∀ i∈l,Restricted11 q i := by
    intro i hi
    exact row_no3_11 q i hq (hv i hi) (fun h => hc.2.2.1 ((hR 3).mp ⟨i,hi,h⟩))
  obtain ⟨u,v,d,k1,k2,hn⟩ := restricted11_list q hq l hr
  rcases hn with hn | ⟨a,b,hab,hn⟩
  · have hu : u := by
      have h1 := (hn 1).mp ((hR 1).mpr hc.1)
      rcases h1 with ⟨h,_⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
      · exact h
      all_goals simp only [LuRazClosure.BRow,DPrime14,K1Row,KPrime14,I] at h <;> omega
    have hguard : d∨k1∨k2 := by
      have h2 := (hn 2).mp ((hR 2).mpr hc.2.1)
      rcases h2 with ⟨_,h⟩ | ⟨_,h⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩
      · unfold ARow I at h; omega
      · unfold LuRazClosure.BRow I at h; omega
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact Or.inl ⟨v,d,k1,k2,hguard,fun e => (hR e).symm.trans ((hn e).trans (by simp only [hu]))⟩
  · have hguard : d∨k1∨k2 := by
      have h2 := (hn 2).mp ((hR 2).mpr hc.2.1)
      have ha := hab.1
      rcases h2 with h | ⟨_,h⟩ | ⟨_,h⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩
      · unfold JRow I at h; omega
      · unfold ARow I at h; omega
      · unfold LuRazClosure.BRow I at h; omega
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact Or.inr ⟨a,b,hab,u,v,d,k1,k2,hguard,fun e => (hR e).symm.trans (hn e)⟩

end LuRazSixRowClosure
