import Exhaustive123Count
namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def Restricted134V (q i : Nat) : Prop :=
  i=4*q+2 ∨ i=4*q+1 ∨ i=4*q ∨ i=4*q-1 ∨ i=2 ∨
    ∃ a, (5≤a ∧ a≤2*q+1) ∧ i=JIndex a
def Fixed134V (q : Nat) (u v d k1 k2 : Prop) (e : Nat) : Prop :=
  (u∧ARow q e) ∨ (v∧BRow q e) ∨ (d∧CRow q e) ∨ (k1∧LPrime q e) ∨ (k2∧ZPrime q e)
def Mixed134V (q a b : Nat) (u v d k1 k2 : Prop) (e : Nat) : Prop :=
  JRow a b e ∨ Fixed134V q u v d k1 k2 e

theorem j_source_v (q t e : Nat) (hq : 4≤q) (ht : 5≤t ∧ t≤2*q+1) :
    VRow q (JIndex t) e ↔ (e=1 ∨ e=4 ∨ I t (g q t) e) := by
  rw [unchanged_row q (JIndex t) e (by unfold Special JIndex; split <;> omega)]
  exact J_is_source_row q t e hq ht

theorem row_no2_v (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2) (h2 : ¬VRow q i 2) : Restricted134V q i := by
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact False.elim (h2 ((row_four q 2 hq).mpr (by omega)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have ho : ¬Row q i 2 := by rwa [unchanged_row q i 2 hs] at h2
  rcases row_excluding_two q i hq hi ho with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact False.elim (hs (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem restricted134V_list (q : Nat) (hq : 4≤q) (l : List Nat)
    (hvalid : ∀ i∈l, Restricted134V q i) :
    ∃ u v d k1 k2 : Prop,
      (∀ e, ListUnion (VRow q) l e ↔ Fixed134V q u v d k1 k2 e) ∨
      ∃ a b, JReachable q a b ∧
        ∀ e, ListUnion (VRow q) l e ↔ Mixed134V q a b u v d k1 k2 e := by
  induction l with
  | nil =>
    refine ⟨False,False,False,False,False,Or.inl ?_⟩
    intro e
    simp [ListUnion,Fixed134V]
  | cons i rest ih =>
    have hi := hvalid i (by simp)
    have hrest : ∀ j∈rest, Restricted134V q j := by
      intro j hj
      exact hvalid j (by simp only [List.mem_cons]; exact Or.inr hj)
    obtain ⟨u,v,d,k1,k2,hnorm⟩ := ih hrest
    rcases hi with hi | hi | hi | hi | hi | ⟨t,ht,hi⟩
    · subst i
      refine ⟨True,v,d,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,a_source q e hq,hn]
        unfold Fixed134V
        by_cases h : ARow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,a_source q e hq,hn]
        unfold Mixed134V Fixed134V
        by_cases h : ARow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,True,d,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,b_source q e hq,hn]
        unfold Fixed134V
        by_cases h : BRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,b_source q e hq,hn]
        unfold Mixed134V Fixed134V
        by_cases h : BRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,True,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,c_source q e hq,hn]
        unfold Fixed134V
        by_cases h : CRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,c_source q e hq,hn]
        unfold Mixed134V Fixed134V
        by_cases h : CRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,d,True,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,last_source q e hq,hn]
        unfold Fixed134V
        by_cases h : LPrime q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,last_source q e hq,hn]
        unfold Mixed134V Fixed134V
        by_cases h : LPrime q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,d,k1,True,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,z_source q e hq,hn]
        unfold Fixed134V
        by_cases h : ZPrime q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,z_source q e hq,hn]
        unfold Mixed134V Fixed134V
        by_cases h : ZPrime q e <;> simp [h,or_assoc]
    · subst i
      have htj := J_single_reachable q t hq ht
      refine ⟨u,v,d,k1,k2,Or.inr ?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · refine ⟨t,g q t,htj,?_⟩
        intro e
        rw [listUnion_cons,j_source_v q t e hq ht,hn]
        simp only [Mixed134V,JRow,or_assoc]
      · refine ⟨min t a,max (g q t) b,JReachable_join q t (g q t) a b hq htj hab,?_⟩
        intro e
        rw [listUnion_cons,j_source_v q t e hq ht,hn]
        change (JRow t (g q t) e ∨ (JRow a b e ∨ Fixed134V q u v d k1 k2 e)) ↔ _
        exact or_assoc.symm.trans (or_congr (JRow_join q t (g q t) a b e hq htj hab) Iff.rfl)


theorem core134_v_parts (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core134 R) :
    (∃ u v d k2 : Prop, (u∨k2) ∧ ∀ e, R e ↔ Fixed134V q u v d True k2 e) ∨
    ∃ a b, JReachable q a b ∧ ∃ u v d k1 k2 : Prop, (d∨k1∨k2) ∧
      ∀ e, R e ↔ Mixed134V q a b u v d k1 k2 e := by
  obtain ⟨l,_,hv,hR⟩ := hg
  have hr : ∀ i∈l, Restricted134V q i := by
    intro i hi
    exact row_no2_v q i hq (hv i hi) (fun h => hc.2.1 ((hR 2).mp ⟨i,hi,h⟩))
  obtain ⟨u,v,d,k1,k2,hn⟩ := restricted134V_list q hq l hr
  rcases hn with hn | ⟨a,b,hab,hn⟩
  · have h4 := (hn 4).mp ((hR 4).mpr hc.2.2.2)
    have hk : k1 := by
      rcases h4 with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨h,_⟩ | ⟨_,h⟩
      · unfold ARow I at h; omega
      · unfold BRow I at h; omega
      · unfold CRow I at h; omega
      · exact h
      · unfold ZPrime I at h; omega
    have h1 := (hn 1).mp ((hR 1).mpr hc.1)
    have hA : u∨k2 := by
      rcases h1 with ⟨h,_⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨h,_⟩
      · exact Or.inl h
      · unfold BRow I at h; omega
      · unfold CRow I at h; omega
      · unfold LPrime I at h; omega
      · exact Or.inr h
    exact Or.inl ⟨u,v,d,k2,hA,fun e => (hR e).symm.trans ((hn e).trans (by simp only [hk]))⟩
  · have h3 := (hn 3).mp ((hR 3).mpr hc.2.2.1)
    have hguard : d∨k1∨k2 := by
      rcases h3 with h | ⟨_,h⟩ | ⟨_,h⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩
      · unfold JRow I at h; have ha := hab.1; omega
      · unfold ARow I at h; omega
      · unfold BRow I at h; omega
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact Or.inr ⟨a,b,hab,u,v,d,k1,k2,hguard,fun e => (hR e).symm.trans (hn e)⟩

end LuRazThreeRow
