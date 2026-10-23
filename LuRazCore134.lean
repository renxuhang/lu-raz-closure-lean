import LuRazCore123Results
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def ZRow (q e : Nat) : Prop := e=1 ∨ e=3 ∨ e=4 ∨ I 5 (2*q) e ∨ e=4*q

theorem Z_source (q e : Nat) (hq : 4≤q) : LuRazParametric.Row q 2 e ↔ ZRow q e := by
  rw [LuRazParametric.row_case_2 q 2 e (by omega) rfl]
  unfold ZRow I
  omega

theorem generated_Z (q : Nat) (hq : 4≤q) : Generated q (ZRow q) :=
  generated_congr q (generated_row q 2 (by omega)) (fun e => Z_source q e hq)

def Core134 (R : Nat → Prop) : Prop := R 1 ∧ ¬R 2 ∧ R 3 ∧ R 4
def Restricted134 (q i : Nat) : Prop :=
  i=4*q+2 ∨ i=4*q+1 ∨ i=4*q ∨ i=4 ∨ i=2 ∨
    ∃ a, (5≤a ∧ a≤2*q+1) ∧ i=JIndex a
def Fixed134 (q : Nat) (u v d k1 k2 : Prop) (e : Nat) : Prop :=
  (u ∧ ARow q e) ∨ (v ∧ BRow q e) ∨ (d ∧ CRow q e) ∨ (k1 ∧ ERow q e) ∨ (k2 ∧ ZRow q e)
def Mixed134 (q a b : Nat) (u v d k1 k2 : Prop) (e : Nat) : Prop :=
  JRow a b e ∨ Fixed134 q u v d k1 k2 e

theorem row_excluding_two (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h2 : ¬LuRazParametric.Row q i 2) : Restricted134 q i := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
      (5≤i ∧ i≤q+2) ∨ (q+3≤i ∧ i≤2*q) ∨ i=2*q+1 ∨ i=2*q+2 ∨ i=2*q+3 ∨
      (2*q+4≤i ∧ i≤3*q) ∨ i=3*q+1 ∨ (3*q+2≤i ∧ i+1≤4*q) ∨
      i=4*q ∨ i=4*q+1 ∨ i=4*q+2 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact False.elim (h2 ((LuRazParametric.row_case_0 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((LuRazParametric.row_case_1 q i 2 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨5,by omega,h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨i+1,by omega,?_⟩)))))
    unfold JIndex
    split <;> omega
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨i+1,by omega,?_⟩)))))
    unfold JIndex
    split <;> omega
  · exact False.elim (h2 ((LuRazParametric.row_case_7 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((LuRazParametric.row_case_8 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((LuRazParametric.row_case_9 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((LuRazParametric.row_case_10 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((LuRazParametric.row_case_11 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (h2 ((LuRazParametric.row_case_12 q i 2 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inl h

theorem restricted134_list (q : Nat) (hq : 4≤q) (l : List Nat)
    (hvalid : ∀ i∈l, Restricted134 q i) :
    ∃ u v d k1 k2 : Prop,
      (∀ e, ListUnion (LuRazParametric.Row q) l e ↔ Fixed134 q u v d k1 k2 e) ∨
      ∃ a b, JReachable q a b ∧
        ∀ e, ListUnion (LuRazParametric.Row q) l e ↔ Mixed134 q a b u v d k1 k2 e := by
  induction l with
  | nil =>
    refine ⟨False,False,False,False,False,Or.inl ?_⟩
    intro e
    simp [ListUnion,Fixed134]
  | cons i rest ih =>
    have hi := hvalid i (by simp)
    have hrest : ∀ j∈rest, Restricted134 q j := by
      intro j hj
      exact hvalid j (by simp only [List.mem_cons]; exact Or.inr hj)
    obtain ⟨u,v,d,k1,k2,hnorm⟩ := ih hrest
    rcases hi with hi | hi | hi | hi | hi | ⟨t,ht,hi⟩
    · subst i
      refine ⟨True,v,d,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,A_source q e hq,hn]
        unfold Fixed134
        by_cases h : ARow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,A_source q e hq,hn]
        unfold Mixed134 Fixed134
        by_cases h : ARow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,True,d,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,B_source q e hq,hn]
        unfold Fixed134
        by_cases h : BRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,B_source q e hq,hn]
        unfold Mixed134 Fixed134
        by_cases h : BRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,True,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,C_source q e hq,hn]
        unfold Fixed134
        by_cases h : CRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,C_source q e hq,hn]
        unfold Mixed134 Fixed134
        by_cases h : CRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,d,True,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,E_source q e hq,hn]
        unfold Fixed134
        by_cases h : ERow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,E_source q e hq,hn]
        unfold Mixed134 Fixed134
        by_cases h : ERow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,d,k1,True,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,Z_source q e hq,hn]
        unfold Fixed134
        by_cases h : ZRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,Z_source q e hq,hn]
        unfold Mixed134 Fixed134
        by_cases h : ZRow q e <;> simp [h,or_assoc]
    · subst i
      have htj := J_single_reachable q t hq ht
      refine ⟨u,v,d,k1,k2,Or.inr ?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · refine ⟨t,g q t,htj,?_⟩
        intro e
        rw [listUnion_cons,J_is_source_row q t e hq ht,hn]
        simp only [Mixed134,JRow,or_assoc]
      · refine ⟨min t a,max (g q t) b,JReachable_join q t (g q t) a b hq htj hab,?_⟩
        intro e
        rw [listUnion_cons,J_is_source_row q t e hq ht,hn]
        change (JRow t (g q t) e ∨ (JRow a b e ∨ Fixed134 q u v d k1 k2 e)) ↔ _
        exact or_assoc.symm.trans (or_congr (JRow_join q t (g q t) a b e hq htj hab) Iff.rfl)


theorem core134_parts (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core134 R) :
    (∃ u v d k1 : Prop, ∀ e, R e ↔ Fixed134 q u v d k1 True e) ∨
    ∃ a b, JReachable q a b ∧ ∃ u v d k1 k2 : Prop, (d∨k1∨k2) ∧
      ∀ e, R e ↔ Mixed134 q a b u v d k1 k2 e := by
  obtain ⟨l,_,hvalid,hR⟩ := hg
  have hi : ∀ i∈l, Restricted134 q i := by
    intro i him
    apply row_excluding_two q i hq (hvalid i him)
    intro h
    exact hc.2.1 ((hR 2).mp ⟨i,him,h⟩)
  obtain ⟨u,v,d,k1,k2,hnorm⟩ := restricted134_list q hq l hi
  rcases hnorm with hn | ⟨a,b,hab,hn⟩
  · have h4 := (hn 4).mp ((hR 4).mpr hc.2.2.2)
    have hk2 : k2 := by
      rcases h4 with h | h | h | h | h
      · have hh := h.2; unfold ARow I at hh; omega
      · have hh := h.2; unfold BRow I at hh; omega
      · have hh := h.2; unfold CRow I at hh; omega
      · have hh := h.2; unfold ERow I at hh; omega
      · exact h.1
    exact Or.inl ⟨u,v,d,k1,fun e => (hR e).symm.trans ((hn e).trans (by simp only [hk2]))⟩
  · have h3 := (hn 3).mp ((hR 3).mpr hc.2.2.1)
    have hguard : d∨k1∨k2 := by
      rcases h3 with h | h | h | h | h | h
      · have hh := h; unfold JRow I at hh; have ha := hab.1; omega
      · have hh := h.2; unfold ARow I at hh; omega
      · have hh := h.2; unfold BRow I at hh; omega
      · exact Or.inl h.1
      · exact Or.inr (Or.inl h.1)
      · exact Or.inr (Or.inr h.1)
    exact Or.inr ⟨a,b,hab,u,v,d,k1,k2,hguard,fun e => (hR e).symm.trans (hn e)⟩
end LuRazClosure
