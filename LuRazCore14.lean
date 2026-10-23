import LuRazGenerated

/-! Core {1,4}, signature 9: semantics in the complete source-family closure. -/
namespace LuRazClosure

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def Core14 (R : Nat → Prop) : Prop := R 1 ∧ ¬R 2 ∧ ¬R 3 ∧ R 4
def Mixed14 (q a b : Nat) (u v : Prop) (e : Nat) : Prop :=
  JRow a b e ∨ (u ∧ ARow q e) ∨ (v ∧ BRow q e)

theorem JRow_join (q a b c d e : Nat) (hq : 4 ≤ q)
    (hab : JReachable q a b) (hcd : JReachable q c d) :
    (JRow a b e ∨ JRow c d e) ↔ JRow (min a c) (max b d) e := by
  by_cases h1 : e=1
  · simp [JRow,h1]
  by_cases h4 : e=4
  · simp [JRow,h4]
  simpa only [JRow,h1,h4,false_or] using J_join_closed q a b c d e hq hab hcd

def Restricted14 (q i : Nat) : Prop :=
  i=4*q+2 ∨ i=4*q+1 ∨ ∃ a, (5 ≤ a ∧ a ≤ 2*q+1) ∧ i=JIndex a

theorem restricted14_list (q : Nat) (hq : 4 ≤ q) (l : List Nat)
    (hvalid : ∀ i ∈ l, Restricted14 q i) :
    ∃ u v : Prop,
      (∀ e, ListUnion (LuRazParametric.Row q) l e ↔
        (u ∧ ARow q e) ∨ (v ∧ BRow q e)) ∨
      ∃ a b, JReachable q a b ∧
        ∀ e, ListUnion (LuRazParametric.Row q) l e ↔ Mixed14 q a b u v e := by
  induction l with
  | nil =>
    refine ⟨False,False,Or.inl ?_⟩
    intro e
    simp [ListUnion]
  | cons i rest ih =>
    have hi := hvalid i (by simp)
    have hrest : ∀ j ∈ rest, Restricted14 q j := by
      intro j hj
      exact hvalid j (by simp only [List.mem_cons]; exact Or.inr hj)
    obtain ⟨u,v,hnorm⟩ := ih hrest
    rcases hi with hi | hi | ⟨t,ht,hi⟩
    · subst i
      refine ⟨True,v,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,A_source q e hq,hn]
        by_cases h : ARow q e <;> simp [h]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,A_source q e hq,hn]
        unfold Mixed14
        by_cases h : ARow q e <;> simp [h]
    · subst i
      refine ⟨u,True,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,B_source q e hq,hn]
        by_cases h : BRow q e <;> simp [h]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,B_source q e hq,hn]
        unfold Mixed14
        by_cases h : BRow q e <;> simp [h]
    · subst i
      have htj := J_single_reachable q t hq ht
      refine ⟨u,v,Or.inr ?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · refine ⟨t,g q t,htj,?_⟩
        intro e
        rw [listUnion_cons,J_is_source_row q t e hq ht,hn]
        simp only [Mixed14,JRow,or_assoc]
      · refine ⟨min t a,max (g q t) b,JReachable_join q t (g q t) a b hq htj hab,?_⟩
        intro e
        rw [listUnion_cons,J_is_source_row q t e hq ht,hn]
        change (JRow t (g q t) e ∨ (JRow a b e ∨ (u ∧ ARow q e) ∨ (v ∧ BRow q e))) ↔ _
        exact or_assoc.symm.trans (or_congr (JRow_join q t (g q t) a b e hq htj hab) Iff.rfl)

theorem full_core14_mixed (q : Nat) (hq : 4 ≤ q) (R : Nat → Prop)
    (hgen : Generated q R) (hcore : Core14 R) :
    ∃ a b, JReachable q a b ∧ ∃ u v : Prop,
      ∀ e, R e ↔ Mixed14 q a b u v e := by
  obtain ⟨l,_,hvalid,hR⟩ := hgen
  have hr : ∀ i ∈ l, Restricted14 q i := by
    intro i hi
    apply row_excluding_two_three q i hq (hvalid i hi)
    · intro h
      exact hcore.2.1 ((hR 2).mp ⟨i,hi,h⟩)
    · intro h
      exact hcore.2.2.1 ((hR 3).mp ⟨i,hi,h⟩)
  obtain ⟨u,v,hnorm⟩ := restricted14_list q hq l hr
  rcases hnorm with hn | ⟨a,b,hab,hn⟩
  · have h4 := (hn 4).mp ((hR 4).mpr hcore.2.2.2)
    unfold ARow BRow I at h4
    omega
  · exact ⟨a,b,hab,u,v,fun e => (hR e).symm.trans (hn e)⟩

theorem mixed14_generated (q a b : Nat) (hq : 4 ≤ q)
    (hab : JReachable q a b) (u v : Prop) : Generated q (Mixed14 q a b u v) := by
  classical
  have hj := generated_J q a b hq hab
  by_cases hu : u <;> by_cases hv : v
  · apply generated_congr q (generated_join q hj (generated_join q (generated_A q hq) (generated_B q hq)))
    intro e
    simp only [Mixed14,hu,hv,true_and]
  · apply generated_congr q (generated_join q hj (generated_A q hq))
    intro e
    simp only [Mixed14,hu,hv,true_and,false_and,or_false]
  · apply generated_congr q (generated_join q hj (generated_B q hq))
    intro e
    simp only [Mixed14,hu,hv,true_and,false_and,false_or]
  · apply generated_congr q hj
    intro e
    simp only [Mixed14,hu,hv,false_and,or_false]

theorem mixed14_core (q a b : Nat) (hq : 4 ≤ q)
    (hab : JReachable q a b) (u v : Prop) : Core14 (Mixed14 q a b u v) := by
  unfold JReachable at hab
  unfold Core14 Mixed14 JRow ARow BRow I
  omega

end LuRazClosure
