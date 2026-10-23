import LuRazCore234Results
import LuRazSmallResults
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def Core123 (R : Nat → Prop) : Prop := R 1 ∧ R 2 ∧ R 3 ∧ ¬R 4
def Restricted123 (q i : Nat) : Prop :=
  i=4*q ∨ i=1 ∨ i=4*q+1 ∨ i=4*q+2 ∨ i=4 ∨
    ∃ p, P q p ∧ i=LIndex q p
def Fixed123 (q : Nat) (u v w a f : Prop) (e : Nat) : Prop :=
  (u ∧ CRow q e) ∨ (v ∧ DRow q e) ∨ (w ∧ BRow q e) ∨ (a ∧ ARow q e) ∨ (f ∧ ERow q e)
def Mixed123 (q t p : Nat) (u v w a f : Prop) (e : Nat) : Prop :=
  LRow q t p e ∨ Fixed123 q u v w a f e

theorem row_excluding_four (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h4 : ¬LuRazParametric.Row q i 4) : Restricted123 q i := by
  have hl : ∀ j, (2*q+3≤j ∧ j+1≤4*q) → ∃ p, P q p ∧ j=LIndex q p := by
    intro j hj
    obtain ⟨p,hp,heq⟩ := beta_surjective q (j+1) hq (by omega)
    refine ⟨p,hp,?_⟩
    unfold LIndex
    omega
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
      (5≤i ∧ i≤q+2) ∨ (q+3≤i ∧ i≤2*q) ∨ i=2*q+1 ∨ i=2*q+2 ∨ i=2*q+3 ∨
      (2*q+4≤i ∧ i≤3*q) ∨ i=3*q+1 ∨ (3*q+2≤i ∧ i+1≤4*q) ∨
      i=4*q ∨ i=4*q+1 ∨ i=4*q+2 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact False.elim (h4 ((LuRazParametric.row_case_0 q i 4 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inl h)
  · exact False.elim (h4 ((LuRazParametric.row_case_2 q i 4 (by omega) h).mpr (by omega)))
  · exact False.elim (h4 ((LuRazParametric.row_case_3 q i 4 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact False.elim (h4 ((LuRazParametric.row_case_5 q i 4 (by omega) h).mpr (by omega)))
  · exact False.elim (h4 ((LuRazParametric.row_case_6 q i 4 (by omega) h).mpr (by omega)))
  · exact False.elim (h4 ((LuRazParametric.row_case_7 q i 4 (by omega) h).mpr (by omega)))
  · exact False.elim (h4 ((LuRazParametric.row_case_8 q i 4 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hl i (by omega))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hl i (by omega))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hl i (by omega))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hl i (by omega))))))
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem restricted123_list (q : Nat) (hq : 4≤q) (l : List Nat)
    (hvalid : ∀ i∈l, Restricted123 q i) :
    ∃ u v w a f : Prop,
      (∀ e, ListUnion (LuRazParametric.Row q) l e ↔ Fixed123 q u v w a f e) ∨
      ∃ t p, P q t ∧ P q p ∧ t≤p ∧
        ∀ e, ListUnion (LuRazParametric.Row q) l e ↔ Mixed123 q t p u v w a f e := by
  induction l with
  | nil =>
    refine ⟨False,False,False,False,False,Or.inl ?_⟩
    intro e
    simp [ListUnion,Fixed123]
  | cons i rest ih =>
    have hi := hvalid i (by simp)
    have hrest : ∀ j∈rest, Restricted123 q j := by
      intro j hj
      exact hvalid j (by simp only [List.mem_cons]; exact Or.inr hj)
    obtain ⟨u,v,w,a,f,hnorm⟩ := ih hrest
    rcases hi with hi | hi | hi | hi | hi | ⟨s,hs,hi⟩
    · subst i
      refine ⟨True,v,w,a,f,?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · left
        intro e
        rw [listUnion_cons,C_source q e hq,hn]
        unfold Fixed123
        by_cases h : CRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨t,p,ht,hp,htp,?_⟩
        intro e
        rw [listUnion_cons,C_source q e hq,hn]
        unfold Mixed123 Fixed123
        by_cases h : CRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,True,w,a,f,?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · left
        intro e
        rw [listUnion_cons,D_source q e hq,hn]
        unfold Fixed123
        by_cases h : DRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨t,p,ht,hp,htp,?_⟩
        intro e
        rw [listUnion_cons,D_source q e hq,hn]
        unfold Mixed123 Fixed123
        by_cases h : DRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,True,a,f,?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · left
        intro e
        rw [listUnion_cons,B_source q e hq,hn]
        unfold Fixed123
        by_cases h : BRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨t,p,ht,hp,htp,?_⟩
        intro e
        rw [listUnion_cons,B_source q e hq,hn]
        unfold Mixed123 Fixed123
        by_cases h : BRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,w,True,f,?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · left
        intro e
        rw [listUnion_cons,A_source q e hq,hn]
        unfold Fixed123
        by_cases h : ARow q e <;> simp [h,or_assoc]
      · right
        refine ⟨t,p,ht,hp,htp,?_⟩
        intro e
        rw [listUnion_cons,A_source q e hq,hn]
        unfold Mixed123 Fixed123
        by_cases h : ARow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,w,a,True,?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · left
        intro e
        rw [listUnion_cons,E_source q e hq,hn]
        unfold Fixed123
        by_cases h : ERow q e <;> simp [h,or_assoc]
      · right
        refine ⟨t,p,ht,hp,htp,?_⟩
        intro e
        rw [listUnion_cons,E_source q e hq,hn]
        unfold Mixed123 Fixed123
        by_cases h : ERow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,w,a,f,Or.inr ?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · refine ⟨s,s,hs,hs,by omega,?_⟩
        intro e
        rw [listUnion_cons,LRow_source q s e hq hs,hn]
        rfl
      · refine ⟨min s t,max s p,P_min q s t hs ht,P_max q s p hs hp,by omega,?_⟩
        intro e
        rw [listUnion_cons,LRow_source q s e hq hs,hn]
        change (LRow q s s e ∨ (LRow q t p e ∨ Fixed123 q u v w a f e)) ↔ _
        exact or_assoc.symm.trans (or_congr (LRow_join q s s t p e hq hs hs ht hp (by omega) htp) Iff.rfl)


def Image123 (q : Nat) (z : NF23) (a f : Prop) (e : Nat) : Prop :=
  z.eval q e ∨ (a ∧ ARow q e) ∨ (f ∧ ERow q e)

theorem core123_image (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core123 R) :
    ∃ z : NF23, z.Valid q ∧ ∃ a f : Prop, (a∨f) ∧ ∀ e, R e ↔ Image123 q z a f e := by
  obtain ⟨l,_,hvalid,hR⟩ := hg
  have hi : ∀ i∈l, Restricted123 q i := by
    intro i him
    apply row_excluding_four q i hq (hvalid i him)
    intro h
    exact hc.2.2.2 ((hR 4).mp ⟨i,him,h⟩)
  obtain ⟨u,v,w,a,f,hnorm⟩ := restricted123_list q hq l hi
  rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
  · have h1 := (hn 1).mp ((hR 1).mpr hc.1)
    have h2 := (hn 2).mp ((hR 2).mpr hc.2.1)
    have h3 := (hn 3).mp ((hR 3).mpr hc.2.2.1)
    have hA : a∨f := by
      rcases h1 with h | h | h | h | h
      · have hh := h.2; unfold CRow I at hh; omega
      · have hh := h.2; unfold DRow I at hh; omega
      · have hh := h.2; unfold BRow I at hh; omega
      · exact Or.inl h.1
      · exact Or.inr h.1
    have hv : v := by
      rcases h2 with h | h | h | h | h
      · have hh := h.2; unfold CRow I at hh; omega
      · exact h.1
      · have hh := h.2; unfold BRow I at hh; omega
      · have hh := h.2; unfold ARow I at hh; omega
      · have hh := h.2; unfold ERow I at hh; omega
    classical
    by_cases hu : u
    · refine ⟨.full,True.intro,a,f,hA,?_⟩
      intro e
      rw [←hR e,hn]
      simp only [Fixed123,Image123,NF23.eval,hu,hv,true_and,CRow,DRow,BRow,I]
      by_cases ha : a <;> by_cases hf : f <;> simp only [ha,hf,true_and,false_and,false_or,or_false,ARow,ERow,I] at hA ⊢ <;> omega
    · have hf : f := by
        rcases h3 with h | h | h | h | h
        · exact False.elim (hu h.1)
        · have hh := h.2; unfold DRow I at hh; omega
        · have hh := h.2; unfold BRow I at hh; omega
        · have hh := h.2; unfold ARow I at hh; omega
        · exact h.1
      have hp4 : P q 4 := by unfold P; omega
      refine ⟨.dgap 4,⟨hp4,by omega⟩,a,f,hA,?_⟩
      intro e
      rw [←hR e,hn]
      simp only [Fixed123,Image123,NF23.eval,hu,hv,hf,true_and,false_and,false_or,CRow,DRow,BRow,ARow,ERow,I]
      by_cases ha : a <;> simp only [ha,true_and,false_and,false_or,or_false] <;> omega
  · have h1 := (hn 1).mp ((hR 1).mpr hc.1)
    have ht' := ht
    have hp' := hp
    unfold P at ht' hp'
    have hbt := beta_bounds q t hq ht
    have hA : a∨f := by
      rcases h1 with h | h | h | h | h | h
      · unfold LRow LNormal I at h; omega
      · have hh := h.2; unfold CRow I at hh; omega
      · have hh := h.2; unfold DRow I at hh; omega
      · have hh := h.2; unfold BRow I at hh; omega
      · exact Or.inl h.1
      · exact Or.inr h.1
    obtain ⟨z,hz,he⟩ := mixed23_normal q t p hq ht hp htp u v w
    refine ⟨z,hz,a,f,hA,?_⟩
    intro e
    have hm : Mixed123 q t p u v w a f e ↔ Mixed23 q t p u v w e ∨ (a∧ARow q e) ∨ (f∧ERow q e) := by
      simp only [Mixed123,Fixed123,Mixed23,or_assoc]
    exact (hR e).symm.trans ((hn e).trans (hm.trans (or_congr (he e) Iff.rfl)))

theorem image123_generated (q : Nat) (hq : 4≤q) (z : NF23) (hz : z.Valid q) (a f : Prop) :
    Generated q (Image123 q z a f) := by
  have hg := generated_optional q (generated_optional q (NF23.generated q hq z hz) (generated_A q hq) a) (generated_E q hq) f
  apply generated_congr q hg
  intro e
  simp only [Image123,or_assoc]
end LuRazClosure
