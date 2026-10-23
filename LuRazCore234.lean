import LuRazCore124Results
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def Core234 (R : Nat → Prop) : Prop := ¬R 1 ∧ R 2 ∧ R 3 ∧ R 4
def Restricted234 (q i : Nat) : Prop :=
  i=4*q ∨ i=1 ∨ i=4*q+1 ∨ i=2*q+1 ∨ i=2*q+2 ∨
    ∃ p, P q p ∧ i=LIndex q p
def Fixed234 (q : Nat) (u v w k1 k2 : Prop) (e : Nat) : Prop :=
  (u ∧ CRow q e) ∨ (v ∧ DRow q e) ∨ (w ∧ BRow q e) ∨ (k1 ∧ K1Row q e) ∨ (k2 ∧ K2Row q e)
def Mixed234 (q t p : Nat) (u v w k1 k2 : Prop) (e : Nat) : Prop :=
  LRow q t p e ∨ Fixed234 q u v w k1 k2 e

theorem row_excluding_one (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h1 : ¬LuRazParametric.Row q i 1) : Restricted234 q i := by
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
  · exact False.elim (h1 ((LuRazParametric.row_case_0 q i 1 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inl h)
  · exact False.elim (h1 ((LuRazParametric.row_case_2 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h1 ((LuRazParametric.row_case_3 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h1 ((LuRazParametric.row_case_4 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h1 ((LuRazParametric.row_case_5 q i 1 (by omega) h).mpr (by omega)))
  · exact False.elim (h1 ((LuRazParametric.row_case_6 q i 1 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hl i (by omega))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hl i (by omega))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hl i (by omega))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hl i (by omega))))))
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact False.elim (h1 ((LuRazParametric.row_case_15 q i 1 (by omega) h).mpr (by omega)))

theorem restricted234_list (q : Nat) (hq : 4≤q) (l : List Nat)
    (hvalid : ∀ i∈l, Restricted234 q i) :
    ∃ u v w k1 k2 : Prop,
      (∀ e, ListUnion (LuRazParametric.Row q) l e ↔ Fixed234 q u v w k1 k2 e) ∨
      ∃ t p, P q t ∧ P q p ∧ t≤p ∧
        ∀ e, ListUnion (LuRazParametric.Row q) l e ↔ Mixed234 q t p u v w k1 k2 e := by
  induction l with
  | nil =>
    refine ⟨False,False,False,False,False,Or.inl ?_⟩
    intro e
    simp [ListUnion,Fixed234]
  | cons i rest ih =>
    have hi := hvalid i (by simp)
    have hrest : ∀ j∈rest, Restricted234 q j := by
      intro j hj
      exact hvalid j (by simp only [List.mem_cons]; exact Or.inr hj)
    obtain ⟨u,v,w,k1,k2,hnorm⟩ := ih hrest
    rcases hi with hi | hi | hi | hi | hi | ⟨a,ha,hi⟩
    · subst i
      refine ⟨True,v,w,k1,k2,?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · left
        intro e
        rw [listUnion_cons,C_source q e hq,hn]
        unfold Fixed234
        by_cases h : CRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨t,p,ht,hp,htp,?_⟩
        intro e
        rw [listUnion_cons,C_source q e hq,hn]
        unfold Mixed234 Fixed234
        by_cases h : CRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,True,w,k1,k2,?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · left
        intro e
        rw [listUnion_cons,D_source q e hq,hn]
        unfold Fixed234
        by_cases h : DRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨t,p,ht,hp,htp,?_⟩
        intro e
        rw [listUnion_cons,D_source q e hq,hn]
        unfold Mixed234 Fixed234
        by_cases h : DRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,True,k1,k2,?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · left
        intro e
        rw [listUnion_cons,B_source q e hq,hn]
        unfold Fixed234
        by_cases h : BRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨t,p,ht,hp,htp,?_⟩
        intro e
        rw [listUnion_cons,B_source q e hq,hn]
        unfold Mixed234 Fixed234
        by_cases h : BRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,w,True,k2,?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · left
        intro e
        rw [listUnion_cons,K1_source q e hq,hn]
        unfold Fixed234
        by_cases h : K1Row q e <;> simp [h,or_assoc]
      · right
        refine ⟨t,p,ht,hp,htp,?_⟩
        intro e
        rw [listUnion_cons,K1_source q e hq,hn]
        unfold Mixed234 Fixed234
        by_cases h : K1Row q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,w,k1,True,?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · left
        intro e
        rw [listUnion_cons,K2_source q e hq,hn]
        unfold Fixed234
        by_cases h : K2Row q e <;> simp [h,or_assoc]
      · right
        refine ⟨t,p,ht,hp,htp,?_⟩
        intro e
        rw [listUnion_cons,K2_source q e hq,hn]
        unfold Mixed234 Fixed234
        by_cases h : K2Row q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,w,k1,k2,Or.inr ?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · refine ⟨a,a,ha,ha,by omega,?_⟩
        intro e
        rw [listUnion_cons,LRow_source q a e hq ha,hn]
        rfl
      · refine ⟨min a t,max a p,P_min q a t ha ht,P_max q a p ha hp,by omega,?_⟩
        intro e
        rw [listUnion_cons,LRow_source q a e hq ha,hn]
        change (LRow q a a e ∨ (LRow q t p e ∨ Fixed234 q u v w k1 k2 e)) ↔ _
        exact or_assoc.symm.trans (or_congr (LRow_join q a a t p e hq ha ha ht hp (by omega) htp) Iff.rfl)

theorem core234_parts (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core234 R) :
    (∃ v w k1 k2 : Prop, (k1 ∨ k2) ∧ ∀ e, R e ↔ Fixed234 q True v w k1 k2 e) ∨
    ∃ t p, P q t ∧ P q p ∧ t≤p ∧ ∃ u v w k1 k2 : Prop,
      (k1 ∨ k2) ∧ ∀ e, R e ↔ Mixed234 q t p u v w k1 k2 e := by
  obtain ⟨l,_,hvalid,hR⟩ := hg
  have hi : ∀ i∈l, Restricted234 q i := by
    intro i him
    apply row_excluding_one q i hq (hvalid i him)
    intro h
    exact hc.1 ((hR 1).mp ⟨i,him,h⟩)
  obtain ⟨u,v,w,k1,k2,hnorm⟩ := restricted234_list q hq l hi
  rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
  · have h4 := (hn 4).mp ((hR 4).mpr hc.2.2.2)
    have h3 := (hn 3).mp ((hR 3).mpr hc.2.2.1)
    have hK : k1 ∨ k2 := by
      rcases h4 with h | h | h | h | h
      · have hh := h.2; unfold CRow I at hh; omega
      · have hh := h.2; unfold DRow I at hh; omega
      · have hh := h.2; unfold BRow I at hh; omega
      · exact Or.inl h.1
      · exact Or.inr h.1
    have hu : u := by
      rcases h3 with h | h | h | h | h
      · exact h.1
      · have hh := h.2; unfold DRow I at hh; omega
      · have hh := h.2; unfold BRow I at hh; omega
      · have hh := h.2; unfold K1Row I at hh; omega
      · have hh := h.2; unfold K2Row I at hh; omega
    refine Or.inl ⟨v,w,k1,k2,hK,?_⟩
    intro e
    rw [←hR e,hn]
    simp only [hu]
  · have h4 := (hn 4).mp ((hR 4).mpr hc.2.2.2)
    have hp' := hp
    have hbt := beta_bounds q t hq ht
    unfold P at hp'
    have hK : k1 ∨ k2 := by
      rcases h4 with h | h | h | h | h | h
      · unfold LRow LNormal I at h; omega
      · have hh := h.2; unfold CRow I at hh; omega
      · have hh := h.2; unfold DRow I at hh; omega
      · have hh := h.2; unfold BRow I at hh; omega
      · exact Or.inl h.1
      · exact Or.inr h.1
    exact Or.inr ⟨t,p,ht,hp,htp,u,v,w,k1,k2,hK,fun e => (hR e).symm.trans (hn e)⟩
end LuRazClosure
