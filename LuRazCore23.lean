import LuRazGenerated

namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def CRow (q e : Nat) : Prop := e=3 ∨ I 5 (2*q+2) e ∨ e=3*q+1
def DRow (q e : Nat) : Prop := e=2 ∨ I (2*q+1) (4*q) e
def LRow (q t p e : Nat) : Prop := e=2 ∨ e=3 ∨ LNormal q t p e
def Core23 (R : Nat → Prop) : Prop := ¬R 1 ∧ R 2 ∧ R 3 ∧ ¬R 4
def Mixed23 (q t p : Nat) (u v w : Prop) (e : Nat) : Prop :=
  LRow q t p e ∨ (u ∧ CRow q e) ∨ (v ∧ DRow q e) ∨ (w ∧ BRow q e)

theorem C_source (q e : Nat) (hq : 4 ≤ q) :
    LuRazParametric.Row q (4*q) e ↔ CRow q e := by
  rw [LuRazParametric.row_case_13 q (4*q) e (by omega) rfl]
  rfl

theorem D_source (q e : Nat) (hq : 4 ≤ q) :
    LuRazParametric.Row q 1 e ↔ DRow q e := by
  rw [LuRazParametric.row_case_1 q 1 e (by omega) rfl]
  rfl

theorem LRow_source (q p e : Nat) (hq : 4 ≤ q) (hp : P q p) :
    LuRazParametric.Row q (LIndex q p) e ↔ LRow q p p e := by
  rw [L_is_source_row q p e hq hp]
  simp only [LRow,L_single_normal]

theorem generated_C (q : Nat) (hq : 4 ≤ q) : Generated q (CRow q) :=
  generated_congr q (generated_row q (4*q) (by omega)) (fun e => C_source q e hq)

theorem generated_D (q : Nat) (hq : 4 ≤ q) : Generated q (DRow q) :=
  generated_congr q (generated_row q 1 (by omega)) (fun e => D_source q e hq)

theorem generated_L (q t p : Nat) (hq : 4 ≤ q) (ht : P q t) (hp : P q p) (htp : t≤p) :
    Generated q (LRow q t p) := by
  obtain ⟨l,hne,hvalid,heq⟩ := L_source_attainable q t p hq ht hp htp
  refine ⟨l.map (LIndex q),?_,?_,?_⟩
  · intro h
    exact hne (List.map_eq_nil_iff.mp h)
  · intro i hi
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
    have hb := beta_bounds q a hq (hvalid a ha)
    unfold LIndex
    omega
  · intro e
    constructor
    · rintro ⟨i,hi,hie⟩
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
      exact (heq e).mp ⟨a,ha,hie⟩
    · intro h
      obtain ⟨a,ha,hae⟩ := (heq e).mpr h
      exact ⟨LIndex q a,List.mem_map.mpr ⟨a,ha,rfl⟩,hae⟩

theorem LRow_join (q t p s r e : Nat) (hq : 4 ≤ q)
    (ht : P q t) (hp : P q p) (hs : P q s) (hr : P q r) (htp : t≤p) (hsr : s≤r) :
    (LRow q t p e ∨ LRow q s r e) ↔ LRow q (min t s) (max p r) e := by
  by_cases h2 : e=2
  · simp [LRow,h2]
  by_cases h3 : e=3
  · simp [LRow,h3]
  simpa only [LRow,h2,h3,false_or] using L_join_normal q t p s r e hq ht hp hs hr htp hsr

def Restricted23 (q i : Nat) : Prop :=
  i=4*q ∨ i=1 ∨ i=4*q+1 ∨ ∃ p, P q p ∧ i=LIndex q p

theorem row_excluding_one_four (q i : Nat) (hq : 4 ≤ q) (hi : i≤4*q+2)
    (h1 : ¬LuRazParametric.Row q i 1) (h4 : ¬LuRazParametric.Row q i 4) : Restricted23 q i := by
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
  · exact False.elim (h4 ((LuRazParametric.row_case_7 q i 4 (by omega) h).mpr (by omega)))
  · exact False.elim (h4 ((LuRazParametric.row_case_8 q i 4 (by omega) h).mpr (by omega)))
  · exact Or.inr (Or.inr (Or.inr (hl i (by omega))))
  · exact Or.inr (Or.inr (Or.inr (hl i (by omega))))
  · exact Or.inr (Or.inr (Or.inr (hl i (by omega))))
  · exact Or.inr (Or.inr (Or.inr (hl i (by omega))))
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact False.elim (h1 ((LuRazParametric.row_case_15 q i 1 (by omega) h).mpr (by omega)))

theorem restricted23_list (q : Nat) (hq : 4 ≤ q) (l : List Nat)
    (hvalid : ∀ i ∈ l, Restricted23 q i) :
    ∃ u v w : Prop,
      (∀ e, ListUnion (LuRazParametric.Row q) l e ↔
        (u ∧ CRow q e) ∨ (v ∧ DRow q e) ∨ (w ∧ BRow q e)) ∨
      ∃ t p, P q t ∧ P q p ∧ t≤p ∧
        ∀ e, ListUnion (LuRazParametric.Row q) l e ↔ Mixed23 q t p u v w e := by
  induction l with
  | nil =>
    refine ⟨False,False,False,Or.inl ?_⟩
    intro e
    simp [ListUnion]
  | cons i rest ih =>
    have hi := hvalid i (by simp)
    have hrest : ∀ j ∈ rest, Restricted23 q j := by
      intro j hj
      exact hvalid j (by simp only [List.mem_cons]; exact Or.inr hj)
    obtain ⟨u,v,w,hnorm⟩ := ih hrest
    rcases hi with hi | hi | hi | ⟨a,ha,hi⟩
    · subst i
      refine ⟨True,v,w,?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · left
        intro e
        rw [listUnion_cons,C_source q e hq,hn]
        by_cases h : CRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨t,p,ht,hp,htp,?_⟩
        intro e
        rw [listUnion_cons,C_source q e hq,hn]
        unfold Mixed23
        by_cases h : CRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,True,w,?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · left
        intro e
        rw [listUnion_cons,D_source q e hq,hn]
        by_cases h : DRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨t,p,ht,hp,htp,?_⟩
        intro e
        rw [listUnion_cons,D_source q e hq,hn]
        unfold Mixed23
        by_cases h : DRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,True,?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · left
        intro e
        rw [listUnion_cons,B_source q e hq,hn]
        by_cases h : BRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨t,p,ht,hp,htp,?_⟩
        intro e
        rw [listUnion_cons,B_source q e hq,hn]
        unfold Mixed23
        by_cases h : BRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,w,Or.inr ?_⟩
      rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
      · refine ⟨a,a,ha,ha,by omega,?_⟩
        intro e
        rw [listUnion_cons,LRow_source q a e hq ha,hn]
        rfl
      · refine ⟨min a t,max a p,P_min q a t ha ht,P_max q a p ha hp,by omega,?_⟩
        intro e
        rw [listUnion_cons,LRow_source q a e hq ha,hn]
        change (LRow q a a e ∨ (LRow q t p e ∨ (u ∧ CRow q e) ∨ (v ∧ DRow q e) ∨ (w ∧ BRow q e))) ↔ _
        exact or_assoc.symm.trans (or_congr (LRow_join q a a t p e hq ha ha ht hp (by omega) htp) Iff.rfl)

theorem full_core23_mixed (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hgen : Generated q R) (hcore : Core23 R) :
    ∃ t p, P q t ∧ P q p ∧ t≤p ∧ ∃ u v w : Prop,
      ∀ e, R e ↔ Mixed23 q t p u v w e := by
  obtain ⟨l,_,hvalid,hR⟩ := hgen
  have hr : ∀ i ∈ l, Restricted23 q i := by
    intro i hi
    apply row_excluding_one_four q i hq (hvalid i hi)
    · intro h
      exact hcore.1 ((hR 1).mp ⟨i,hi,h⟩)
    · intro h
      exact hcore.2.2.2 ((hR 4).mp ⟨i,hi,h⟩)
  obtain ⟨u,v,w,hnorm⟩ := restricted23_list q hq l hr
  rcases hnorm with hn | ⟨t,p,ht,hp,htp,hn⟩
  · have h3 := (hn 3).mp ((hR 3).mpr hcore.2.2.1)
    have h2 := (hn 2).mp ((hR 2).mpr hcore.2.1)
    have hu : u := by
      rcases h3 with h | h | h
      · exact h.1
      · have hd := h.2; unfold DRow I at hd; omega
      · have hb := h.2; unfold BRow I at hb; omega
    have hv : v := by
      rcases h2 with h | h | h
      · have hc := h.2; unfold CRow I at hc; omega
      · exact h.1
      · have hb := h.2; unfold BRow I at hb; omega
    have hp4 : P q 4 := by unfold P; omega
    refine ⟨4,4,hp4,hp4,by omega,True,True,False,?_⟩
    intro e
    rw [←hR e,hn]
    simp only [hu,hv,true_and]
    unfold Mixed23 LRow LNormal CRow DRow BRow I beta
    simp (disch := omega) only [ite_eq_left,ite_eq_right,true_and,false_and,or_false,false_or]
    omega
  · exact ⟨t,p,ht,hp,htp,u,v,w,fun e => (hR e).symm.trans (hn e)⟩

theorem mixed23_generated (q t p : Nat) (hq : 4≤q)
    (ht : P q t) (hp : P q p) (htp : t≤p) (u v w : Prop) :
    Generated q (Mixed23 q t p u v w) := by
  have h0 := generated_L q t p hq ht hp htp
  have h1 := generated_optional q h0 (generated_C q hq) u
  have h2 := generated_optional q h1 (generated_D q hq) v
  have h3 := generated_optional q h2 (generated_B q hq) w
  apply generated_congr q h3
  intro e
  simp only [Mixed23,or_assoc]

end LuRazClosure
