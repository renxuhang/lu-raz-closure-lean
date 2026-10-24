import SixRowLargeSources
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
def Fixed6 (q : Nat) (u v w : Prop) (e : Nat) : Prop :=
  (u ∧ C6 q e) ∨ (v ∧ E6 q e) ∨ (w ∧ LuRazClosure.BRow q e)
def Mixed6 (q t p : Nat) (u v w : Prop) (e : Nat) : Prop :=
  LRow q t p e ∨ Fixed6 q u v w e

theorem restricted6_list (q : Nat) (hq : 4≤q) (l : List Nat)
    (hv : ∀i∈l,Restricted6 q i) :
    ∃u v w : Prop,
      (∀e,ListUnion (LuRazSixRow.BRow q) l e ↔ Fixed6 q u v w e) ∨
      ∃t p,P q t ∧ P q p ∧ t≤p ∧ p≤2*q ∧
        ∀e,ListUnion (LuRazSixRow.BRow q) l e ↔ Mixed6 q t p u v w e := by
  induction l with
  | nil => exact ⟨False,False,False,Or.inl (by intro e; simp [ListUnion,Fixed6])⟩
  | cons i rest ih =>
    have hi := hv i (by simp)
    have hr : ∀j∈rest,Restricted6 q j := by intro j hj; exact hv j (by simp [hj])
    obtain ⟨u,v,w,hn⟩ := ih hr
    rcases hi with hi|hi|hi|⟨s,hs,hsh,hi⟩
    · subst i
      refine ⟨True,v,w,?_⟩
      rcases hn with hn|⟨t,p,ht,hp,htp,hph,hn⟩
      · left; intro e; rw [listUnion_cons,c6_source q e hq,hn]
        by_cases he : C6 q e <;> simp [Fixed6,he,or_assoc]
      · right; refine ⟨t,p,ht,hp,htp,hph,?_⟩
        intro e; rw [listUnion_cons,c6_source q e hq,hn]
        by_cases he : C6 q e <;> simp [Mixed6,Fixed6,he,or_assoc]
    · subst i
      refine ⟨u,True,w,?_⟩
      rcases hn with hn|⟨t,p,ht,hp,htp,hph,hn⟩
      · left; intro e; rw [listUnion_cons,e6_source q e hq,hn]
        by_cases he : E6 q e <;> simp [Fixed6,he,or_assoc]
      · right; refine ⟨t,p,ht,hp,htp,hph,?_⟩
        intro e; rw [listUnion_cons,e6_source q e hq,hn]
        by_cases he : E6 q e <;> simp [Mixed6,Fixed6,he,or_assoc]
    · subst i
      refine ⟨u,v,True,?_⟩
      rcases hn with hn|⟨t,p,ht,hp,htp,hph,hn⟩
      · left; intro e; rw [listUnion_cons,b0_source q e hq,hn]
        by_cases he : LuRazClosure.BRow q e <;> simp [Fixed6,he,or_assoc]
      · right; refine ⟨t,p,ht,hp,htp,hph,?_⟩
        intro e; rw [listUnion_cons,b0_source q e hq,hn]
        by_cases he : LuRazClosure.BRow q e <;> simp [Mixed6,Fixed6,he,or_assoc]
    · subst i
      refine ⟨u,v,w,Or.inr ?_⟩
      rcases hn with hn|⟨t,p,ht,hp,htp,hph,hn⟩
      · refine ⟨s,s,hs,hs,by omega,hsh,?_⟩
        intro e; rw [listUnion_cons,l6_source q s e hq hs hsh,hn]; rfl
      · refine ⟨min s t,max s p,P_min q s t hs ht,P_max q s p hs hp,by omega,by omega,?_⟩
        intro e; rw [listUnion_cons,l6_source q s e hq hs hsh,hn]
        change (LRow q s s e ∨ (LRow q t p e ∨ Fixed6 q u v w e)) ↔ _
        exact or_assoc.symm.trans (or_congr (LRow_join q s s t p e hq hs hs ht hp (by omega) htp) Iff.rfl)

theorem core6_parts (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : Generated q R) (hc : Core23 R) :
    ∃u v w : Prop,
      (v ∧ ∀e,R e ↔ Fixed6 q u v w e) ∨
      ∃t p,P q t ∧ P q p ∧ t≤p ∧ p≤2*q ∧ ∀e,R e ↔ Mixed6 q t p u v w e := by
  obtain ⟨l,_,hv,he⟩ := hg
  have hr : ∀i∈l,Restricted6 q i := by
    intro i hi
    exact no_one_four_source6 q i hq (hv i hi)
      (fun hh=>hc.1 ((he 1).mp ⟨i,hi,hh⟩))
      (fun hh=>hc.2.2.2 ((he 4).mp ⟨i,hi,hh⟩))
  obtain ⟨u,v,w,hn⟩ := restricted6_list q hq l hr
  refine ⟨u,v,w,?_⟩
  rcases hn with hn|⟨t,p,ht,hp,htp,hph,hn⟩
  · left
    have h2 := (hn 2).mp ((he 2).mpr hc.2.1)
    have hv : v := by
      simp only [Fixed6,C6,LuRazClosure.BRow,I] at h2
      rcases h2 with h|h|h
      · omega
      · exact h.1
      · omega
    exact ⟨hv,fun e=>(he e).symm.trans (hn e)⟩
  · exact Or.inr ⟨t,p,ht,hp,htp,hph,fun e=>(he e).symm.trans (hn e)⟩
end LuRazSixRowClosure
