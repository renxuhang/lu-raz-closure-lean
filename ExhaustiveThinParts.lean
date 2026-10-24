import ExhaustiveFullRetained
namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

def RestrictedThin (q i : Nat) : Prop :=
  i=4*q+2 ∨ i=4*q ∨ i=2*q+1 ∨ i=4 ∨ i=4*q-1 ∨
    ∃ a, (5≤a ∧ a≤2*q+1) ∧ i=JIndex a
def FixedThin (q : Nat) (u d k f l : Prop) (e : Nat) : Prop :=
  (u∧ARow q e) ∨ (d∧CRow q e) ∨ (k∧K1Row q e) ∨ (f∧EPrime q e) ∨ (l∧LPrime q e)
def MixedThin (q a b : Nat) (u d k f l : Prop) (e : Nat) : Prop :=
  JRow a b e ∨ FixedThin q u d k f l e

theorem k1_source_v (q e : Nat) (hq : 4≤q) : VRow q (2*q+1) e ↔ K1Row q e := by
  rw [unchanged_row q _ e (by unfold Special; omega)]
  exact K1_source q e hq

theorem row_no_last (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (hn : ¬VRow q i (4*q-1)) : RestrictedThin q i := by
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · exact False.elim (hn ((row_two q _ hq).mpr (by omega)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have ho : ¬Row q i (4*q-1) := by rwa [unchanged_row q i _ hs] at hn
  have hi0 : i≠0 := by
    intro h; exact ho ((row_case_0 q i _ (by omega) h).mpr (by omega))
  rcases row_nonTop_parts q i hq hi hi0 with ⟨t,ht⟩ | hJ | ⟨p,hp,rfl⟩
  · cases t <;> simp only [FixedGen.index] at ht
    case A => exact Or.inl ht
    case C => exact Or.inr (Or.inl ht)
    case K1 => exact Or.inr (Or.inr (Or.inl ht))
    case Z => exact False.elim (hs (Or.inl ht))
    all_goals subst i
    all_goals first
      | (rw [B_source q _ hq] at ho; unfold BRow I at ho; omega)
      | (rw [D_source q _ hq] at ho; unfold DRow I at ho; omega)
      | (rw [E_source q _ hq] at ho; unfold ERow I at ho; omega)
      | (rw [K2_source q _ hq] at ho; unfold K2Row I at ho; omega)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ))))
  · rw [LRow_source q p _ hq hp] at ho
    unfold LRow LNormal I beta at ho
    unfold Special LIndex beta at hs
    unfold P at hp
    repeat first | (simp_all <;> omega) | split at ho | split at hs

theorem restrictedThin_list (q : Nat) (hq : 4≤q) (l : List Nat)
    (hvalid : ∀ i∈l, RestrictedThin q i) :
    ∃ u v d k1 k2 : Prop,
      (∀ e, ListUnion (VRow q) l e ↔ FixedThin q u v d k1 k2 e) ∨
      ∃ a b, JReachable q a b ∧
        ∀ e, ListUnion (VRow q) l e ↔ MixedThin q a b u v d k1 k2 e := by
  induction l with
  | nil =>
    refine ⟨False,False,False,False,False,Or.inl ?_⟩
    intro e
    simp [ListUnion,FixedThin]
  | cons i rest ih =>
    have hi := hvalid i (by simp)
    have hrest : ∀ j∈rest, RestrictedThin q j := by
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
        unfold FixedThin
        by_cases h : ARow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,a_source q e hq,hn]
        unfold MixedThin FixedThin
        by_cases h : ARow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,True,d,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,c_source q e hq,hn]
        unfold FixedThin
        by_cases h : CRow q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,c_source q e hq,hn]
        unfold MixedThin FixedThin
        by_cases h : CRow q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,True,k1,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,k1_source_v q e hq,hn]
        unfold FixedThin
        by_cases h : K1Row q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,k1_source_v q e hq,hn]
        unfold MixedThin FixedThin
        by_cases h : K1Row q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,d,True,k2,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,e_source q e hq,hn]
        unfold FixedThin
        by_cases h : EPrime q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,e_source q e hq,hn]
        unfold MixedThin FixedThin
        by_cases h : EPrime q e <;> simp [h,or_assoc]
    · subst i
      refine ⟨u,v,d,k1,True,?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · left
        intro e
        rw [listUnion_cons,last_source q e hq,hn]
        unfold FixedThin
        by_cases h : LPrime q e <;> simp [h,or_assoc]
      · right
        refine ⟨a,b,hab,?_⟩
        intro e
        rw [listUnion_cons,last_source q e hq,hn]
        unfold MixedThin FixedThin
        by_cases h : LPrime q e <;> simp [h,or_assoc]
    · subst i
      have htj := J_single_reachable q t hq ht
      refine ⟨u,v,d,k1,k2,Or.inr ?_⟩
      rcases hnorm with hn | ⟨a,b,hab,hn⟩
      · refine ⟨t,g q t,htj,?_⟩
        intro e
        rw [listUnion_cons,j_source_v q t e hq ht,hn]
        simp only [MixedThin,JRow,or_assoc]
      · refine ⟨min t a,max (g q t) b,JReachable_join q t (g q t) a b hq htj hab,?_⟩
        intro e
        rw [listUnion_cons,j_source_v q t e hq ht,hn]
        change (JRow t (g q t) e ∨ (JRow a b e ∨ FixedThin q u v d k1 k2 e)) ↔ _
        exact or_assoc.symm.trans (or_congr (JRow_join q t (g q t) a b e hq htj hab) Iff.rfl)


theorem thin_parts (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hg : Generated q R) (hn : ¬R (4*q-1)) :
    ∃ u d k f l : Prop,
      (∀ e, R e ↔ FixedThin q u d k f l e) ∨
      ∃ a b, JReachable q a b ∧ ∀ e, R e ↔ MixedThin q a b u d k f l e := by
  obtain ⟨ls,_,hv,hR⟩ := hg
  have hr : ∀ i∈ls, RestrictedThin q i := by
    intro i hi
    exact row_no_last q i hq (hv i hi) (fun h => hn ((hR _).mp ⟨i,hi,h⟩))
  obtain ⟨u,d,k,f,l,hnorm⟩ := restrictedThin_list q hq ls hr
  refine ⟨u,d,k,f,l,?_⟩
  rcases hnorm with he | ⟨a,b,hab,he⟩
  · exact Or.inl (fun e => (hR e).symm.trans (he e))
  · exact Or.inr ⟨a,b,hab,fun e => (hR e).symm.trans (he e)⟩

end LuRazThreeRow
