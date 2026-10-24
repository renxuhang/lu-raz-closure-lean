import VariantCoreFrequencyParts

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- An actual closure enumeration with the exact frequency at any of the four core coordinates. -/
theorem core_frequency_exact (q e : Nat) (hq : 4≤q) (he : 1≤e ∧ e≤4) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R) ∧
      2*(l.length : Int)=23*(q:Int)*(q:Int)+31*(q:Int)-30 ∧
      2*CountAt l e=NewCoreFrequency2 (q:Int) e := by
  classical
  obtain ⟨o,hon,hoe,hof⟩ := old_changed_frequency2 q e hq he
  obtain ⟨n,hnn,hne,hnf⟩ := new_changed_frequency2 q e hq he
  let u := (closureMembers q).filter (fun R => decide (¬Changed R))
  have hun : u.Nodup := List.Nodup.sublist List.filter_sublist (closure_members_nodup q hq)
  have hue : ∀ R, R∈u ↔ LuRazClosure.Generated q R ∧ ¬Changed R := by
    intro R
    simp only [u,List.mem_filter,decide_eq_true_eq,closure_members_exact q hq R]
  have huen : ∀ R, R∈u ↔ Generated q R ∧ ¬Changed R := by
    intro R
    rw [hue R]
    by_cases hc : Changed R
    · simp [hc]
    · rw [unchanged_outside_changed q hq R hc]
  have ho := append_enumerations (LuRazClosure.Generated q) (fun R => ¬Changed R) Changed
    u o hun hon hue hoe (fun R h h' => h h')
  have hn := append_enumerations (Generated q) (fun R => ¬Changed R) Changed
    u n hun hnn huen hne (fun R h h' => h h')
  have hne' : ∀ R, R∈u++n ↔ Generated q R := by
    intro R
    rw [hn.2 R]
    by_cases hc : Changed R <;> simp [hc]
  have hp : (u++o).Perm (closureMembers q) := by
    apply (List.perm_ext_iff_of_nodup ho.1 (closure_members_nodup q hq)).mpr
    intro R
    rw [ho.2 R,closure_members_exact q hq R]
    by_cases hc : Changed R <;> simp [hc]
  have hfreq := count_at_perm (u++o) (closureMembers q) hp e
  rw [count_at_append] at hfreq
  have hf := old_core_frequency2 q e hq he
  obtain ⟨l',hl'n,hl'e,hl'len⟩ := closure_new_cardinality q hq
  have hp' : (u++n).Perm l' := by
    apply (List.perm_ext_iff_of_nodup hn.1 hl'n).mpr
    intro R
    rw [hne' R,hl'e R]
  refine ⟨u++n,hn.1,hne',?_,?_⟩
  · rw [hp'.length_eq]
    exact hl'len
  · rw [count_at_append]
    have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp only [OldCoreFrequency2,NewCoreFrequency2,OldChangedFrequency2,NewChangedFrequency2,
        Nat.reduceEqDiff,ite_true,ite_false] at hf hof hnf ⊢ <;> omega

theorem core_frequency_finite (q e : Nat) (hq : 4≤q) (he : 1≤e ∧ e≤4) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ T ⟨e-1,by omega⟩) ∧
      2*(l.length : Int)=NewCoreFrequency2 (q:Int) e := by
  classical
  obtain ⟨l,hn,hle,_,hf⟩ := core_frequency_exact q e hq he
  let f := l.filter (fun R => decide (R e))
  have hfn : f.Nodup := List.Nodup.sublist List.filter_sublist hn
  have hfe : ∀ R, R∈f ↔ Generated q R ∧ R e := by
    intro R
    simp only [f,List.mem_filter,decide_eq_true_eq,hle R]
  have ht := transfer_enumeration q hq (fun R => R e) f hfn hfe
  refine ⟨f.map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (lift_at q T e (by omega)))
  · simpa only [List.length_map,CountAt,f] using hf

theorem core_frequency_above_two_thirds (q e : Nat) (hq : 4≤q) (he : 1≤e ∧ e≤4) :
    2*(23*(q:Int)*(q:Int)+31*(q:Int)-30)<3*NewCoreFrequency2 (q:Int) e := by
  have hq' : 4≤(q:Int) := by omega
  have hprod := Int.mul_nonneg (show 0≤(q:Int) by omega) (show 0≤(q:Int)-4 by omega)
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp only [NewCoreFrequency2,Nat.reduceEqDiff,ite_true,ite_false] <;>
    simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at * <;> omega

/-- Each of the four core coordinates lies in strictly more than two thirds of the closure. -/
theorem core_strict_two_thirds (q e : Nat) (hq : 4≤q) (he : 1≤e ∧ e≤4) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R) ∧
      2*(l.length : Int)<3*CountAt l e := by
  obtain ⟨l,hn,hle,hl,hf⟩ := core_frequency_exact q e hq he
  have h := core_frequency_above_two_thirds q e hq he
  exact ⟨l,hn,hle,by omega⟩

/-- The smaller closure has 2q more distinct members containing coordinate 4. -/
theorem coordinate_four_increase (q : Nat) (hq : 4≤q) :
    ∃ old new : List (Fin (4*q) → Prop), old.Nodup ∧ new.Nodup ∧
      (∀ T, T∈old ↔ LuRazClosure.FinGenerated q T ∧ T ⟨3,by omega⟩) ∧
      (∀ T, T∈new ↔ FinGenerated q T ∧ T ⟨3,by omega⟩) ∧
      new.length=old.length+2*q := by
  obtain ⟨old,ho,hoe,hol⟩ := coordinate_four_finite_count q hq
  obtain ⟨new,hn,hne,hnl⟩ := core_frequency_finite q 4 hq (by omega)
  refine ⟨old,new,ho,hn,hoe,hne,?_⟩
  simp only [NewCoreFrequency2,Nat.reduceEqDiff,ite_false] at hnl
  omega

end LuRazThreeRow
