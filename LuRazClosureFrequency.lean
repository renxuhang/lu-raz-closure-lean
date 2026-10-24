import LuRazTotalClosure

namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section

def hasOne (R : Nat → Prop) : Bool := by
  classical
  exact decide (R 1)

def containingOneMembers (q : Nat) : List (Nat → Prop) := by
  classical
  exact (closureMembers q).filter hasOne

theorem coreCode_odd_iff_one (R : Nat → Prop) : coreCode R % 2 = 1 ↔ R 1 := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;>
    by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [coreCode,h1,h2,h3,h4]

theorem filter_partialGroup_one (q k : Nat) (hq : 4≤q) (hk : k∈partialCodes) :
    (partialGroup q k).filter hasOne =
      if k % 2 = 1 then partialGroup q k else [] := by
  classical
  by_cases ho : k % 2 = 1
  · rw [ite_eq_left ho]
    apply List.filter_eq_self.mpr
    intro R hR
    unfold hasOne
    apply decide_eq_true
    apply (coreCode_odd_iff_one R).mp
    rw [((partialGroup_exact q k hq hk R).mp hR).2]
    exact ho
  · rw [ite_eq_right ho]
    apply List.filter_eq_nil_iff.mpr
    intro R hR
    unfold hasOne
    intro hb
    have h1 := of_decide_eq_true hb
    have hh := (coreCode_odd_iff_one R).mpr h1
    rw [((partialGroup_exact q k hq hk R).mp hR).2] at hh
    exact ho hh

theorem filter_fullMembers_one (q : Nat) (hq : 4≤q) :
    (fullMembers q).filter hasOne = fullMembers q := by
  classical
  apply List.filter_eq_self.mpr
  intro R hR
  unfold hasOne
  exact decide_eq_true ((full_members_exact q hq R).mp hR).2.1

theorem containingOneMembers_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈containingOneMembers q ↔ Generated q R ∧ R 1 := by
  classical
  simp only [containingOneMembers,List.mem_filter,hasOne,decide_eq_true_eq,closure_members_exact q hq R]

theorem containingOneMembers_nodup (q : Nat) (hq : 4≤q) :
    (containingOneMembers q).Nodup := by
  classical
  exact List.Nodup.sublist List.filter_sublist (closure_members_nodup q hq)

theorem containingOneMembers_length (q : Nat) (hq : 4≤q) :
    2*((containingOneMembers q).length : Int)=19*(q:Int)*(q:Int)+25*(q:Int)-44 := by
  classical
  have he : containingOneMembers q = partialGroup q 1 ++ partialGroup q 3 ++
      partialGroup q 5 ++ partialGroup q 7 ++ partialGroup q 9 ++
      partialGroup q 11 ++ partialGroup q 13 ++ fullMembers q := by
    simp only [containingOneMembers,closureMembers,partialMembers,partialCodes,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.filter_append]
    rw [filter_partialGroup_one q 0 hq (by decide),filter_partialGroup_one q 1 hq (by decide),
      filter_partialGroup_one q 2 hq (by decide),filter_partialGroup_one q 3 hq (by decide),
      filter_partialGroup_one q 4 hq (by decide),filter_partialGroup_one q 5 hq (by decide),
      filter_partialGroup_one q 6 hq (by decide),filter_partialGroup_one q 7 hq (by decide),
      filter_partialGroup_one q 9 hq (by decide),filter_partialGroup_one q 10 hq (by decide),
      filter_partialGroup_one q 11 hq (by decide),filter_partialGroup_one q 13 hq (by decide),
      filter_partialGroup_one q 14 hq (by decide),filter_fullMembers_one q hq]
    simp only [Nat.reduceMod,Nat.reduceEqDiff,ite_true,ite_false,List.nil_append,List.append_nil,List.append_assoc]
  have h1 : ((partialGroup q 1).length : Int)=2 := by
    have hh : (enumSmall 1).length=2 := by simpa only [smallCount] using enumSmall_length 1 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h3 : ((partialGroup q 3).length : Int)=1 := by
    have hh : (enumSmall 3).length=1 := by simpa only [smallCount] using enumSmall_length 3 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h5 : ((partialGroup q 5).length : Int)=5 := by
    have hh : (enumSmall 5).length=5 := by simpa only [smallCount] using enumSmall_length 5 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h7 : 2*((partialGroup q 7).length : Int)=3*(q:Int)*(q:Int)+7*(q:Int)-14 := by
    simpa only [partialGroup,core123Members,List.length_map] using enum123_length q hq
  have h9 : ((partialGroup q 9).length : Int)=3*(q:Int)*(q:Int)-5*(q:Int)+2 := by
    simpa only [partialGroup,core14Members,List.length_map] using enum14_length q hq
  have h11 : ((partialGroup q 11).length : Int)=9*(q:Int)-10 := by
    simpa only [partialGroup,core124Members,List.length_map] using enum124_length q hq
  have h13 : ((partialGroup q 13).length : Int)=10*(q:Int)-16 := by
    simpa only [partialGroup,core134Members,List.length_map] using enum134_length q hq
  have hf : ((fullMembers q).length : Int)=5*(q:Int)*(q:Int)-5*(q:Int)+1 := by
    simpa only [fullMembers,List.length_map] using enumFull_length q hq
  rw [he]
  simp only [List.length_append,Int.natCast_add]
  simp only [Int.mul_assoc] at h7 h9 hf ⊢
  omega

theorem coordinate_one_finite_count (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ T ⟨0,by omega⟩) ∧
      2*(l.length : Int)=19*(q:Int)*(q:Int)+25*(q:Int)-44 := by
  have ht := transfer_enumeration q hq (fun R => R 1) (containingOneMembers q)
    (containingOneMembers_nodup q hq) (containingOneMembers_exact q hq)
  refine ⟨(containingOneMembers q).map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (lift_at q T 1 (by omega)))
  · simpa only [List.length_map] using containingOneMembers_length q hq

theorem coordinate_one_for_every_x (x : Nat) (hx : 3≤x) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated (x+1) T ∧ T ⟨0,by omega⟩) ∧
      2*(l.length : Int)=19*(x:Int)*(x:Int)+63*(x:Int) := by
  obtain ⟨l,hn,he,hl⟩ := coordinate_one_finite_count (x+1) (by omega)
  refine ⟨l,hn,he,?_⟩
  simp only [Int.natCast_add,Int.natCast_one,Int.mul_add,Int.mul_sub,
    Int.add_mul,Int.sub_mul,Int.mul_assoc] at hl ⊢
  omega

theorem coordinate_one_strict_three_quarters (q : Nat) (hq : 4≤q) :
    3*((closureMembers q).length : Int)<4*((containingOneMembers q).length : Int) := by
  have hc := closure_members_length q hq
  have hf := containingOneMembers_length q hq
  have hs : 0≤(q:Int)*((q:Int)-4) := Int.mul_nonneg (by omega) (by omega)
  have hm : (q:Int)*4=4*(q:Int) := Int.mul_comm (q:Int) 4
  simp only [Int.mul_sub,hm,Int.mul_assoc] at hc hf hs ⊢
  omega

#print axioms coreCode_odd_iff_one
#print axioms filter_partialGroup_one
#print axioms filter_fullMembers_one
#print axioms containingOneMembers_exact
#print axioms containingOneMembers_nodup
#print axioms containingOneMembers_length
#print axioms coordinate_one_finite_count
#print axioms coordinate_one_for_every_x
#print axioms coordinate_one_strict_three_quarters

end
end LuRazClosure
