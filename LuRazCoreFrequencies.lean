import LuRazClosureFrequency
namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
def hasTwo (R : Nat → Prop) : Bool := by
  classical
  exact decide (R 2)

def containingTwoMembers (q : Nat) : List (Nat → Prop) := by
  classical
  exact (closureMembers q).filter hasTwo

theorem coreCode_bit2_iff_two (R : Nat → Prop) : coreCode R / 2 % 2 = 1 ↔ R 2 := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;>
    by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [coreCode,h1,h2,h3,h4]

theorem filter_partialGroup_two (q k : Nat) (hq : 4≤q) (hk : k∈partialCodes) :
    (partialGroup q k).filter hasTwo =
      if k / 2 % 2 = 1 then partialGroup q k else [] := by
  classical
  by_cases ho : k / 2 % 2 = 1
  · rw [ite_eq_left ho]
    apply List.filter_eq_self.mpr
    intro R hR
    unfold hasTwo
    apply decide_eq_true
    apply (coreCode_bit2_iff_two R).mp
    rw [((partialGroup_exact q k hq hk R).mp hR).2]
    exact ho
  · rw [ite_eq_right ho]
    apply List.filter_eq_nil_iff.mpr
    intro R hR
    unfold hasTwo
    intro hb
    have h1 := of_decide_eq_true hb
    have hh := (coreCode_bit2_iff_two R).mpr h1
    rw [((partialGroup_exact q k hq hk R).mp hR).2] at hh
    exact ho hh

theorem filter_fullMembers_two (q : Nat) (hq : 4≤q) :
    (fullMembers q).filter hasTwo = fullMembers q := by
  classical
  apply List.filter_eq_self.mpr
  intro R hR
  unfold hasTwo
  exact decide_eq_true ((full_members_exact q hq R).mp hR).2.2.1

theorem containingTwoMembers_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈containingTwoMembers q ↔ Generated q R ∧ R 2 := by
  classical
  simp only [containingTwoMembers,List.mem_filter,hasTwo,decide_eq_true_eq,closure_members_exact q hq R]

theorem containingTwoMembers_nodup (q : Nat) (hq : 4≤q) :
    (containingTwoMembers q).Nodup := by
  classical
  exact List.Nodup.sublist List.filter_sublist (closure_members_nodup q hq)


theorem containingTwoMembers_length (q : Nat) (hq : 4≤q) :
    2*((containingTwoMembers q).length : Int)=17*(q:Int)*(q:Int)+25*(q:Int)-34 := by
  classical
  have he : containingTwoMembers q = partialGroup q 2 ++ partialGroup q 3 ++ partialGroup q 6 ++ partialGroup q 7 ++ partialGroup q 10 ++ partialGroup q 11 ++ partialGroup q 14 ++ fullMembers q := by
    simp only [containingTwoMembers,closureMembers,partialMembers,partialCodes,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.filter_append]
    rw [filter_partialGroup_two q 0 hq (by decide),filter_partialGroup_two q 1 hq (by decide),filter_partialGroup_two q 2 hq (by decide),filter_partialGroup_two q 3 hq (by decide),filter_partialGroup_two q 4 hq (by decide),filter_partialGroup_two q 5 hq (by decide),filter_partialGroup_two q 6 hq (by decide),filter_partialGroup_two q 7 hq (by decide),filter_partialGroup_two q 9 hq (by decide),filter_partialGroup_two q 10 hq (by decide),filter_partialGroup_two q 11 hq (by decide),filter_partialGroup_two q 13 hq (by decide),filter_partialGroup_two q 14 hq (by decide),filter_fullMembers_two q hq]
    simp only [Nat.reduceDiv,Nat.reduceMod,Nat.reduceEqDiff,ite_true,ite_false,List.nil_append,List.append_nil,List.append_assoc]
  have h0 : ((partialGroup q 0).length : Int)=1 := by
    have hh : (enumSmall 0).length=1 := by simpa only [smallCount] using enumSmall_length 0 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h1 : ((partialGroup q 1).length : Int)=2 := by
    have hh : (enumSmall 1).length=2 := by simpa only [smallCount] using enumSmall_length 1 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h2 : ((partialGroup q 2).length : Int)=1 := by
    have hh : (enumSmall 2).length=1 := by simpa only [smallCount] using enumSmall_length 2 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h3 : ((partialGroup q 3).length : Int)=1 := by
    have hh : (enumSmall 3).length=1 := by simpa only [smallCount] using enumSmall_length 3 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h4 : ((partialGroup q 4).length : Int)=2 := by
    have hh : (enumSmall 4).length=2 := by simpa only [smallCount] using enumSmall_length 4 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h5 : ((partialGroup q 5).length : Int)=5 := by
    have hh : (enumSmall 5).length=5 := by simpa only [smallCount] using enumSmall_length 5 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h6 : ((partialGroup q 6).length : Int)=2*(q:Int)*(q:Int)-(q:Int)-3 := by
    simpa only [partialGroup,core23Members,List.length_map] using enum23_length q hq
  have h7 : 2*((partialGroup q 7).length : Int)=3*(q:Int)*(q:Int)+7*(q:Int)-14 := by
    simpa only [partialGroup,core123Members,List.length_map] using enum123_length q hq
  have h9 : ((partialGroup q 9).length : Int)=3*(q:Int)*(q:Int)-5*(q:Int)+2 := by
    simpa only [partialGroup,core14Members,List.length_map] using enum14_length q hq
  have h11 : ((partialGroup q 11).length : Int)=9*(q:Int)-10 := by
    simpa only [partialGroup,core124Members,List.length_map] using enum124_length q hq
  have h13 : ((partialGroup q 13).length : Int)=10*(q:Int)-16 := by
    simpa only [partialGroup,core134Members,List.length_map] using enum134_length q hq
  have h14 : ((partialGroup q 14).length : Int)=6*(q:Int)-6 := by
    simpa only [partialGroup,core234Members,List.length_map] using enum234_length q hq
  have h10 : ((partialGroup q 10).length : Int)=6 := rfl

  have hf : ((fullMembers q).length : Int)=5*(q:Int)*(q:Int)-5*(q:Int)+1 := by
    simpa only [fullMembers,List.length_map] using enumFull_length q hq
  rw [he]
  simp only [List.length_append,Int.natCast_add]
  simp only [Int.mul_assoc] at h6 h7 h9 hf ⊢
  omega
theorem coordinate_two_finite_count (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ T ⟨1,by omega⟩) ∧
      2*(l.length : Int)=17*(q:Int)*(q:Int)+25*(q:Int)-34 := by
  have ht := transfer_enumeration q hq (fun R => R 2) (containingTwoMembers q)
    (containingTwoMembers_nodup q hq) (containingTwoMembers_exact q hq)
  refine ⟨(containingTwoMembers q).map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (lift_at q T 2 (by omega)))
  · simpa only [List.length_map] using containingTwoMembers_length q hq

theorem coordinate_two_strict_two_thirds (q : Nat) (hq : 4≤q) :
    2*((closureMembers q).length : Int)<3*((containingTwoMembers q).length : Int) := by
  have hc := closure_members_length q hq
  have hf := containingTwoMembers_length q hq
  have hs : 0≤(q:Int)*((q:Int)-4) := Int.mul_nonneg (by omega) (by omega)
  have hm : (q:Int)*4=4*(q:Int) := Int.mul_comm (q:Int) 4
  simp only [Int.mul_sub,hm,Int.mul_assoc] at hc hf hs ⊢
  omega

def hasThree (R : Nat → Prop) : Bool := by
  classical
  exact decide (R 3)

def containingThreeMembers (q : Nat) : List (Nat → Prop) := by
  classical
  exact (closureMembers q).filter hasThree

theorem coreCode_bit3_iff_three (R : Nat → Prop) : coreCode R / 4 % 2 = 1 ↔ R 3 := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;>
    by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [coreCode,h1,h2,h3,h4]

theorem filter_partialGroup_three (q k : Nat) (hq : 4≤q) (hk : k∈partialCodes) :
    (partialGroup q k).filter hasThree =
      if k / 4 % 2 = 1 then partialGroup q k else [] := by
  classical
  by_cases ho : k / 4 % 2 = 1
  · rw [ite_eq_left ho]
    apply List.filter_eq_self.mpr
    intro R hR
    unfold hasThree
    apply decide_eq_true
    apply (coreCode_bit3_iff_three R).mp
    rw [((partialGroup_exact q k hq hk R).mp hR).2]
    exact ho
  · rw [ite_eq_right ho]
    apply List.filter_eq_nil_iff.mpr
    intro R hR
    unfold hasThree
    intro hb
    have h1 := of_decide_eq_true hb
    have hh := (coreCode_bit3_iff_three R).mpr h1
    rw [((partialGroup_exact q k hq hk R).mp hR).2] at hh
    exact ho hh

theorem filter_fullMembers_three (q : Nat) (hq : 4≤q) :
    (fullMembers q).filter hasThree = fullMembers q := by
  classical
  apply List.filter_eq_self.mpr
  intro R hR
  unfold hasThree
  exact decide_eq_true ((full_members_exact q hq R).mp hR).2.2.2.1

theorem containingThreeMembers_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈containingThreeMembers q ↔ Generated q R ∧ R 3 := by
  classical
  simp only [containingThreeMembers,List.mem_filter,hasThree,decide_eq_true_eq,closure_members_exact q hq R]

theorem containingThreeMembers_nodup (q : Nat) (hq : 4≤q) :
    (containingThreeMembers q).Nodup := by
  classical
  exact List.Nodup.sublist List.filter_sublist (closure_members_nodup q hq)


theorem containingThreeMembers_length (q : Nat) (hq : 4≤q) :
    2*((containingThreeMembers q).length : Int)=17*(q:Int)*(q:Int)+27*(q:Int)-48 := by
  classical
  have he : containingThreeMembers q = partialGroup q 4 ++ partialGroup q 5 ++ partialGroup q 6 ++ partialGroup q 7 ++ partialGroup q 13 ++ partialGroup q 14 ++ fullMembers q := by
    simp only [containingThreeMembers,closureMembers,partialMembers,partialCodes,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.filter_append]
    rw [filter_partialGroup_three q 0 hq (by decide),filter_partialGroup_three q 1 hq (by decide),filter_partialGroup_three q 2 hq (by decide),filter_partialGroup_three q 3 hq (by decide),filter_partialGroup_three q 4 hq (by decide),filter_partialGroup_three q 5 hq (by decide),filter_partialGroup_three q 6 hq (by decide),filter_partialGroup_three q 7 hq (by decide),filter_partialGroup_three q 9 hq (by decide),filter_partialGroup_three q 10 hq (by decide),filter_partialGroup_three q 11 hq (by decide),filter_partialGroup_three q 13 hq (by decide),filter_partialGroup_three q 14 hq (by decide),filter_fullMembers_three q hq]
    simp only [Nat.reduceDiv,Nat.reduceMod,Nat.reduceEqDiff,ite_true,ite_false,List.nil_append,List.append_nil,List.append_assoc]
  have h0 : ((partialGroup q 0).length : Int)=1 := by
    have hh : (enumSmall 0).length=1 := by simpa only [smallCount] using enumSmall_length 0 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h1 : ((partialGroup q 1).length : Int)=2 := by
    have hh : (enumSmall 1).length=2 := by simpa only [smallCount] using enumSmall_length 1 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h2 : ((partialGroup q 2).length : Int)=1 := by
    have hh : (enumSmall 2).length=1 := by simpa only [smallCount] using enumSmall_length 2 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h3 : ((partialGroup q 3).length : Int)=1 := by
    have hh : (enumSmall 3).length=1 := by simpa only [smallCount] using enumSmall_length 3 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h4 : ((partialGroup q 4).length : Int)=2 := by
    have hh : (enumSmall 4).length=2 := by simpa only [smallCount] using enumSmall_length 4 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h5 : ((partialGroup q 5).length : Int)=5 := by
    have hh : (enumSmall 5).length=5 := by simpa only [smallCount] using enumSmall_length 5 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h6 : ((partialGroup q 6).length : Int)=2*(q:Int)*(q:Int)-(q:Int)-3 := by
    simpa only [partialGroup,core23Members,List.length_map] using enum23_length q hq
  have h7 : 2*((partialGroup q 7).length : Int)=3*(q:Int)*(q:Int)+7*(q:Int)-14 := by
    simpa only [partialGroup,core123Members,List.length_map] using enum123_length q hq
  have h9 : ((partialGroup q 9).length : Int)=3*(q:Int)*(q:Int)-5*(q:Int)+2 := by
    simpa only [partialGroup,core14Members,List.length_map] using enum14_length q hq
  have h11 : ((partialGroup q 11).length : Int)=9*(q:Int)-10 := by
    simpa only [partialGroup,core124Members,List.length_map] using enum124_length q hq
  have h13 : ((partialGroup q 13).length : Int)=10*(q:Int)-16 := by
    simpa only [partialGroup,core134Members,List.length_map] using enum134_length q hq
  have h14 : ((partialGroup q 14).length : Int)=6*(q:Int)-6 := by
    simpa only [partialGroup,core234Members,List.length_map] using enum234_length q hq
  have h10 : ((partialGroup q 10).length : Int)=6 := rfl

  have hf : ((fullMembers q).length : Int)=5*(q:Int)*(q:Int)-5*(q:Int)+1 := by
    simpa only [fullMembers,List.length_map] using enumFull_length q hq
  rw [he]
  simp only [List.length_append,Int.natCast_add]
  simp only [Int.mul_assoc] at h6 h7 h9 hf ⊢
  omega
theorem coordinate_three_finite_count (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ T ⟨2,by omega⟩) ∧
      2*(l.length : Int)=17*(q:Int)*(q:Int)+27*(q:Int)-48 := by
  have ht := transfer_enumeration q hq (fun R => R 3) (containingThreeMembers q)
    (containingThreeMembers_nodup q hq) (containingThreeMembers_exact q hq)
  refine ⟨(containingThreeMembers q).map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (lift_at q T 3 (by omega)))
  · simpa only [List.length_map] using containingThreeMembers_length q hq

theorem coordinate_three_strict_two_thirds (q : Nat) (hq : 4≤q) :
    2*((closureMembers q).length : Int)<3*((containingThreeMembers q).length : Int) := by
  have hc := closure_members_length q hq
  have hf := containingThreeMembers_length q hq
  have hs : 0≤(q:Int)*((q:Int)-4) := Int.mul_nonneg (by omega) (by omega)
  have hm : (q:Int)*4=4*(q:Int) := Int.mul_comm (q:Int) 4
  simp only [Int.mul_sub,hm,Int.mul_assoc] at hc hf hs ⊢
  omega

def hasFour (R : Nat → Prop) : Bool := by
  classical
  exact decide (R 4)

def containingFourMembers (q : Nat) : List (Nat → Prop) := by
  classical
  exact (closureMembers q).filter hasFour

theorem coreCode_bit4_iff_four (R : Nat → Prop) : coreCode R / 8 % 2 = 1 ↔ R 4 := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;>
    by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [coreCode,h1,h2,h3,h4]

theorem filter_partialGroup_four (q k : Nat) (hq : 4≤q) (hk : k∈partialCodes) :
    (partialGroup q k).filter hasFour =
      if k / 8 % 2 = 1 then partialGroup q k else [] := by
  classical
  by_cases ho : k / 8 % 2 = 1
  · rw [ite_eq_left ho]
    apply List.filter_eq_self.mpr
    intro R hR
    unfold hasFour
    apply decide_eq_true
    apply (coreCode_bit4_iff_four R).mp
    rw [((partialGroup_exact q k hq hk R).mp hR).2]
    exact ho
  · rw [ite_eq_right ho]
    apply List.filter_eq_nil_iff.mpr
    intro R hR
    unfold hasFour
    intro hb
    have h1 := of_decide_eq_true hb
    have hh := (coreCode_bit4_iff_four R).mpr h1
    rw [((partialGroup_exact q k hq hk R).mp hR).2] at hh
    exact ho hh

theorem filter_fullMembers_four (q : Nat) (hq : 4≤q) :
    (fullMembers q).filter hasFour = fullMembers q := by
  classical
  apply List.filter_eq_self.mpr
  intro R hR
  unfold hasFour
  exact decide_eq_true ((full_members_exact q hq R).mp hR).2.2.2.2

theorem containingFourMembers_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈containingFourMembers q ↔ Generated q R ∧ R 4 := by
  classical
  simp only [containingFourMembers,List.mem_filter,hasFour,decide_eq_true_eq,closure_members_exact q hq R]

theorem containingFourMembers_nodup (q : Nat) (hq : 4≤q) :
    (containingFourMembers q).Nodup := by
  classical
  exact List.Nodup.sublist List.filter_sublist (closure_members_nodup q hq)


theorem containingFourMembers_length (q : Nat) (hq : 4≤q) :
    2*((containingFourMembers q).length : Int)=16*(q:Int)*(q:Int)+30*(q:Int)-46 := by
  classical
  have he : containingFourMembers q = partialGroup q 9 ++ partialGroup q 10 ++ partialGroup q 11 ++ partialGroup q 13 ++ partialGroup q 14 ++ fullMembers q := by
    simp only [containingFourMembers,closureMembers,partialMembers,partialCodes,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.filter_append]
    rw [filter_partialGroup_four q 0 hq (by decide),filter_partialGroup_four q 1 hq (by decide),filter_partialGroup_four q 2 hq (by decide),filter_partialGroup_four q 3 hq (by decide),filter_partialGroup_four q 4 hq (by decide),filter_partialGroup_four q 5 hq (by decide),filter_partialGroup_four q 6 hq (by decide),filter_partialGroup_four q 7 hq (by decide),filter_partialGroup_four q 9 hq (by decide),filter_partialGroup_four q 10 hq (by decide),filter_partialGroup_four q 11 hq (by decide),filter_partialGroup_four q 13 hq (by decide),filter_partialGroup_four q 14 hq (by decide),filter_fullMembers_four q hq]
    simp only [Nat.reduceDiv,Nat.reduceMod,Nat.reduceEqDiff,ite_true,ite_false,List.nil_append,List.append_nil,List.append_assoc]
  have h0 : ((partialGroup q 0).length : Int)=1 := by
    have hh : (enumSmall 0).length=1 := by simpa only [smallCount] using enumSmall_length 0 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h1 : ((partialGroup q 1).length : Int)=2 := by
    have hh : (enumSmall 1).length=2 := by simpa only [smallCount] using enumSmall_length 1 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h2 : ((partialGroup q 2).length : Int)=1 := by
    have hh : (enumSmall 2).length=1 := by simpa only [smallCount] using enumSmall_length 2 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h3 : ((partialGroup q 3).length : Int)=1 := by
    have hh : (enumSmall 3).length=1 := by simpa only [smallCount] using enumSmall_length 3 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h4 : ((partialGroup q 4).length : Int)=2 := by
    have hh : (enumSmall 4).length=2 := by simpa only [smallCount] using enumSmall_length 4 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h5 : ((partialGroup q 5).length : Int)=5 := by
    have hh : (enumSmall 5).length=5 := by simpa only [smallCount] using enumSmall_length 5 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h6 : ((partialGroup q 6).length : Int)=2*(q:Int)*(q:Int)-(q:Int)-3 := by
    simpa only [partialGroup,core23Members,List.length_map] using enum23_length q hq
  have h7 : 2*((partialGroup q 7).length : Int)=3*(q:Int)*(q:Int)+7*(q:Int)-14 := by
    simpa only [partialGroup,core123Members,List.length_map] using enum123_length q hq
  have h9 : ((partialGroup q 9).length : Int)=3*(q:Int)*(q:Int)-5*(q:Int)+2 := by
    simpa only [partialGroup,core14Members,List.length_map] using enum14_length q hq
  have h11 : ((partialGroup q 11).length : Int)=9*(q:Int)-10 := by
    simpa only [partialGroup,core124Members,List.length_map] using enum124_length q hq
  have h13 : ((partialGroup q 13).length : Int)=10*(q:Int)-16 := by
    simpa only [partialGroup,core134Members,List.length_map] using enum134_length q hq
  have h14 : ((partialGroup q 14).length : Int)=6*(q:Int)-6 := by
    simpa only [partialGroup,core234Members,List.length_map] using enum234_length q hq
  have h10 : ((partialGroup q 10).length : Int)=6 := rfl

  have hf : ((fullMembers q).length : Int)=5*(q:Int)*(q:Int)-5*(q:Int)+1 := by
    simpa only [fullMembers,List.length_map] using enumFull_length q hq
  rw [he]
  simp only [List.length_append,Int.natCast_add]
  simp only [Int.mul_assoc] at h6 h7 h9 hf ⊢
  omega
theorem coordinate_four_finite_count (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ T ⟨3,by omega⟩) ∧
      2*(l.length : Int)=16*(q:Int)*(q:Int)+30*(q:Int)-46 := by
  have ht := transfer_enumeration q hq (fun R => R 4) (containingFourMembers q)
    (containingFourMembers_nodup q hq) (containingFourMembers_exact q hq)
  refine ⟨(containingFourMembers q).map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (lift_at q T 4 (by omega)))
  · simpa only [List.length_map] using containingFourMembers_length q hq

theorem coordinate_four_strict_two_thirds (q : Nat) (hq : 4≤q) :
    2*((closureMembers q).length : Int)<3*((containingFourMembers q).length : Int) := by
  have hc := closure_members_length q hq
  have hf := containingFourMembers_length q hq
  have hs : 0≤(q:Int)*((q:Int)-4) := Int.mul_nonneg (by omega) (by omega)
  have hm : (q:Int)*4=4*(q:Int) := Int.mul_comm (q:Int) 4
  simp only [Int.mul_sub,hm,Int.mul_assoc] at hc hf hs ⊢
  omega

#print axioms coreCode_bit2_iff_two
#print axioms filter_partialGroup_two
#print axioms filter_fullMembers_two
#print axioms containingTwoMembers_exact
#print axioms containingTwoMembers_nodup
#print axioms containingTwoMembers_length
#print axioms coordinate_two_finite_count
#print axioms coordinate_two_strict_two_thirds
#print axioms coreCode_bit3_iff_three
#print axioms filter_partialGroup_three
#print axioms filter_fullMembers_three
#print axioms containingThreeMembers_exact
#print axioms containingThreeMembers_nodup
#print axioms containingThreeMembers_length
#print axioms coordinate_three_finite_count
#print axioms coordinate_three_strict_two_thirds
#print axioms coreCode_bit4_iff_four
#print axioms filter_partialGroup_four
#print axioms filter_fullMembers_four
#print axioms containingFourMembers_exact
#print axioms containingFourMembers_nodup
#print axioms containingFourMembers_length
#print axioms coordinate_four_finite_count
#print axioms coordinate_four_strict_two_thirds
end
end LuRazClosure
