import LuRazCore134Results
namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

noncomputable def coreCode (R : Nat → Prop) : Nat := by
  classical
  exact (if R 1 then 1 else 0)+(if R 2 then 2 else 0)+(if R 3 then 4 else 0)+(if R 4 then 8 else 0)
def CoreFull (R : Nat → Prop) : Prop := R 1 ∧ R 2 ∧ R 3 ∧ R 4

def partialCodes : List Nat := [0,1,2,3,4,5,6,7,9,10,11,13,14]

theorem row_four_implies_one_or_two (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h4 : LuRazParametric.Row q i 4) : LuRazParametric.Row q i 1 ∨ LuRazParametric.Row q i 2 := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
      (5≤i ∧ i≤q+2) ∨ (q+3≤i ∧ i≤2*q) ∨ i=2*q+1 ∨ i=2*q+2 ∨ i=2*q+3 ∨
      (2*q+4≤i ∧ i≤3*q) ∨ i=3*q+1 ∨ (3*q+2≤i ∧ i+1≤4*q) ∨
      i=4*q ∨ i=4*q+1 ∨ i=4*q+2 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl ((LuRazParametric.row_case_0 q i 1 (by omega) h).mpr (by omega))
  · have hh := (LuRazParametric.row_case_1 q i 4 (by omega) h).mp h4
    omega
  · exact Or.inl ((LuRazParametric.row_case_2 q i 1 (by omega) h).mpr (by omega))
  · exact Or.inl ((LuRazParametric.row_case_3 q i 1 (by omega) h).mpr (by omega))
  · have hh := (LuRazParametric.row_case_4 q i 4 (by omega) h).mp h4
    omega
  · exact Or.inl ((LuRazParametric.row_case_5 q i 1 (by omega) h).mpr (by omega))
  · exact Or.inl ((LuRazParametric.row_case_6 q i 1 (by omega) h).mpr (by omega))
  · exact Or.inr ((LuRazParametric.row_case_7 q i 2 (by omega) h).mpr (by omega))
  · exact Or.inr ((LuRazParametric.row_case_8 q i 2 (by omega) h).mpr (by omega))
  · have hh := (LuRazParametric.row_case_9 q i 4 (by omega) h).mp h4
    omega
  · have hh := (LuRazParametric.row_case_10 q i 4 (by omega) h).mp h4
    omega
  · have hh := (LuRazParametric.row_case_11 q i 4 (by omega) h).mp h4
    omega
  · have hh := (LuRazParametric.row_case_12 q i 4 (by omega) h).mp h4
    omega
  · have hh := (LuRazParametric.row_case_13 q i 4 (by omega) h).mp h4
    omega
  · have hh := (LuRazParametric.row_case_14 q i 4 (by omega) h).mp h4
    omega
  · have hh := (LuRazParametric.row_case_15 q i 4 (by omega) h).mp h4
    omega

theorem generated_four_implies_one_or_two (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hg : Generated q R) :
    R 4 → R 1 ∨ R 2 := by
  obtain ⟨l,_,hv,he⟩ := hg
  intro h4
  obtain ⟨i,hi,hi4⟩ := (he 4).mpr h4
  rcases row_four_implies_one_or_two q i hq (hv i hi) hi4 with h1 | h2
  · exact Or.inl ((he 1).mp ⟨i,hi,h1⟩)
  · exact Or.inr ((he 2).mp ⟨i,hi,h2⟩)

theorem partialCodes_iff_not_full (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hg : Generated q R) :
    coreCode R∈partialCodes ↔ ¬CoreFull R := by
  classical
  have hh := generated_four_implies_one_or_two q hq R hg
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;> by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp_all [coreCode,partialCodes,CoreFull]

theorem small_core_code (k : Nat) (hk : k≤5) (R : Nat → Prop) : CoreSmallAt k R ↔ coreCode R=k := by
  classical
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with h | h | h | h | h | h <;> subst k <;>
    by_cases h1 : R 1 <;> by_cases h2 : R 2 <;> by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [CoreSmallAt,coreCode,h1,h2,h3,h4]

theorem core23_code (R : Nat → Prop) : Core23 R ↔ coreCode R=6 := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;> by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [Core23,coreCode,h1,h2,h3,h4]

theorem core123_code (R : Nat → Prop) : Core123 R ↔ coreCode R=7 := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;> by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [Core123,coreCode,h1,h2,h3,h4]

theorem core14_code (R : Nat → Prop) : Core14 R ↔ coreCode R=9 := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;> by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [Core14,coreCode,h1,h2,h3,h4]

theorem core24_code (R : Nat → Prop) : Core24 R ↔ coreCode R=10 := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;> by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [Core24,coreCode,h1,h2,h3,h4]

theorem core124_code (R : Nat → Prop) : Core124 R ↔ coreCode R=11 := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;> by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [Core124,coreCode,h1,h2,h3,h4]

theorem core134_code (R : Nat → Prop) : Core134 R ↔ coreCode R=13 := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;> by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [Core134,coreCode,h1,h2,h3,h4]

theorem core234_code (R : Nat → Prop) : Core234 R ↔ coreCode R=14 := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;> by_cases h3 : R 3 <;> by_cases h4 : R 4 <;>
    simp [Core234,coreCode,h1,h2,h3,h4]

def partialGroup (q : Nat) : Nat → List (Nat → Prop)
  | 0 => smallMembers q 0
  | 1 => smallMembers q 1
  | 2 => smallMembers q 2
  | 3 => smallMembers q 3
  | 4 => smallMembers q 4
  | 5 => smallMembers q 5
  | 6 => core23Members q
  | 7 => core123Members q
  | 9 => core14Members q
  | 10 => members24 q
  | 11 => core124Members q
  | 13 => core134Members q
  | 14 => core234Members q
  | _ => []
noncomputable def partialMembers (q : Nat) : List (Nat → Prop) := partialCodes.flatMap (partialGroup q)

theorem partialGroup_exact (q k : Nat) (hq : 4≤q) (hk : k∈partialCodes) (R : Nat → Prop) :
    R∈partialGroup q k ↔ Generated q R ∧ coreCode R=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=13 ∨ k=14 := by simpa [partialCodes] using hk
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst k
  · exact (small_members_exact q 0 hq R).trans (and_congr Iff.rfl (small_core_code 0 (by decide) R))
  · exact (small_members_exact q 1 hq R).trans (and_congr Iff.rfl (small_core_code 1 (by decide) R))
  · exact (small_members_exact q 2 hq R).trans (and_congr Iff.rfl (small_core_code 2 (by decide) R))
  · exact (small_members_exact q 3 hq R).trans (and_congr Iff.rfl (small_core_code 3 (by decide) R))
  · exact (small_members_exact q 4 hq R).trans (and_congr Iff.rfl (small_core_code 4 (by decide) R))
  · exact (small_members_exact q 5 hq R).trans (and_congr Iff.rfl (small_core_code 5 (by decide) R))
  · exact (core23_members_exact q hq R).trans (and_congr Iff.rfl (core23_code R))
  · exact (core123_members_exact q hq R).trans (and_congr Iff.rfl (core123_code R))
  · exact (core14_members_exact q hq R).trans (and_congr Iff.rfl (core14_code R))
  · exact (members24_exact q hq R).trans (and_congr Iff.rfl (core24_code R))
  · exact (core124_members_exact q hq R).trans (and_congr Iff.rfl (core124_code R))
  · exact (core134_members_exact q hq R).trans (and_congr Iff.rfl (core134_code R))
  · exact (core234_members_exact q hq R).trans (and_congr Iff.rfl (core234_code R))

theorem partialGroup_nodup (q k : Nat) (hq : 4≤q) (hk : k∈partialCodes) : (partialGroup q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=13 ∨ k=14 := by simpa [partialCodes] using hk
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst k
  · exact small_members_nodup q 0 hq
  · exact small_members_nodup q 1 hq
  · exact small_members_nodup q 2 hq
  · exact small_members_nodup q 3 hq
  · exact small_members_nodup q 4 hq
  · exact small_members_nodup q 5 hq
  · exact core23_members_nodup q hq
  · exact core123_members_nodup q hq
  · exact core14_members_nodup q hq
  · exact members24_nodup q hq
  · exact core124_members_nodup q hq
  · exact core134_members_nodup q hq
  · exact core234_members_nodup q hq

theorem partialMembers_nodup (q : Nat) (hq : 4≤q) : (partialMembers q).Nodup := by
  apply nodup_flatMap_separated _ _ (by decide)
  · intro k hk
    exact partialGroup_nodup q k hq hk
  · intro k hk j hj R hR T hT heq
    have hr := ((partialGroup_exact q k hq hk R).mp hR).2
    have ht := ((partialGroup_exact q j hq hj T).mp hT).2
    subst T
    omega

theorem partialMembers_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈partialMembers q ↔ Generated q R ∧ ¬CoreFull R := by
  constructor
  · intro hR
    obtain ⟨k,hk,hr⟩ := List.mem_flatMap.mp hR
    have he := (partialGroup_exact q k hq hk R).mp hr
    refine ⟨he.1,(partialCodes_iff_not_full q hq R he.1).mp ?_⟩
    rw [he.2]
    exact hk
  · rintro ⟨hg,hn⟩
    have hm := (partialCodes_iff_not_full q hq R hg).mpr hn
    exact List.mem_flatMap.mpr ⟨coreCode R,hm,(partialGroup_exact q (coreCode R) hq hm R).mpr ⟨hg,rfl⟩⟩
end LuRazClosure
