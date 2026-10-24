import SixRowLargeDifferenceAt
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem new_source_two_horn (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h2 : LuRazSixRow.BRow q i 2) : LuRazSixRow.BRow q i 3 ∨ LuRazSixRow.BRow q i 4 := by
  classical
  by_cases h4 : LuRazSixRow.BRow q i 4
  · exact Or.inr h4
  · left
    rcases no_four_source7 q i hq hi h4 with hr|hr|hr|hr
    · exact (restricted6_points q i hq hr).2.2 h2
    · subst i; rw [a0_source q 2 hq] at h2; unfold ARow I at h2; omega
    · subst i; rw [z7_source q 2 hq] at h2; unfold Z7 I at h2; omega
    · subst i; rw [h7_source q 2 hq] at h2; unfold H7 I at h2; omega

theorem new_source_four_horn (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h4 : LuRazSixRow.BRow q i 4) : LuRazSixRow.BRow q i 1 ∨ LuRazSixRow.BRow q i 2 := by
  by_cases hd : i=1
  · subst i; right
    rw [LuRazSixRow.unchanged_row q 1 2 (by unfold LuRazSixRow.Special; omega),LuRazFourRow.row_one q 2 hq]
    omega
  by_cases hz : i=2
  · subst i; left; rw [z7_source q 1 hq]; unfold Z7; omega
  by_cases he : i=4
  · subst i; right; rw [e6_source q 2 hq]; unfold E6; omega
  by_cases hm : i=2*q+2
  · subst i; right; rw [LuRazSixRow.row_middle q 2 hq]; omega
  by_cases hl : i=4*q-1
  · subst i; left; rw [h7_source q 1 hq]; unfold H7; omega
  by_cases hc : i=4*q
  · subst i; rw [c6_source q 4 hq] at h4; unfold C6 I at h4; omega
  have ho : OrdinaryLarge q i := ⟨hd,hz,he,hm,hl,hc⟩
  have hold := row_four_implies_one_or_two q i hq hi ((large_ordinary q i 4 ho).mp h4)
  exact hold.elim (fun h=>Or.inl ((large_ordinary q i 1 ho).mpr h))
    (fun h=>Or.inr ((large_ordinary q i 2 ho).mpr h))

theorem new_generated_horns (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hg : Generated q R) :
    (R 2 → R 3 ∨ R 4) ∧ (R 4 → R 1 ∨ R 2) := by
  constructor
  · intro h2
    obtain ⟨i,hi,hr,hs⟩ := point_covered q hg h2
    exact (new_source_two_horn q i hq hi hr).elim (fun h=>Or.inl (hs _ h)) (fun h=>Or.inr (hs _ h))
  · intro h4
    obtain ⟨i,hi,hr,hs⟩ := point_covered q hg h4
    exact (new_source_four_horn q i hq hi hr).elim (fun h=>Or.inl (hs _ h)) (fun h=>Or.inr (hs _ h))

theorem new_thin_empty (q k : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hk : k=2 ∨ k=3 ∨ k=8 ∨ k=12) (hc : CoreMask k R) : ¬Generated q R := by
  intro hg
  have hh := new_generated_horns q hq R hg
  rcases hk with rfl|rfl|rfl|rfl
  · have h : ¬R 1 ∧ R 2 ∧ ¬R 3 ∧ ¬R 4 := by simpa [CoreMask] using hc
    exact (hh.1 h.2.1).elim h.2.2.1 h.2.2.2
  · have h : R 1 ∧ R 2 ∧ ¬R 3 ∧ ¬R 4 := by simpa [CoreMask] using hc
    exact (hh.1 h.2.1).elim h.2.2.1 h.2.2.2
  · have h : ¬R 1 ∧ ¬R 2 ∧ ¬R 3 ∧ R 4 := by simpa [CoreMask] using hc
    exact (hh.2 h.2.2.2).elim h.1 h.2.1
  · have h : ¬R 1 ∧ ¬R 2 ∧ R 3 ∧ R 4 := by simpa [CoreMask] using hc
    exact (hh.2 h.2.2.2).elim h.1 h.2.1

theorem thin_no_added (q k : Nat) (R : Nat→Prop) (hk : k=2 ∨ k=3 ∨ k=8 ∨ k=12) : ¬AddedAt q k R := by
  rintro ⟨f,_,ht,_⟩
  cases f <;> simp only [AddedForm.core] at ht <;> omega
theorem core8_no_removed (q : Nat) (R : Nat→Prop) : ¬RemovedAt q 8 R := by
  rintro ⟨f,_,ht,_⟩
  cases f <;> simp only [RemovedForm.core] at ht <;> omega

theorem old2_normal (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 2 R) :
    LuRazThreeRow.Generated q R ↔ ∀e,RemovedForm.eval q .r2 e ↔ R e := by
  have hs : ¬R 1 ∧ R 2 ∧ ¬R 3 ∧ ¬R 4 := by simpa [CoreMask] using hc
  have hcsmall : CoreSmallAt 2 R := by simpa [CoreMask,CoreSmallAt] using hc
  constructor
  · intro hv
    have ho := (LuRazThreeRow.no_three_unchanged q hq R hs.2.2.1).mp hv
    have hm := (small_members_exact q 2 hq R).mpr ⟨ho,hcsmall⟩
    obtain ⟨z,hz,he⟩ := List.mem_map.mp hm
    have ht := (enumSmall_exact 2 z).mp hz
    have hzz : z=NFSmall.dOnly := by cases z <;> simp_all [NFSmall.tag]
    subst z
    intro e
    simpa only [RemovedForm.eval,NFSmall.eval,DRow] using iff_of_eq (congrFun he e)
  · intro he
    apply (LuRazThreeRow.no_three_unchanged q hq R hs.2.2.1).mpr
    apply LuRazClosure.generated_congr q (NFSmall.generated q hq .dOnly)
    exact fun e=>by simpa only [RemovedForm.eval,NFSmall.eval,DRow] using he e

theorem old3_normal (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 3 R) :
    LuRazThreeRow.Generated q R ↔ ∀e,RemovedForm.eval q .r3 e ↔ R e := by
  have hs : R 1 ∧ R 2 ∧ ¬R 3 ∧ ¬R 4 := by simpa [CoreMask] using hc
  have hcsmall : CoreSmallAt 3 R := by simpa [CoreMask,CoreSmallAt] using hc
  constructor
  · intro hv
    have ho := (LuRazThreeRow.no_three_unchanged q hq R hs.2.2.1).mp hv
    have hm := (small_members_exact q 3 hq R).mpr ⟨ho,hcsmall⟩
    obtain ⟨z,hz,he⟩ := List.mem_map.mp hm
    have ht := (enumSmall_exact 3 z).mp hz
    have hzz : z=NFSmall.ad := by cases z <;> simp_all [NFSmall.tag]
    subst z
    intro e
    refine Iff.trans ?_ (iff_of_eq (congrFun he e))
    simp only [RemovedForm.eval,NFSmall.eval,ARow,DRow,A,I]; omega
  · intro he
    apply (LuRazThreeRow.no_three_unchanged q hq R hs.2.2.1).mpr
    apply LuRazClosure.generated_congr q (NFSmall.generated q hq .ad)
    intro e
    refine Iff.trans ?_ (he e)
    simp only [RemovedForm.eval,NFSmall.eval,ARow,DRow,A,I]; omega

theorem removed_at2_normal (q : Nat) (R : Nat→Prop) : RemovedAt q 2 R ↔ ∀e,RemovedForm.eval q .r2 e ↔ R e := by
  constructor
  · rintro ⟨f,_,ht,he⟩
    cases f <;> simp only [RemovedForm.core] at ht
    case r2 => exact he
    all_goals contradiction
  · intro he; exact ⟨.r2,True.intro,rfl,he⟩
theorem removed_at3_normal (q : Nat) (R : Nat→Prop) : RemovedAt q 3 R ↔ ∀e,RemovedForm.eval q .r3 e ↔ R e := by
  constructor
  · rintro ⟨f,_,ht,he⟩
    cases f <;> simp only [RemovedForm.core] at ht
    case r3 => exact he
    all_goals contradiction
  · intro he; exact ⟨.r3,True.intro,rfl,he⟩

theorem old8_empty (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 8 R) : ¬LuRazThreeRow.Generated q R := by
  have hs : ¬R 1 ∧ ¬R 2 ∧ ¬R 3 ∧ R 4 := by simpa [CoreMask] using hc
  intro hv
  have ho := (LuRazThreeRow.no_three_unchanged q hq R hs.2.2.1).mp hv
  obtain ⟨l,_,hv,he⟩ := ho
  obtain ⟨i,hi,hr⟩ := (he 4).mpr hs.2.2.2
  have hh := row_four_implies_one_or_two q i hq (hv i hi) hr
  exact hh.elim (fun h=>hs.1 ((he 1).mp ⟨i,hi,h⟩)) (fun h=>hs.2.1 ((he 2).mp ⟨i,hi,h⟩))

theorem old12_removed (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 12 R) :
    LuRazThreeRow.Generated q R ↔ RemovedAt q 12 R := by
  have hs : LuRazThreeRow.Core12 R := by simpa [CoreMask,LuRazThreeRow.Core12] using hc
  constructor
  · intro hv
    obtain ⟨c,b,he⟩ := LuRazThreeRow.core12_mix q hq R hv hs
    classical
    by_cases hc0 : c <;> by_cases hb0 : b
    · refine ⟨.r12 3,by change 3≤3; omega,rfl,?_⟩
      intro e; refine Iff.trans ?_ (he e).symm
      simp only [RemovedForm.eval,Lp,C,B,LuRazThreeRow.Mix12,LuRazThreeRow.LPrime,CRow,BRow,hc0,hb0,true_and,false_and,or_false,false_or,I] <;> simp_all <;> omega
    · refine ⟨.r12 2,by change 2≤3; omega,rfl,?_⟩
      intro e; refine Iff.trans ?_ (he e).symm
      simp only [RemovedForm.eval,Lp,C,B,LuRazThreeRow.Mix12,LuRazThreeRow.LPrime,CRow,BRow,hc0,hb0,true_and,false_and,or_false,false_or,I] <;> simp_all <;> omega
    · refine ⟨.r12 1,by change 1≤3; omega,rfl,?_⟩
      intro e; refine Iff.trans ?_ (he e).symm
      simp only [RemovedForm.eval,Lp,C,B,LuRazThreeRow.Mix12,LuRazThreeRow.LPrime,CRow,BRow,hc0,hb0,true_and,false_and,or_false,false_or,I] <;> simp_all <;> omega
    · refine ⟨.r12 0,by change 0≤3; omega,rfl,?_⟩
      intro e; refine Iff.trans ?_ (he e).symm
      simp only [RemovedForm.eval,Lp,C,B,LuRazThreeRow.Mix12,LuRazThreeRow.LPrime,CRow,BRow,hc0,hb0,true_and,false_and,or_false,false_or,I] <;> simp_all <;> omega
  · rintro ⟨f,hf,ht,he⟩
    cases f <;> simp only [RemovedForm.core] at ht
    case r12 k =>
      apply LuRazThreeRow.generated_congr q (LuRazThreeRow.mix12_generated q hq (2≤k) (k=1 ∨ k=3))
      intro e; refine Iff.trans ?_ (he e)
      simp only [LuRazThreeRow.Mix12,LuRazThreeRow.LPrime,CRow,BRow,RemovedForm.eval,Lp,C,B,I]
      omega
    all_goals contradiction
end LuRazSixRowClosure
