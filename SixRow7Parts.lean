import SixRow6Exact
import RowInfluence
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem restricted6_points (q i : Nat) (hq : 4≤q) (hi : Restricted6 q i) :
    ¬LuRazSixRow.BRow q i 1 ∧ ¬LuRazSixRow.BRow q i 4 ∧
    (LuRazSixRow.BRow q i 2 → LuRazSixRow.BRow q i 3) := by
  rcases hi with hi|hi|hi|⟨p,hp,hph,hi⟩ <;> subst i
  · simp only [c6_source q 1 hq,c6_source q 4 hq,c6_source q 2 hq,c6_source q 3 hq,C6,I]
    omega
  · simp only [e6_source q 1 hq,e6_source q 4 hq,e6_source q 2 hq,e6_source q 3 hq,E6,I]
    simp_all <;> omega
  · simp only [b0_source q 1 hq,b0_source q 4 hq,b0_source q 2 hq,b0_source q 3 hq,LuRazClosure.BRow,I]
    omega
  · have hp' := hp
    unfold P at hp'
    simp only [l6_source q p 1 hq hp hph,l6_source q p 4 hq hp hph,l6_source q p 2 hq hp hph,l6_source q p 3 hq hp hph,LRow,LNormal,I,beta]
    repeat first | omega | (simp_all <;> omega) | split

theorem no_four_source7 (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h4 : ¬LuRazSixRow.BRow q i 4) :
    Restricted6 q i ∨ i=4*q+2 ∨ i=2 ∨ i=4*q-1 := by
  by_cases h1 : ¬LuRazSixRow.BRow q i 1
  · exact Or.inl (no_one_four_source6 q i hq hi h1 h4)
  · have hh : LuRazSixRow.BRow q i 1 := Classical.not_not.mp h1
    by_cases h : i=1
    · subst i
      exact False.elim (h4 ((LuRazSixRow.unchanged_row q 1 4 (by unfold LuRazSixRow.Special; omega)).mpr
        ((LuRazFourRow.row_one q 4 hq).mpr (by omega))))
    by_cases h2 : i=2
    · exact Or.inr (Or.inr (Or.inl h2))
    by_cases he : i=4
    · subst i; rw [e6_source q 1 hq] at hh; unfold E6 I at hh; omega
    by_cases hk : i=2*q+2
    · subst i; exact False.elim (h4 ((LuRazSixRow.row_middle q 4 hq).mpr (by omega)))
    by_cases hl : i=4*q-1
    · exact Or.inr (Or.inr (Or.inr hl))
    by_cases hc : i=4*q
    · subst i; rw [c6_source q 1 hq] at hh; unfold C6 I at hh; omega
    have ho : OrdinaryLarge q i := ⟨h,h2,he,hk,hl,hc⟩
    have hold1 := (large_ordinary q i 1 ho).mp hh
    have hold4 : ¬Row q i 4 := fun hr=>h4 ((large_ordinary q i 4 ho).mpr hr)
    have hold := LuRazRowInfluence.one_without_four_source q i hq hold1 hold4
    exact Or.inr (Or.inl (hold.resolve_left he))

def Image7 (q : Nat) (z : NF6) (a b c : Prop) (e : Nat) : Prop :=
  z.eval q e ∨ (a ∧ ARow q e) ∨ (b ∧ Z7 q e) ∨ (c ∧ H7 q e)

theorem core7_image (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : Generated q R) (hc : Core123 R) :
    ∃z : NF6,z.Valid q ∧ ∃a b c : Prop,(a∨b∨c) ∧ ∀e,R e ↔ Image7 q z a b c e := by
  classical
  obtain ⟨l,_,hv,he⟩ := hg
  have hall : ∀i∈l,Restricted6 q i ∨ i=4*q+2 ∨ i=2 ∨ i=4*q-1 := by
    intro i hi
    exact no_four_source7 q i hq (hv i hi) (fun hh=>hc.2.2.2 ((he 4).mp ⟨i,hi,hh⟩))
  let k := l.filter (fun i=>decide (Restricted6 q i))
  have hkm (i : Nat) : i∈k ↔ i∈l ∧ Restricted6 q i := by simp only [k,List.mem_filter,decide_eq_true_eq]
  obtain ⟨i,hi,hi2⟩ := (he 2).mpr hc.2.1
  have hir : Restricted6 q i := by
    rcases hall i hi with h|h|h|h
    · exact h
    · subst i; rw [a0_source q 2 hq] at hi2; unfold ARow I at hi2; omega
    · subst i; rw [z7_source q 2 hq] at hi2; unfold Z7 I at hi2; omega
    · subst i; rw [h7_source q 2 hq] at hi2; unfold H7 I at hi2; omega
  have hkin : i∈k := (hkm i).mpr ⟨hi,hir⟩
  have hkn : k≠[] := fun h=>List.not_mem_nil (h ▸ hkin)
  have hbase : Generated q (ListUnion (LuRazSixRow.BRow q) k) :=
    ⟨k,hkn,fun j hj=>hv j ((hkm j).mp hj).1,fun _=>Iff.rfl⟩
  have hcore : Core23 (ListUnion (LuRazSixRow.BRow q) k) := by
    refine ⟨?_,⟨i,hkin,hi2⟩,⟨i,hkin,(restricted6_points q i hq hir).2.2 hi2⟩,?_⟩
    · rintro ⟨j,hj,hj1⟩
      exact (restricted6_points q j hq ((hkm j).mp hj).2).1 hj1
    · rintro ⟨j,hj,hj4⟩
      exact (restricted6_points q j hq ((hkm j).mp hj).2).2.1 hj4
  obtain ⟨z,hz,hzR⟩ := core6_normal q hq _ hbase hcore
  have hflags : (4*q+2∈l) ∨ (2∈l) ∨ (4*q-1∈l) := by
    obtain ⟨j,hj,hj1⟩ := (he 1).mpr hc.1
    rcases hall j hj with hh|hh|hh|hh
    · exact False.elim ((restricted6_points q j hq hh).1 hj1)
    · exact Or.inl (hh ▸ hj)
    · exact Or.inr (Or.inl (hh ▸ hj))
    · exact Or.inr (Or.inr (hh ▸ hj))
  refine ⟨z,hz,(4*q+2∈l),(2∈l),(4*q-1∈l),hflags,?_⟩
  intro e
  constructor
  · intro hr
    obtain ⟨j,hj,hje⟩ := (he e).mpr hr
    rcases hall j hj with hh|hh|hh|hh
    · exact Or.inl ((hzR e).mp ⟨j,(hkm j).mpr ⟨hj,hh⟩,hje⟩)
    · subst j; exact Or.inr (Or.inl ⟨hj,(a0_source q e hq).mp hje⟩)
    · subst j; exact Or.inr (Or.inr (Or.inl ⟨hj,(z7_source q e hq).mp hje⟩))
    · subst j; exact Or.inr (Or.inr (Or.inr ⟨hj,(h7_source q e hq).mp hje⟩))
  · intro hr
    rcases hr with hr|hr|hr|hr
    · obtain ⟨j,hj,hje⟩ := (hzR e).mpr hr
      exact (he e).mp ⟨j,((hkm j).mp hj).1,hje⟩
    · exact (he e).mp ⟨4*q+2,hr.1,(a0_source q e hq).mpr hr.2⟩
    · exact (he e).mp ⟨2,hr.1,(z7_source q e hq).mpr hr.2⟩
    · exact (he e).mp ⟨4*q-1,hr.1,(h7_source q e hq).mpr hr.2⟩
end LuRazSixRowClosure
