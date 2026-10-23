import LuRazStructure
import LuRazFrequency
import LuRazSizes

namespace LuRazParametric
open RazReimerPredicates
noncomputable section

theorem S_nontrivial (q : Nat) (hq : 3 ≤ q) : Nontrivial (S q) := by
  refine ⟨0,(⟨0,by omega⟩ : Fin (4*q)),?_⟩
  change Row q 0 1
  apply (row_case_0 q 0 1 hq rfl).mpr
  omega

theorem row_one_last_implies_three (q i : Nat) (hq : 3 ≤ q)
    (h1 : Row q i 1) (hn : Row q i (4*q)) : Row q i 3 := by
  have hh : i = 0 ∨ i = 2 ∨ i = 4 := by
    unfold Row at h1 hn
    omega
  rcases hh with h | h | h
  · apply (row_case_0 q i 3 hq h).mpr; omega
  · apply (row_case_2 q i 3 hq h).mpr; omega
  · apply (row_case_4 q i 3 hq h).mpr; omega

theorem not_union_closed (q : Nat) (hq : 3 ≤ q) : ¬ UnionClosed (S q) := by
  intro hu
  let a : Fin (4*q+3) := ⟨4*q+1,by omega⟩
  let b : Fin (4*q+3) := ⟨4*q+2,by omega⟩
  let E1 : Fin (4*q) := ⟨0,by omega⟩
  let E3 : Fin (4*q) := ⟨2,by omega⟩
  let EN : Fin (4*q) := ⟨4*q-1,by omega⟩
  have hn : 4*q-1+1 = 4*q := by omega
  obtain ⟨k,hk⟩ := hu a b
  have hb1 : S q b E1 := by
    change Row q (4*q+2) 1
    apply (row_case_15 q (4*q+2) 1 hq rfl).mpr
    omega
  have haN : S q a EN := by
    change Row q (4*q+1) (4*q-1+1)
    rw [hn]
    apply (row_case_14 q (4*q+1) (4*q) hq rfl).mpr
    omega
  have hk1 : Row q k.val 1 := (hk E1).mpr (Or.inr hb1)
  have hkN := (hk EN).mpr (Or.inl haN)
  change Row q k.val (4*q-1+1) at hkN
  rw [hn] at hkN
  have hk3 : S q k E3 := row_one_last_implies_three q k.val hq hk1 hkN
  have ha3 : ¬ S q a E3 := by
    change ¬ Row q (4*q+1) 3
    rw [row_case_14 q (4*q+1) 3 hq rfl]
    omega
  have hb3 : ¬ S q b E3 := by
    change ¬ Row q (4*q+2) 3
    rw [row_case_15 q (4*q+2) 3 hq rfl]
    omega
  exact ((hk E3).mp hk3).elim ha3 hb3

-- Complete all-parameter construction theorem. It makes no assertion about
-- the separate conjecture for the exact size of the generated closure.
theorem completed_construction (q : Nat) (hq : 3 ≤ q) :
    ReimerCondition (S q) ∧ Nontrivial (S q) ∧
    (∀ e, frequency (S q) e = 2*q+1) ∧
    ¬ HasAbundantElement (S q) ∧ ¬ UnionClosed (S q) ∧
    (∀ i, q-1 ≤ setSize q i) ∧ (∃ i, setSize q i = q-1) := by
  exact ⟨reimer_condition q hq,S_nontrivial q hq,predicate_frequencies q hq,
    no_abundant_element q hq,not_union_closed q hq,minimum_size_lower q hq,
    ⟨⟨4*q+1,by omega⟩,minimum_size_attained q hq⟩⟩

-- The parameter x is exactly the smallest member size, as in the paper.
-- Ground-set size: 4*(x+1)=4*x+4; number of distinct members: 4*x+7.
theorem completed_for_every_x (x : Nat) (hx : 2 ≤ x) :
    ReimerCondition (S (x+1)) ∧ Nontrivial (S (x+1)) ∧
    (∀ e, frequency (S (x+1)) e = 2*x+3) ∧
    ¬ HasAbundantElement (S (x+1)) ∧ ¬ UnionClosed (S (x+1)) ∧
    (∀ i, x ≤ setSize (x+1) i) ∧ (∃ i, setSize (x+1) i = x) := by
  obtain ⟨hR,hN,hF,hA,hU,hL,hE⟩ := completed_construction (x+1) (by omega)
  refine ⟨hR,hN,?_,hA,hU,?_,?_⟩
  · intro e
    have h := hF e
    omega
  · intro i
    have h := hL i
    omega
  · obtain ⟨i,hi⟩ := hE
    exact ⟨i,by omega⟩

end
end LuRazParametric
