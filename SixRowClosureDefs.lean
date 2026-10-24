import SixRowResults
import VariantGlobalDifference

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric LuRazSixRow
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Nonempty unions of the modified rows, with the ordinary set interpretation. -/
def Generated (q : Nat) (R : Nat → Prop) : Prop :=
  ∃ l : List Nat, l ≠ [] ∧ (∀ i ∈ l, i ≤ 4*q+2) ∧
    ∀ e, ListUnion (BRow q) l e ↔ R e

theorem generated_row (q i : Nat) (hi : i ≤ 4*q+2) : Generated q (BRow q i) := by
  refine ⟨[i],by simp,?_,?_⟩
  · intro j hj
    have hji : j=i := by simpa using hj
    subst j; exact hi
  · intro e
    constructor
    · rintro ⟨j,hj,he⟩
      have hji : j=i := by simpa using hj
      subst j; exact he
    · exact fun he => ⟨i,by simp,he⟩

theorem generated_congr (q : Nat) {R T : Nat → Prop}
    (h : Generated q R) (he : ∀ e, R e ↔ T e) : Generated q T := by
  obtain ⟨l,hn,hv,hR⟩ := h
  exact ⟨l,hn,hv,fun e => (hR e).trans (he e)⟩

theorem generated_join (q : Nat) {R T : Nat → Prop}
    (hR : Generated q R) (hT : Generated q T) : Generated q (fun e => R e ∨ T e) := by
  obtain ⟨l,hn,hv,hR⟩ := hR
  obtain ⟨k,_,hkv,hT⟩ := hT
  refine ⟨l++k,?_,?_,?_⟩
  · exact fun h => hn (List.append_eq_nil_iff.mp h).1
  · intro i hi
    exact (List.mem_append.mp hi).elim (hv i) (hkv i)
  · intro e
    rw [listUnion_append,hR,hT]

theorem generated_optional (q : Nat) {R T : Nat → Prop}
    (hR : Generated q R) (hT : Generated q T) (p : Prop) :
    Generated q (fun e => R e ∨ (p ∧ T e)) := by
  classical
  by_cases hp : p
  · exact generated_congr q (generated_join q hR hT) (by intro e; simp [hp])
  · exact generated_congr q hR (by intro e; simp [hp])

/-- Every point of a generated set is covered by a source row contained in that set. -/
theorem point_covered (q : Nat) {R : Nat → Prop} (h : Generated q R) {e : Nat} (he : R e) :
    ∃ i, i ≤ 4*q+2 ∧ BRow q i e ∧ (∀ f, BRow q i f → R f) := by
  obtain ⟨l,_,hv,hR⟩ := h
  obtain ⟨i,hi,hie⟩ := (hR e).mpr he
  exact ⟨i,hv i hi,hie,fun f hf => (hR f).mp ⟨i,hi,hf⟩⟩

def Covered (q : Nat) (R : Nat → Prop) : Prop :=
  (∃ i, i ≤ 4*q+2 ∧ ∀ f, BRow q i f → R f) ∧
  ∀ e, R e → ∃ i, i ≤ 4*q+2 ∧ BRow q i e ∧ ∀ f, BRow q i f → R f

/-- Exact generation criterion; it avoids enumerating all source subfamilies. -/
theorem generated_iff_covered (q : Nat) (R : Nat → Prop) : Generated q R ↔ Covered q R := by
  classical
  constructor
  · intro h
    refine ⟨?_,fun _ he => point_covered q h he⟩
    obtain ⟨l,hn,hv,hR⟩ := h
    cases l with
    | nil => exact False.elim (hn rfl)
    | cons i l =>
      exact ⟨i,hv i (by simp),fun f hf => (hR f).mp ⟨i,by simp,hf⟩⟩
  · intro h
    let l := (List.range (4*q+3)).filter (fun i => decide (∀ f, BRow q i f → R f))
    have hmem (i : Nat) : i ∈ l ↔ i ≤ 4*q+2 ∧ ∀ f, BRow q i f → R f := by
      simp only [l,List.mem_filter,List.mem_range,decide_eq_true_eq]
      constructor
      · exact fun h => ⟨by omega,h.2⟩
      · exact fun h => ⟨by omega,h.2⟩
    refine ⟨l,?_,fun i hi => ((hmem i).mp hi).1,?_⟩
    · obtain ⟨i,hi,hsub⟩ := h.1
      have him := (hmem i).mpr ⟨hi,hsub⟩
      exact fun he => List.not_mem_nil (he ▸ him)
    · intro e
      constructor
      · rintro ⟨i,hi,hie⟩
        exact ((hmem i).mp hi).2 e hie
      · intro he
        obtain ⟨i,hi,hie,hsub⟩ := h.2 e he
        exact ⟨i,(hmem i).mpr ⟨hi,hsub⟩,hie⟩


end LuRazSixRowClosure
