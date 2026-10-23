import LuRazParametric

namespace LuRazParametric
open RazReimerPredicates

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def NatSeparated (q i j : Nat) : Prop :=
  ∃ e, 1 ≤ e ∧ e ≤ 4*q ∧
    ((Row q i e ∧ ¬FilterRow q j e) ∨ (Row q j e ∧ ¬FilterRow q i e))

theorem NatSeparated.symm {q i j : Nat} (h : NatSeparated q i j) :
    NatSeparated q j i := by
  obtain ⟨e,hlo,hhi,hsep⟩ := h
  exact ⟨e,hlo,hhi,hsep.symm⟩

theorem zero_coatom_sep (q : Nat) (hq : 3 ≤ q) (j : Nat)
    (hj1 : 1 ≤ j) (hj2 : j ≤ 4*q) : NatSeparated q 0 j := by
  refine ⟨j,hj1,hj2,Or.inl ⟨?_,?_⟩⟩
  · exact (row_case_0 q 0 j hq rfl).mpr ⟨hj1,hj2⟩
  · unfold FilterRow; omega

theorem zero_extra1_sep (q : Nat) (hq : 3 ≤ q) : NatSeparated q 0 (4*q+1) := by
  refine ⟨1,by omega,by omega,Or.inl ⟨?_,?_⟩⟩
  · apply (row_case_0 q 0 1 hq rfl).mpr; omega
  · unfold FilterRow; omega
theorem zero_extra2_sep (q : Nat) (hq : 3 ≤ q) : NatSeparated q 0 (4*q+2) := by
  refine ⟨3,by omega,by omega,Or.inl ⟨?_,?_⟩⟩
  · apply (row_case_0 q 0 3 hq rfl).mpr; omega
  · unfold FilterRow; omega

theorem coatom_coatom_sep (q : Nat) (hq : 3 ≤ q) (i j : Nat)
    (hi1 : 1 ≤ i) (hi2 : i ≤ 4*q) (hj1 : 1 ≤ j) (hj2 : j ≤ 4*q)
    (hne : i ≠ j) : NatSeparated q i j := by
  rcases coatoms_separated q hq i j hi1 hi2 hj1 hj2 hne with h | h
  · refine ⟨j,hj1,hj2,Or.inl ⟨h,?_⟩⟩; unfold FilterRow; omega
  · refine ⟨i,hi1,hi2,Or.inr ⟨h,?_⟩⟩; unfold FilterRow; omega

theorem coatom_first_sep (q : Nat) (hq : 3 ≤ q) (i : Nat)
    (hi1 : 1 ≤ i) (hi2 : i ≤ 4*q) : NatSeparated q i (4*q+1) := by
  rcases first_double_hole_separated q hq i hi1 hi2 with h | h | h
  · refine ⟨1,by omega,by omega,Or.inl ⟨h,?_⟩⟩; unfold FilterRow; omega
  · refine ⟨2,by omega,by omega,Or.inl ⟨h,?_⟩⟩; unfold FilterRow; omega
  · refine ⟨i,hi1,hi2,Or.inr ⟨h,?_⟩⟩; unfold FilterRow; omega

theorem coatom_second_sep (q : Nat) (hq : 3 ≤ q) (i : Nat)
    (hi1 : 1 ≤ i) (hi2 : i ≤ 4*q) : NatSeparated q i (4*q+2) := by
  rcases second_double_hole_separated q hq i hi1 hi2 with h | h | h
  · refine ⟨3,by omega,by omega,Or.inl ⟨h,?_⟩⟩; unfold FilterRow; omega
  · refine ⟨4,by omega,by omega,Or.inl ⟨h,?_⟩⟩; unfold FilterRow; omega
  · refine ⟨i,hi1,hi2,Or.inr ⟨h,?_⟩⟩; unfold FilterRow; omega

theorem extras_sep (q : Nat) (hq : 3 ≤ q) : NatSeparated q (4*q+1) (4*q+2) := by
  refine ⟨1,by omega,by omega,Or.inr ⟨?_,?_⟩⟩
  · apply (row_case_15 q (4*q+2) 1 hq rfl).mpr; omega
  · unfold FilterRow; omega

theorem main_partition (q i : Nat) (hi : i < 4*q+3) :
    i = 0 ∨ (1 ≤ i ∧ i ≤ 4*q) ∨ i = 4*q+1 ∨ i = 4*q+2 := by omega

theorem nat_separated (q : Nat) (hq : 3 ≤ q) (i j : Nat)
    (hi : i < 4*q+3) (hj : j < 4*q+3) (hne : i ≠ j) : NatSeparated q i j := by
  rcases main_partition q i hi with hi0 | hiC | hiA | hiB
  · rcases main_partition q j hj with hj0 | hjC | hjA | hjB
    · exfalso; omega
    · have hi : i = 0 := hi0
      subst i
      exact zero_coatom_sep q hq j hjC.1 hjC.2
    · have hi : i = 0 := hi0
      subst i
      have hj : j = 4*q+1 := hjA
      subst j
      exact zero_extra1_sep q hq
    · have hi : i = 0 := hi0
      subst i
      have hj : j = 4*q+2 := hjB
      subst j
      exact zero_extra2_sep q hq
  · rcases main_partition q j hj with hj0 | hjC | hjA | hjB
    · have hj : j = 0 := hj0
      subst j
      exact (zero_coatom_sep q hq i hiC.1 hiC.2).symm
    · exact coatom_coatom_sep q hq i j hiC.1 hiC.2 hjC.1 hjC.2 hne
    · have hj : j = 4*q+1 := hjA
      subst j
      exact coatom_first_sep q hq i hiC.1 hiC.2
    · have hj : j = 4*q+2 := hjB
      subst j
      exact coatom_second_sep q hq i hiC.1 hiC.2
  · rcases main_partition q j hj with hj0 | hjC | hjA | hjB
    · have hi : i = 4*q+1 := hiA
      subst i
      have hj : j = 0 := hj0
      subst j
      exact (zero_extra1_sep q hq).symm
    · have hi : i = 4*q+1 := hiA
      subst i
      exact (coatom_first_sep q hq j hjC.1 hjC.2).symm
    · exfalso; omega
    · have hi : i = 4*q+1 := hiA
      subst i
      have hj : j = 4*q+2 := hjB
      subst j
      exact extras_sep q hq
  · rcases main_partition q j hj with hj0 | hjC | hjA | hjB
    · have hi : i = 4*q+2 := hiB
      subst i
      have hj : j = 0 := hj0
      subst j
      exact (zero_extra2_sep q hq).symm
    · have hi : i = 4*q+2 := hiB
      subst i
      exact (coatom_second_sep q hq j hjC.1 hjC.2).symm
    · have hi : i = 4*q+2 := hiB
      subst i
      have hj : j = 4*q+1 := hjA
      subst j
      exact (extras_sep q hq).symm
    · exfalso; omega

theorem nat_filter_injective (q : Nat) (hq : 3 ≤ q) (i j : Nat)
    (hi : i < 4*q+3) (hj : j < 4*q+3)
    (h : ∀ e, 1 ≤ e → e ≤ 4*q → (FilterRow q i e ↔ FilterRow q j e)) : i = j := by
  have h1 := h 1 (by omega) (by omega)
  have h2 := h 2 (by omega) (by omega)
  have h3 := h 3 (by omega) (by omega)
  have h4 := h 4 (by omega) (by omega)
  rcases main_partition q i hi with hi0 | hiC | hiA | hiB
  · rcases main_partition q j hj with hj0 | hjC | hjA | hjB
    · omega
    · have hJ := h j hjC.1 hjC.2
      unfold FilterRow at h1 h2 h3 h4 hJ
      omega
    · unfold FilterRow at h1 h2 h3 h4
      omega
    · unfold FilterRow at h1 h2 h3 h4
      omega
  · rcases main_partition q j hj with hj0 | hjC | hjA | hjB
    · have hI := h i hiC.1 hiC.2
      unfold FilterRow at h1 h2 h3 h4 hI
      omega
    · have hI := h i hiC.1 hiC.2
      have hJ := h j hjC.1 hjC.2
      unfold FilterRow at h1 h2 h3 h4 hI hJ
      omega
    · have hI := h i hiC.1 hiC.2
      unfold FilterRow at h1 h2 h3 h4 hI
      omega
    · have hI := h i hiC.1 hiC.2
      unfold FilterRow at h1 h2 h3 h4 hI
      omega
  · rcases main_partition q j hj with hj0 | hjC | hjA | hjB
    · unfold FilterRow at h1 h2 h3 h4
      omega
    · have hJ := h j hjC.1 hjC.2
      unfold FilterRow at h1 h2 h3 h4 hJ
      omega
    · omega
    · unfold FilterRow at h1 h2 h3 h4
      omega
  · rcases main_partition q j hj with hj0 | hjC | hjA | hjB
    · unfold FilterRow at h1 h2 h3 h4
      omega
    · have hJ := h j hjC.1 hjC.2
      unfold FilterRow at h1 h2 h3 h4 hJ
      omega
    · unfold FilterRow at h1 h2 h3 h4
      omega
    · omega

theorem S_included_F (q : Nat) (hq : 3 ≤ q) :
    ∀ i, Included (S q i) (F q i) := by
  intro i e he
  exact row_in_filter q hq i.val (e.val+1) i.isLt (by omega) (by have := e.isLt; omega) he

theorem intervals_disjoint (q : Nat) (hq : 3 ≤ q) : IntervalsDisjoint (S q) (F q) := by
  intro i j hne T hiS hiF hjS hjF
  obtain ⟨e,hlo,hhi,hsep⟩ := nat_separated q hq i.val j.val i.isLt j.isLt
    (fun heq => hne (Fin.ext heq))
  let E : Fin (4*q) := ⟨e-1,by omega⟩
  have hrestore : e-1+1 = e := by omega
  rcases hsep with h | h
  · have hs : S q i E := by change Row q i.val (e-1+1); rw [hrestore]; exact h.1
    have hn : ¬ F q j E := by change ¬ FilterRow q j.val (e-1+1); rw [hrestore]; exact h.2
    exact hn (hjF E (hiS E hs))
  · have hs : S q j E := by change Row q j.val (e-1+1); rw [hrestore]; exact h.1
    have hn : ¬ F q i E := by change ¬ FilterRow q i.val (e-1+1); rw [hrestore]; exact h.2
    exact hn (hiF E (hjS E hs))

theorem S_injective (q : Nat) (hq : 3 ≤ q) : Function.Injective (S q) := by
  classical
  intro i j heq
  apply Classical.byContradiction
  intro hne
  apply intervals_disjoint q hq i j hne (S q i)
  · intro e he; exact he
  · exact S_included_F q hq i
  · rw [heq]; intro e he; exact he
  · rw [heq]; exact S_included_F q hq j

theorem F_injective (q : Nat) (hq : 3 ≤ q) : Function.Injective (F q) := by
  intro i j heq
  apply Fin.ext
  apply nat_filter_injective q hq i.val j.val i.isLt j.isLt
  intro e hlo hhi
  have hh := congrFun heq (⟨e-1,by omega⟩ : Fin (4*q))
  change FilterRow q i.val (e-1+1) = FilterRow q j.val (e-1+1) at hh
  have hr : e-1+1 = e := by omega
  rw [hr] at hh
  exact iff_of_eq hh

def hole1 (q : Nat) (hq : 3 ≤ q) (i : Fin (4*q+3)) : Fin (4*q) :=
  if hA : i.val = 4*q+1 then ⟨0,by omega⟩ else
  if hB : i.val = 4*q+2 then ⟨2,by omega⟩ else
  ⟨i.val-1,by have := i.isLt; omega⟩
def hole2 (q : Nat) (hq : 3 ≤ q) (i : Fin (4*q+3)) : Fin (4*q) :=
  if i.val = 4*q+1 then ⟨1,by omega⟩ else
  if i.val = 4*q+2 then ⟨3,by omega⟩ else hole1 q hq i

theorem F_top (q : Nat) (e : Fin (4*q)) : F q 0 e := by
  unfold F FilterRow
  exact Or.inl rfl

theorem F_coatom (q : Nat) (hq : 3 ≤ q) (p e : Fin (4*q)) :
    F q ⟨p.val+1,by omega⟩ e ↔ e ≠ p := by
  simp only [ne_eq,Fin.ext_iff]
  unfold F FilterRow
  simp only [Fin.val_mk]
  have := p.isLt
  omega

theorem F_holes (q : Nat) (hq : 3 ≤ q) (i : Fin (4*q+3)) (hi : i.val ≠ 0)
    (e : Fin (4*q)) : F q i e ↔ e ≠ hole1 q hq i ∧ e ≠ hole2 q hq i := by
  by_cases hA : i.val = 4*q+1
  · simp only [hole1,hole2,dif_pos hA,if_pos hA,Fin.ext_iff,ne_eq]
    unfold F FilterRow
    have := e.isLt
    omega
  by_cases hB : i.val = 4*q+2
  · simp only [hole1,hole2,dif_neg hA,dif_pos hB,if_neg hA,if_pos hB,Fin.ext_iff,ne_eq]
    unfold F FilterRow
    have := e.isLt
    omega
  · simp only [hole1,hole2,dif_neg hA,dif_neg hB,if_neg hA,if_neg hB,Fin.ext_iff,ne_eq]
    unfold F FilterRow
    have := i.isLt
    omega

theorem F_upward (q : Nat) (hq : 3 ≤ q) : UpwardClosed (F q) := by
  classical
  intro i T ht
  by_cases hi : i.val = 0
  · have hieq : i = 0 := Fin.ext hi
    subst i
    refine ⟨0,funext (fun e => propext ⟨fun he => ht e he,fun _ => F_top q e⟩)⟩
  · have hrow := F_holes q hq i hi
    have hh : ∀ e, e ≠ hole1 q hq i → e ≠ hole2 q hq i → T e :=
      fun e hp hq' => ht e ((hrow e).mpr ⟨hp,hq'⟩)
    rcases LuRazFollowup.two_hole_superset T (hole1 q hq i) (hole2 q hq i) hh with htop | hp | hq' | hpq
    · exact ⟨0,funext (fun e => propext ⟨fun _ => htop e,fun _ => F_top q e⟩)⟩
    · refine ⟨⟨(hole1 q hq i).val+1,by have := (hole1 q hq i).isLt; omega⟩,?_⟩
      exact funext (fun e => propext ((F_coatom q hq (hole1 q hq i) e).trans (hp e).symm))
    · refine ⟨⟨(hole2 q hq i).val+1,by have := (hole2 q hq i).isLt; omega⟩,?_⟩
      exact funext (fun e => propext ((F_coatom q hq (hole2 q hq i) e).trans (hq' e).symm))
    · exact ⟨i,funext (fun e => propext ((hrow e).trans (hpq e).symm))⟩

theorem reimer_condition (q : Nat) (hq : 3 ≤ q) : ReimerCondition (S q) :=
  ⟨F q,S_injective q hq,F_injective q hq,F_upward q hq,S_included_F q hq,intervals_disjoint q hq⟩

end LuRazParametric
