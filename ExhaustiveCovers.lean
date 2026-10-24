import ThreeRowResearch

namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem old_of_local_covers (q : Nat) (R : Nat → Prop) (e0 : Nat) (h0 : R e0)
    (hcov : ∀ e, R e → ∃ T, LuRazClosure.Generated q T ∧ T e ∧ (∀ f, T f → R f)) :
    LuRazClosure.Generated q R := by
  classical
  have hc : ∀ e, R e → ∃ i, i≤4*q+2 ∧ Row q i e ∧ ∀ f, Row q i f → R f := by
    intro e he
    obtain ⟨T,⟨l,_,hv,hT⟩,hte,hsub⟩ := hcov e he
    obtain ⟨i,hi,hie⟩ := (hT e).mpr hte
    exact ⟨i,hv i hi,hie,fun f hf => hsub f ((hT f).mp ⟨i,hi,hf⟩)⟩
  let l := (List.range (4*q+3)).filter (fun i => decide (∀ f, Row q i f → R f))
  have hm (i : Nat) : i∈l ↔ i≤4*q+2 ∧ ∀ f, Row q i f → R f := by
    simp only [l,List.mem_filter,List.mem_range,decide_eq_true_eq]
    constructor
    · exact fun h => ⟨by omega,h.2⟩
    · exact fun h => ⟨by omega,h.2⟩
  refine ⟨l,?_,fun i hi => ((hm i).mp hi).1,?_⟩
  · obtain ⟨i,hi,_,hsub⟩ := hc e0 h0
    exact List.ne_nil_of_mem ((hm i).mpr ⟨hi,hsub⟩)
  · intro e
    constructor
    · rintro ⟨i,hi,hie⟩; exact ((hm i).mp hi).2 e hie
    · intro he
      obtain ⟨i,hi,hie,hsub⟩ := hc e he
      exact ⟨i,(hm i).mpr ⟨hi,hsub⟩,hie⟩

theorem old_two_augmented (q : Nat) (hq : 4≤q) :
    LuRazClosure.Generated q (fun e => VRow q 2 e ∨ e=2) := by
  have hp : P q (2*q) := by unfold P; omega
  apply LuRazClosure.generated_congr q (LuRazClosure.generated_join q (generated_A q hq)
    (LuRazClosure.generated_L q (2*q) (2*q) hq hp hp (by omega)))
  intro e
  rw [row_two q e hq]
  unfold ARow LRow LNormal I beta
  repeat first | (simp_all <;> omega) | split

theorem old_four_augmented (q : Nat) (hq : 4≤q) :
    LuRazClosure.Generated q (fun e => VRow q 4 e ∨ e=4*q-1) := by
  have hp : P q 4 := by unfold P; omega
  apply LuRazClosure.generated_congr q (LuRazClosure.generated_join q (generated_E q hq)
    (LuRazClosure.generated_L q 4 4 hq hp hp (by omega)))
  intro e
  rw [row_four q e hq]
  unfold ERow LRow LNormal I beta
  repeat first | (simp_all <;> omega) | split

theorem core123_old_if_last (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core123 R) (hn : R (4*q-1)) : LuRazClosure.Generated q R := by
  apply old_of_local_covers q R 1 hc.1
  intro e he
  obtain ⟨i,hi,hie,hsub⟩ := point_covered q hg he
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · exact ⟨_,old_two_augmented q hq,Or.inl hie,fun f hf =>
        hf.elim (hsub f) (fun h => h ▸ hc.2.1)⟩
    · exact ⟨_,old_four_augmented q hq,Or.inl hie,fun f hf =>
        hf.elim (hsub f) (fun h => h ▸ hn)⟩
    · exact False.elim (hc.2.2.2 (hsub 4 ((row_last q 4 hq).mpr (by omega))))
  · exact ⟨Row q i,LuRazClosure.generated_row q i hi,(unchanged_row q i e hs).mp hie,
      fun f hf => hsub f ((unchanged_row q i f hs).mpr hf)⟩

end LuRazThreeRow
