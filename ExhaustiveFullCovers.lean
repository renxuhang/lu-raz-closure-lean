import Exhaustive134Count

namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem old_last_augmented (q : Nat) (hq : 4≤q) :
    LuRazClosure.Generated q (fun e => VRow q (4*q-1) e ∨ e=1 ∨ e=2) := by
  apply LuRazClosure.generated_congr q (LuRazClosure.generated_join q (generated_Z q hq)
    (LuRazClosure.generated_row q (4*q-1) (by omega)))
  intro e
  rw [row_last q e hq,row_case_12 q (4*q-1) e (by omega) (by omega)]
  unfold ZRow I
  omega

theorem full_old_if_last (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : CoreFull R) (hn : R (4*q-1)) : LuRazClosure.Generated q R := by
  apply old_of_local_covers q R 1 hc.1
  intro e he
  obtain ⟨i,hi,hie,hsub⟩ := point_covered q hg he
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · exact ⟨_,old_two_augmented q hq,Or.inl hie,fun f hf =>
        hf.elim (hsub f) (fun h => h ▸ hc.2.1)⟩
    · exact ⟨_,old_four_augmented q hq,Or.inl hie,fun f hf =>
        hf.elim (hsub f) (fun h => h ▸ hn)⟩
    · refine ⟨_,old_last_augmented q hq,Or.inl hie,?_⟩
      intro f hf
      rcases hf with h | h | h
      · exact hsub f h
      · exact h ▸ hc.1
      · exact h ▸ hc.2.1
  · exact ⟨Row q i,LuRazClosure.generated_row q i hi,(unchanged_row q i e hs).mp hie,
      fun f hf => hsub f ((unchanged_row q i f hs).mpr hf)⟩

theorem full_old_if_neither (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hn1 : ¬R (4*q-1)) (hn : ¬R (4*q)) : LuRazClosure.Generated q R := by
  obtain ⟨l,hne,hv,hR⟩ := hg
  have hs : ∀ i∈l, ¬Special q i := by
    intro i hi h
    rcases h with rfl | rfl | rfl
    · exact hn1 ((hR _).mp ⟨2,hi,(row_two q _ hq).mpr (by omega)⟩)
    · exact hn ((hR _).mp ⟨4,hi,(row_four q _ hq).mpr (by omega)⟩)
    · exact hn ((hR _).mp ⟨4*q-1,hi,(row_last q _ hq).mpr (by omega)⟩)
  refine ⟨l,hne,hv,?_⟩
  intro e
  rw [←hR e]
  constructor
  · rintro ⟨i,hi,hie⟩; exact ⟨i,hi,(unchanged_row q i e (hs i hi)).mpr hie⟩
  · rintro ⟨i,hi,hie⟩; exact ⟨i,hi,(unchanged_row q i e (hs i hi)).mp hie⟩

theorem generated_e2 (q : Nat) (hq : 4≤q) : Generated q (fun e => ERow q e ∨ e=2) := by
  apply generated_congr q (generated_join q
    (generated_congr q (generated_row q 4 (by omega)) (fun e => e_source q e hq)) (generated_b q hq))
  intro e
  unfold EPrime BRow ERow I
  omega

theorem generated_k1 (q : Nat) (hq : 4≤q) : Generated q (K1Row q) := by
  apply generated_congr q (generated_row q (2*q+1) (by omega))
  intro e
  rw [unchanged_row q _ e (by unfold Special; omega)]
  exact K1_source q e hq

theorem generated_k2 (q : Nat) (hq : 4≤q) : Generated q (K2Row q) := by
  apply generated_congr q (generated_row q (2*q+2) (by omega))
  intro e
  rw [unchanged_row q _ e (by unfold Special; omega)]
  exact K2_source q e hq

theorem generated_krow (q k : Nat) (hq : 4≤q) (hk : k<2) : Generated q (KRow q k) := by
  have hc : k=0 ∨ k=1 := by omega
  rcases hc with rfl | rfl
  · exact generated_congr q (generated_k1 q hq) (fun e => (KRow_zero q e).symm)
  · exact generated_congr q (generated_k2 q hq) (fun e => (KRow_one q e hq).symm)

end LuRazThreeRow
