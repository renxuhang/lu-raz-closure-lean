import ThreeRowFullLossCount
import ThreeRowCore5

namespace LuRazThreeRow
open LuRazClosure LuRazParametric LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def EPrime (q e : Nat) : Prop := e=1 ∨ e=2 ∨ e=3 ∨ I (2*q+3) (4*q-2) e ∨ e=4*q

theorem e_source (q e : Nat) (hq : 4≤q) : VRow q 4 e ↔ EPrime q e := by
  rw [row_four q e hq]
  unfold EPrime I
  omega

theorem generated_j (q a b : Nat) (hq : 4≤q) (hab : JReachable q a b) : Generated q (JRow a b) := by
  obtain ⟨l,hn,hv,he⟩ := J_source_attainable q a b hq hab
  have hs (t : Nat) (ht : t∈l) : ¬Special q (JIndex t) := by
    have ht' := hv t ht
    unfold Special JIndex
    split <;> omega
  refine ⟨l.map JIndex,?_,?_,?_⟩
  · exact fun h => hn (List.map_eq_nil_iff.mp h)
  · intro i hi
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi
    have ht' := hv t ht
    unfold JIndex
    split <;> omega
  · intro e
    constructor
    · rintro ⟨i,hi,hie⟩
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi
      exact (he e).mp ⟨t,ht,(unchanged_row q _ e (hs t ht)).mp hie⟩
    · intro h
      obtain ⟨t,ht,hte⟩ := (he e).mpr h
      exact ⟨JIndex t,List.mem_map.mpr ⟨t,ht,rfl⟩,(unchanged_row q _ e (hs t ht)).mpr hte⟩

inductive AddFull where
  | right (a : Nat) | gap (a : Nat) | point
  deriving DecidableEq, Repr

def AddFull.Valid (q : Nat) : AddFull → Prop
  | .right a => 6≤a ∧ a≤2*q+2
  | .gap a => q+4≤a ∧ a≤2*q+2
  | .point => True

def AddFull.eval (q : Nat) : AddFull → Nat → Prop
  | .right a => fun e => FullHead e ∨ I a (4*q-2) e ∨ e=4*q
  | .gap a => fun e => FullHead e ∨ I 5 (q+2) e ∨ I a (4*q-2) e ∨ e=4*q
  | .point => fun e => FullHead e ∨ I 5 (2*q+1) e ∨ I (2*q+3) (4*q-2) e ∨ e=4*q

theorem add_right_generated (q a : Nat) (hq : 4≤q) (ha : 6≤a ∧ a≤2*q+2) :
    Generated q (AddFull.eval q (.right a)) := by
  have he := generated_congr q (generated_row q 4 (by omega)) (fun e => e_source q e hq)
  by_cases hal : a≤2*q+1
  · have hj : JReachable q a (4*q-3) := by
      unfold JReachable g
      split <;> omega
    apply generated_congr q (generated_join q he (generated_j q a (4*q-3) hq hj))
    intro e
    unfold EPrime JRow AddFull.eval FullHead I
    omega
  · have haa : a=2*q+2 := by omega
    have hk := generated_row q (2*q+1) (by omega)
    apply generated_congr q (generated_join q he hk)
    intro e
    rw [unchanged_row q (2*q+1) e (by unfold Special; omega),K1_source q e hq]
    unfold EPrime K1Row AddFull.eval FullHead I
    omega

theorem add_full_generated (q : Nat) (hq : 4≤q) (z : AddFull) (hz : z.Valid q) : Generated q (z.eval q) := by
  cases z with
  | right a => exact add_right_generated q a hq hz
  | gap a =>
    have ha := generated_congr q (generated_row q (4*q+2) (by omega)) (fun e => a_source q e hq)
    apply generated_congr q (generated_join q ha (add_right_generated q a hq (by simp only [AddFull.Valid] at hz; omega)))
    intro e
    unfold ARow AddFull.eval FullHead I
    omega
  | point =>
    have he := generated_congr q (generated_row q 4 (by omega)) (fun e => e_source q e hq)
    have hl := generated_congr q (generated_row q (4*q-1) (by omega)) (fun e => last_source q e hq)
    apply generated_congr q (generated_join q he hl)
    intro e
    unfold EPrime LPrime AddFull.eval FullHead I
    omega

theorem add_full_core (q : Nat) (hq : 4≤q) (z : AddFull) (hz : z.Valid q) : CoreFull (z.eval q) := by
  cases z <;> unfold CoreFull AddFull.eval FullHead I <;> simp_all

theorem old_full_thin_prefix (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q)
    (hn : z.eval q (4*q)) (hn1 : ¬z.eval q (4*q-1)) :
    z.eval q 5 ∧ z.eval q (q+3) ∧ (z.eval q (4*q-2) → z.eval q (2*q+2)) := by
  cases z <;> simp only [NFFull.Valid] at hz <;>
    simp only [NFFull.eval,FullHead,I] at hn hn1 ⊢ <;> simp_all <;> omega

theorem add_full_not_old (q : Nat) (hq : 4≤q) (z : AddFull) (hz : z.Valid q) :
    ¬LuRazClosure.Generated q (z.eval q) := by
  intro hg
  obtain ⟨w,hw,he⟩ := (full_closure_exact q hq _).mp ⟨hg,add_full_core q hq z hz⟩
  have hn : w.eval q (4*q) := (he _).mp (by cases z <;> simp [AddFull.eval])
  have hn1 : ¬w.eval q (4*q-1) := by
    intro h
    have hh := (he _).mpr h
    cases z <;> simp only [AddFull.eval,FullHead,I] at hh <;> omega
  have hp := old_full_thin_prefix q hq w hw hn hn1
  rw [←he 5,←he (q+3),←he (4*q-2),←he (2*q+2)] at hp
  cases z <;> simp only [AddFull.Valid] at hz <;>
    simp only [AddFull.eval,FullHead,I] at hp <;> simp_all <;> omega

theorem add_full_unique (q : Nat) (hq : 4≤q) (z w : AddFull) (hz : z.Valid q) (hw : w.Valid q)
    (he : ∀ e, z.eval q e ↔ w.eval q e) : z=w := by
  have h5 := he 5
  have hq3 := he (q+3)
  cases z <;> cases w
  case right.right a b =>
    have ha := he a
    have hb := he b
    simp only [AddFull.Valid] at hz hw
    simp only [AddFull.eval,FullHead,I] at ha hb
    have hab : a=b := by omega
    rw [hab]
  case gap.gap a b =>
    have ha := he a
    have hb := he b
    simp only [AddFull.Valid] at hz hw
    simp only [AddFull.eval,FullHead,I] at ha hb
    have hab : a=b := by omega
    rw [hab]
  case point.point => rfl
  all_goals simp only [AddFull.Valid] at hz hw
  all_goals simp only [AddFull.eval,FullHead,I] at h5 hq3
  all_goals simp_all <;> omega

end LuRazThreeRow
