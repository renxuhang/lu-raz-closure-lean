import SixRowRangeCountTools

namespace LuRazSixRowSpectrum
open LuRazClosure LuRazEnumeration LuRazThreeRow LuRazSixRowClosure Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
noncomputable section

theorem count_regular_suffix (q e : Nat) (hq : 4≤q)
    (f : Nat → Nat → Prop) (fixed : Prop)
    (h : ∀a,f a e ↔ fixed ∨ Difference.Suffix q a e) :
    CountAt ((regularParams q).map f) e=
      lowerRangeCount 4 (q-2) e (2*(q:Int)) (4*(q:Int)) fixed+
      lowerRangeCount (q+4) (q-3) e (2*(q:Int)-1) (4*(q:Int)) fixed := by
  simp only [regularParams,List.map_append,count_at_append]
  have hl := count_lower_range 4 (q-2) e f (2*(q:Int)) (4*(q:Int)) fixed (by
    intro a ha
    have hb := (range_mem a 4 (q-2)).mp ha
    rw [h a]
    simp only [Difference.Suffix,I]
    by_cases hp : fixed <;> simp [hp] <;> omega)
  have hr := count_lower_range (q+4) (q-3) e f (2*(q:Int)-1) (4*(q:Int)) fixed (by
    intro a ha
    have hb := (range_mem a (q+4) (q-3)).mp ha
    rw [h a]
    simp only [Difference.Suffix,I]
    by_cases hp : fixed <;> simp [hp] <;> omega)
  rw [hl,hr]

theorem removed_count_R6C_regular (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 4).map (RemovedForm.eval q)) e=
      removedCountR6C_regular (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  rw [count_regular_suffix q e hq (fun a => RemovedForm.eval q (.r6regular a))
    ((e=2 ∨ e=3) ∨ Difference.C q e) (by intro a; simp only [RemovedForm.eval,or_assoc])]
  simp only [lowerRangeCount,removedCountR6C_regular,indicator_as_bool,Difference.C,I]
  repeat first | omega | split

theorem added_count_N6C_regular (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 2).map (AddedForm.eval q)) e=
      addedCountN6C_regular (q:Int) (e:Int) := by
  simp only [addedGroup,List.map_map,Function.comp_def]
  rw [count_regular_suffix q e hq (fun a => AddedForm.eval q (.n6regular a))
    ((e=2 ∨ e=3) ∨ Difference.Ct q e) (by intro a; simp only [AddedForm.eval,or_assoc])]
  simp only [lowerRangeCount,addedCountN6C_regular,indicator_as_bool,Difference.Ct,I]
  repeat first | omega | split

theorem added_count_N7C_regular (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 5).map (AddedForm.eval q)) e=
      addedCountN7C_regular (q:Int) (e:Int) := by
  simp only [addedGroup,List.map_map,Function.comp_def]
  rw [count_regular_suffix q e hq (fun a => AddedForm.eval q (.n7regular a))
    ((e=1 ∨ e=2 ∨ e=3) ∨ Difference.Ct q e) (by intro a; simp only [AddedForm.eval,or_assoc])]
  simp only [lowerRangeCount,addedCountN7C_regular,indicator_as_bool,Difference.Ct,I]
  repeat first | omega | split

end
end LuRazSixRowSpectrum
