import SixRowRangeCountTools

namespace LuRazSixRowSpectrum
open LuRazClosure LuRazEnumeration LuRazThreeRow LuRazSixRowClosure Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
noncomputable section

theorem removed_count_R6D (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 6).map (RemovedForm.eval q)) e=removedCountR6D (q:Int) (e:Int) := by
  simp only [removedGroup,dParams,List.map_cons,List.map_append,List.map_map,
    Function.comp_def,count_at_cons,count_at_append]
  have hl := count_upper_range (4) (q-2) e (fun a => RemovedForm.eval q (.r6d a)) 5 ((e=2 ∨ e=3) ∨ I (2*q+1) (4*q) e) (by
    intro a ha
    have hb := (range_mem a (4) (q-2)).mp ha
    simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,
      Difference.Cp,Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
    omega)
  have hr := count_upper_range (q+3) (q-3) e (fun a => RemovedForm.eval q (.r6d a)) 5 ((e=2 ∨ e=3) ∨ I (2*q+1) (4*q) e) (by
    intro a ha
    have hb := (range_mem a (q+3) (q-3)).mp ha
    simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,
      Difference.Cp,Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
    omega)
  rw [hl,hr]
  clear hl hr
  simp [indicator_as_bool,lowerRangeCount,upperRangeCount,LuRazCounting.mark,
    RemovedForm.eval,removedCountR6D,Difference.A,Difference.B,Difference.C,Difference.Ct,
    Difference.Cp,Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,I]
  repeat first | omega | (split <;> simp_all)

theorem added_count_N6E (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 4).map (AddedForm.eval q)) e=addedCountN6E (q:Int) (e:Int) := by
  simp only [addedGroup,pParams,List.map_append,List.map_map,Function.comp_def,count_at_append]
  have hl := count_upper_range (4) (q-2) e (fun a => AddedForm.eval q (.n6e a)) 5 ((e=2 ∨ e=3) ∨ I (2*q+3) (4*q) e) (by
    intro a ha
    have hb := (range_mem a (4) (q-2)).mp ha
    simp only [AddedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,
      Difference.Cp,Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
    omega)
  have hr := count_upper_range (q+3) (q-1) e (fun a => AddedForm.eval q (.n6e a)) 5 ((e=2 ∨ e=3) ∨ I (2*q+3) (4*q) e) (by
    intro a ha
    have hb := (range_mem a (q+3) (q-1)).mp ha
    simp only [AddedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,
      Difference.Cp,Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
    omega)
  rw [hl,hr]
  clear hl hr
  simp [indicator_as_bool,lowerRangeCount,upperRangeCount,LuRazCounting.mark,
    AddedForm.eval,addedCountN6E,Difference.A,Difference.B,Difference.C,Difference.Ct,
    Difference.Cp,Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,I]
  repeat first | omega | (split <;> simp_all)

theorem added_count_N7right (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 7).map (AddedForm.eval q)) e=addedCountN7right (q:Int) (e:Int) := by
  simp only [addedGroup,rightParams,List.map_cons,List.map_map,
    Function.comp_def,count_at_cons]
  have hl := count_lower_range (3*q+2) (q-2) e (fun a => AddedForm.eval q (.n7right a)) 0 (4*(q:Int)) ((e=1 ∨ e=2 ∨ e=3) ∨ Difference.Lnew q e) (by
    intro a ha
    have hb := (range_mem a (3*q+2) (q-2)).mp ha
    simp only [AddedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,
      Difference.Cp,Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
    omega)
  rw [hl]
  clear hl
  simp [indicator_as_bool,lowerRangeCount,upperRangeCount,LuRazCounting.mark,
    AddedForm.eval,addedCountN7right,Difference.A,Difference.B,Difference.C,Difference.Ct,
    Difference.Cp,Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,I]
  repeat first | omega | (split <;> simp_all)

theorem removed_count_R14C (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 21).map (RemovedForm.eval q)) e=removedCountR14C (q:Int) (e:Int) := by
  simp only [removedGroup,c14Params,List.map_append,List.map_map,Function.comp_def,count_at_append]
  have hl := count_lower_range (2*q+4) (q-2) e (fun a => RemovedForm.eval q (.r14c a)) 0 (4*(q:Int)) ((e=2 ∨ e=3 ∨ e=4) ∨ Difference.C q e) (by
    intro a ha
    have hb := (range_mem a (2*q+4) (q-2)).mp ha
    simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,
      Difference.Cp,Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
    omega)
  have hr := count_lower_range (3*q+3) (q-3) e (fun a => RemovedForm.eval q (.r14c a)) 0 (4*(q:Int)) ((e=2 ∨ e=3 ∨ e=4) ∨ Difference.C q e) (by
    intro a ha
    have hb := (range_mem a (3*q+3) (q-3)).mp ha
    simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,
      Difference.Cp,Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
    omega)
  rw [hl,hr]
  clear hl hr
  simp [indicator_as_bool,lowerRangeCount,upperRangeCount,LuRazCounting.mark,
    RemovedForm.eval,removedCountR14C,Difference.A,Difference.B,Difference.C,Difference.Ct,
    Difference.Cp,Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,I]
  repeat first | omega | (split <;> simp_all)

theorem removed_count_R15short (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 26).map (RemovedForm.eval q)) e=removedCountR15short (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_append,List.map_map,Function.comp_def,count_at_append]
  have hl := count_upper_range (4) (q-2) e (fun a => RemovedForm.eval q (.r15short a (2*q+2))) 5 ((e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ I (2*q+2) (4*q) e) (by
    intro a ha
    have hb := (range_mem a (4) (q-2)).mp ha
    simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,
      Difference.Cp,Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
    omega)
  have hr := count_upper_range (4) (q-2) e (fun a => RemovedForm.eval q (.r15short a (2*q+3))) 5 ((e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ I (2*q+3) (4*q) e) (by
    intro a ha
    have hb := (range_mem a (4) (q-2)).mp ha
    simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,
      Difference.Cp,Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
    omega)
  rw [hl,hr]
  clear hl hr
  have hc : max (0:Int) (min (2*(q:Int)+3) (e:Int)-(2*(q:Int)+2)+1)=0 ∨
      max (0:Int) (min (2*(q:Int)+3) (e:Int)-(2*(q:Int)+2)+1)=1 ∨
      max (0:Int) (min (2*(q:Int)+3) (e:Int)-(2*(q:Int)+2)+1)=2 := by omega
  rcases hc with hc | hc | hc
  all_goals simp [indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR15short,hc,I]
  all_goals repeat first | omega | (split <;> simp_all)

end
end LuRazSixRowSpectrum
