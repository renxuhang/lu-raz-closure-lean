import SixRowRangeCountTools

namespace LuRazSixRowSpectrum
open LuRazClosure LuRazEnumeration LuRazThreeRow LuRazSixRowClosure Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
noncomputable section

theorem added_count_N10 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 9).map (AddedForm.eval q)) e=addedCountN10 (q:Int) (e:Int) := by
  simp only [addedGroup,List.map_map,Function.comp_def]
  have hc := count_lower_range (2*q+1) (3) e
    (fun a => AddedForm.eval q (.n10 a)) 0 (4*(q:Int)-2) ((e=2 ∨ e=4) ∨ (e=4*q)) (by
      intro a ha
      have hb := (range_mem a (2*q+1) (3)).mp ha
      simp only [AddedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,addedCountN10,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem added_count_N11J (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 10).map (AddedForm.eval q)) e=addedCountN11J (q:Int) (e:Int) := by
  simp only [addedGroup,List.map_map,Function.comp_def]
  have hc := count_lower_range (5) (2*q-3) e
    (fun a => AddedForm.eval q (.n11j a)) 0 (4*(q:Int)-2) ((e=1 ∨ e=2 ∨ e=4) ∨ (e=4*q)) (by
      intro a ha
      have hb := (range_mem a (5) (2*q-3)).mp ha
      simp only [AddedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,addedCountN11J,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem added_count_N11AJ (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 11).map (AddedForm.eval q)) e=addedCountN11AJ (q:Int) (e:Int) := by
  simp only [addedGroup,List.map_map,Function.comp_def]
  have hc := count_lower_range (q+4) (q-2) e
    (fun a => AddedForm.eval q (.n11aj a)) 0 (4*(q:Int)-2) ((e=1 ∨ e=2 ∨ e=4) ∨ (I 5 (q+2) e ∨ e=4*q)) (by
      intro a ha
      have hb := (range_mem a (q+4) (q-2)).mp ha
      simp only [AddedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,addedCountN11AJ,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem added_count_N11AK (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 12).map (AddedForm.eval q)) e=addedCountN11AK (q:Int) (e:Int) := by
  simp only [addedGroup,List.map_map,Function.comp_def]
  have hc := count_lower_range (2*q+2) (2) e
    (fun a => AddedForm.eval q (.n11ak a)) 0 (4*(q:Int)-2) ((e=1 ∨ e=2 ∨ e=4) ∨ (I 5 (q+2) e ∨ e=4*q)) (by
      intro a ha
      have hb := (range_mem a (2*q+2) (2)).mp ha
      simp only [AddedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,addedCountN11AK,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem added_count_N13plain (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 13).map (AddedForm.eval q)) e=addedCountN13plain (q:Int) (e:Int) := by
  simp only [addedGroup,List.map_map,Function.comp_def]
  have hc := count_upper_range (2*q+2) (q-1) e
    (fun a => AddedForm.eval q (.n13plain a)) 5 ((e=1 ∨ e=3 ∨ e=4)) (by
      intro a ha
      have hb := (range_mem a (2*q+2) (q-1)).mp ha
      simp only [AddedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,addedCountN13plain,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem added_count_N13isolated (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 14).map (AddedForm.eval q)) e=addedCountN13isolated (q:Int) (e:Int) := by
  simp only [addedGroup,List.map_map,Function.comp_def]
  have hc := count_upper_range (2*q+2) (q-2) e
    (fun a => AddedForm.eval q (.n13isolated a)) 5 ((e=1 ∨ e=3 ∨ e=4) ∨ (e=3*q+1 ∨ e=4*q-1)) (by
      intro a ha
      have hb := (range_mem a (2*q+2) (q-2)).mp ha
      simp only [AddedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,addedCountN13isolated,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem added_count_N13right (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 15).map (AddedForm.eval q)) e=addedCountN13right (q:Int) (e:Int) := by
  simp only [addedGroup,List.map_map,Function.comp_def]
  have hc := count_upper_range (3*q+1) (q-3) e
    (fun a => AddedForm.eval q (.n13right a)) 5 ((e=1 ∨ e=3 ∨ e=4) ∨ (e=4*q-1)) (by
      intro a ha
      have hb := (range_mem a (3*q+1) (q-3)).mp ha
      simp only [AddedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,addedCountN13right,I]
  all_goals repeat first | omega | (split <;> simp_all)

end
end LuRazSixRowSpectrum

