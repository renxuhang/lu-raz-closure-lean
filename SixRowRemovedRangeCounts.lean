import SixRowRangeCountTools

namespace LuRazSixRowSpectrum
open LuRazClosure LuRazEnumeration LuRazThreeRow LuRazSixRowClosure Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
noncomputable section

theorem removed_count_R7E (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 8).map (RemovedForm.eval q)) e=removedCountR7E (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  have hc := count_upper_range (4) (q-2) e
    (fun a => RemovedForm.eval q (.r7e a)) 5 ((e=1 ∨ e=2 ∨ e=3) ∨ (I (2*q+3) (4*q) e)) (by
      intro a ha
      have hb := (range_mem a (4) (q-2)).mp ha
      simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR7E,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem removed_count_R7D (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 9).map (RemovedForm.eval q)) e=removedCountR7D (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  have hc := count_upper_range (4) (2*q-4) e
    (fun a => RemovedForm.eval q (.r7d a)) 5 ((e=1 ∨ e=2 ∨ e=3) ∨ (I (2*q+1) (4*q) e)) (by
      intro a ha
      have hb := (range_mem a (4) (2*q-4)).mp ha
      simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR7D,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem removed_count_R10 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 10).map (RemovedForm.eval q)) e=removedCountR10 (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  have hc := count_lower_range (2*q+2) (2) e
    (fun a => RemovedForm.eval q (.r10 a)) 0 (4*(q:Int)-1) ((e=2 ∨ e=4)) (by
      intro a ha
      have hb := (range_mem a (2*q+2) (2)).mp ha
      simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR10,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem removed_count_R11J (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 11).map (RemovedForm.eval q)) e=removedCountR11J (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  have hc := count_lower_range (5) (2*q-3) e
    (fun a => RemovedForm.eval q (.r11j a)) 0 (4*(q:Int)-1) ((e=1 ∨ e=2 ∨ e=4)) (by
      intro a ha
      have hb := (range_mem a (5) (2*q-3)).mp ha
      simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR11J,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem removed_count_R11AJ (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 12).map (RemovedForm.eval q)) e=removedCountR11AJ (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  have hc := count_lower_range (q+4) (q-2) e
    (fun a => RemovedForm.eval q (.r11aj a)) 0 (4*(q:Int)-1) ((e=1 ∨ e=2 ∨ e=4) ∨ (I 5 (q+2) e)) (by
      intro a ha
      have hb := (range_mem a (q+4) (q-2)).mp ha
      simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR11AJ,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem removed_count_R11AK (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 13).map (RemovedForm.eval q)) e=removedCountR11AK (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  have hc := count_lower_range (2*q+2) (2) e
    (fun a => RemovedForm.eval q (.r11ak a)) 0 (4*(q:Int)-1) ((e=1 ∨ e=2 ∨ e=4) ∨ (I 5 (q+2) e)) (by
      intro a ha
      have hb := (range_mem a (2*q+2) (2)).mp ha
      simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR11AK,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem removed_count_R13CJ (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 15).map (RemovedForm.eval q)) e=removedCountR13CJ (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  have hc := count_upper_range (2*q+2) (q-2) e
    (fun a => RemovedForm.eval q (.r13cj a)) 5 ((e=1 ∨ e=3 ∨ e=4) ∨ (e=3*q+1)) (by
      intro a ha
      have hb := (range_mem a (2*q+2) (q-2)).mp ha
      simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR13CJ,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem removed_count_R13ZJ (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 16).map (RemovedForm.eval q)) e=removedCountR13ZJ (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  have hc := count_upper_range (2*q+2) (2*q-4) e
    (fun a => RemovedForm.eval q (.r13zj a)) 5 ((e=1 ∨ e=3 ∨ e=4) ∨ (e=4*q)) (by
      intro a ha
      have hb := (range_mem a (2*q+2) (2*q-4)).mp ha
      simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR13ZJ,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem removed_count_R13CZJ (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 17).map (RemovedForm.eval q)) e=removedCountR13CZJ (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  have hc := count_upper_range (2*q+2) (q-2) e
    (fun a => RemovedForm.eval q (.r13czj a)) 5 ((e=1 ∨ e=3 ∨ e=4) ∨ (e=3*q+1 ∨ e=4*q)) (by
      intro a ha
      have hb := (range_mem a (2*q+2) (q-2)).mp ha
      simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR13CZJ,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem removed_count_R14line (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 20).map (RemovedForm.eval q)) e=removedCountR14line (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  have hc := count_lower_range (2*q+4) (2*q-4) e
    (fun a => RemovedForm.eval q (.r14line a)) 0 (4*(q:Int)) ((e=2 ∨ e=3 ∨ e=4) ∨ (I 5 (2*q+1) e)) (by
      intro a ha
      have hb := (range_mem a (2*q+4) (2*q-4)).mp ha
      simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR14line,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem removed_count_R15right (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 23).map (RemovedForm.eval q)) e=removedCountR15right (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  have hc := count_lower_range (6) (2*q-3) e
    (fun a => RemovedForm.eval q (.r15right a)) 0 (4*(q:Int)-2) ((e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (e=4*q)) (by
      intro a ha
      have hb := (range_mem a (6) (2*q-3)).mp ha
      simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR15right,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem removed_count_R15gap (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 24).map (RemovedForm.eval q)) e=removedCountR15gap (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  have hc := count_lower_range (q+4) (q-1) e
    (fun a => RemovedForm.eval q (.r15gap a)) 0 (4*(q:Int)-2) ((e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (I 5 (q+2) e ∨ e=4*q)) (by
      intro a ha
      have hb := (range_mem a (q+4) (q-1)).mp ha
      simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR15gap,I]
  all_goals repeat first | omega | (split <;> simp_all)

theorem removed_count_R15line (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 25).map (RemovedForm.eval q)) e=removedCountR15line (q:Int) (e:Int) := by
  simp only [removedGroup,List.map_map,Function.comp_def]
  have hc := count_lower_range (2*q+4) (2*q-4) e
    (fun a => RemovedForm.eval q (.r15line a)) 0 (4*(q:Int)) ((e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (I 5 (2*q+1) e)) (by
      intro a ha
      have hb := (range_mem a (2*q+4) (2*q-4)).mp ha
      simp only [RemovedForm.eval,Difference.A,Difference.B,Difference.C,Difference.Ct,Difference.Cp,
        Difference.Lp,Difference.Zp,Difference.Ep,Difference.Lnew,Difference.Suffix,I]
      omega)
  rw [hc]
  clear hc
  by_cases hfirst : (5:Int)≤(e:Int) <;>
    by_cases hlast1 : (e:Int)≤4*(q:Int)+ -1 <;>
    by_cases hlast2 : (e:Int)≤4*(q:Int)+ -2
  all_goals simp [hfirst,hlast1,hlast2,indicator_as_bool,lowerRangeCount,upperRangeCount,removedCountR15line,I]
  all_goals repeat first | omega | (split <;> simp_all)

end
end LuRazSixRowSpectrum

