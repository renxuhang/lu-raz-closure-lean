import SixRowDifferenceCountsDefs
import SixRowDifferenceLists
import VariantSpectrumTools

namespace LuRazSixRowSpectrum
open LuRazClosure LuRazEnumeration LuRazThreeRow LuRazCounting
open LuRazSixRowClosure.Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

theorem removed_finite_count_0 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 0).map (RemovedForm.eval q)) e=
      removedCountR2 (q:Int) (e:Int) := by
  classical
  simp only [removedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,removedCountR2]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem removed_finite_count_1 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 1).map (RemovedForm.eval q)) e=
      removedCountR3 (q:Int) (e:Int) := by
  classical
  simp only [removedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,removedCountR3]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem removed_finite_count_2 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 2).map (RemovedForm.eval q)) e=
      removedCountR4 (q:Int) (e:Int) := by
  classical
  simp only [removedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,removedCountR4]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem removed_finite_count_3 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 3).map (RemovedForm.eval q)) e=
      removedCountR5 (q:Int) (e:Int) := by
  classical
  simp only [removedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,removedCountR5]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem removed_finite_count_5 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 5).map (RemovedForm.eval q)) e=
      removedCountR6C_exception (q:Int) (e:Int) := by
  classical
  simp only [removedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,removedCountR6C_exception]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem removed_finite_count_7 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 7).map (RemovedForm.eval q)) e=
      removedCountR7fresh (q:Int) (e:Int) := by
  classical
  simp only [removedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,removedCountR7fresh]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem removed_finite_count_14 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 14).map (RemovedForm.eval q)) e=
      removedCountR12 (q:Int) (e:Int) := by
  classical
  simp only [removedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,removedCountR12]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem removed_finite_count_18 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 18).map (RemovedForm.eval q)) e=
      removedCountR13points (q:Int) (e:Int) := by
  classical
  simp only [removedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,removedCountR13points]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem removed_finite_count_19 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 19).map (RemovedForm.eval q)) e=
      removedCountR14points (q:Int) (e:Int) := by
  classical
  simp only [removedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,removedCountR14points]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem removed_finite_count_22 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((removedGroup q 22).map (RemovedForm.eval q)) e=
      removedCountR15points (q:Int) (e:Int) := by
  classical
  simp only [removedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [RemovedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,removedCountR15points]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem added_finite_count_0 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 0).map (AddedForm.eval q)) e=
      addedCountN4 (q:Int) (e:Int) := by
  classical
  simp only [addedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,addedCountN4]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem added_finite_count_1 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 1).map (AddedForm.eval q)) e=
      addedCountN5 (q:Int) (e:Int) := by
  classical
  simp only [addedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,addedCountN5]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem added_finite_count_3 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 3).map (AddedForm.eval q)) e=
      addedCountN6C_exception (q:Int) (e:Int) := by
  classical
  simp only [addedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,addedCountN6C_exception]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem added_finite_count_6 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 6).map (AddedForm.eval q)) e=
      addedCountN7C_exception (q:Int) (e:Int) := by
  classical
  simp only [addedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,addedCountN7C_exception]
  simp_all
  repeat' first | omega | split <;> simp_all

theorem added_finite_count_8 (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    CountAt ((addedGroup q 8).map (AddedForm.eval q)) e=
      addedCountN7point (q:Int) (e:Int) := by
  classical
  simp only [addedGroup,List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Nat.reduceAdd,count_at_cons,count_at_singleton]
  simp only [CountAt,List.filter_nil,List.length_nil,Int.natCast_zero]
  simp only [AddedForm.eval,A,B,C,Ct,Cp,Lp,Zp,Ep,Lnew,I,mark,addedCountN7point]
  simp_all
  repeat' first | omega | split <;> simp_all

end LuRazSixRowSpectrum
