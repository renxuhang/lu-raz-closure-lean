import SixRowDifferenceCountsDefs
namespace LuRazSixRowSpectrum
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
theorem delta_four_0 (q e : Int) (h0: 0≤(q + -4)) (h1: 0≤(e + -1)) (h2: 0≤((4)*q + (-1)*e)) (h3: 0≤(e + -4)) (h4: 0≤((-1)*e + 4)) :
    (addedGroupCounts q e).sum-(removedGroupCounts q e).sum=((-12)*q + 12) := by
  have v0 : ¬((e) = (1)) := by (try simp only [ite_true,ite_false,and_true,true_and,and_false,false_and,or_true,true_or,or_false,false_or,not_true_eq_false,not_false_eq_true]) <;> (omega)
  have v1 : ¬((e) = (2)) := by (try simp only [v0,ite_true,ite_false,and_true,true_and,and_false,false_and,or_true,true_or,or_false,false_or,not_true_eq_false,not_false_eq_true]) <;> (clear v0; omega)
  have v2 : ¬((e) = (3)) := by (try simp only [v0,v1,ite_true,ite_false,and_true,true_and,and_false,false_and,or_true,true_or,or_false,false_or,not_true_eq_false,not_false_eq_true]) <;> (clear v0 v1; omega)
  have v3 : ((e) = (4)) := by (try simp only [v0,v1,v2,ite_true,ite_false,and_true,true_and,and_false,false_and,or_true,true_or,or_false,false_or,not_true_eq_false,not_false_eq_true]) <;> (clear v0 v1 v2; omega)
  have heq : e=(4) := by omega
  simp (maxSteps := 1000000) only [addedGroupCounts,removedGroupCounts,List.sum_cons,List.sum_nil,addedCountN4,addedCountN5,addedCountN6C_regular,addedCountN6C_exception,addedCountN6E,addedCountN7C_regular,addedCountN7C_exception,addedCountN7right,addedCountN7point,addedCountN10,addedCountN11J,addedCountN11AJ,addedCountN11AK,addedCountN13plain,addedCountN13isolated,addedCountN13right,removedCountR2,removedCountR3,removedCountR4,removedCountR5,removedCountR6C_regular,removedCountR6C_exception,removedCountR6D,removedCountR7fresh,removedCountR7E,removedCountR7D,removedCountR10,removedCountR11J,removedCountR11AJ,removedCountR11AK,removedCountR12,removedCountR13CJ,removedCountR13ZJ,removedCountR13CZJ,removedCountR13points,removedCountR14points,removedCountR14line,removedCountR14C,removedCountR15points,removedCountR15right,removedCountR15gap,removedCountR15line,removedCountR15short,v0,v1,v2,v3,ite_true,ite_false,and_true,true_and,and_false,false_and,or_true,true_or,or_false,false_or,not_true_eq_false,not_false_eq_true,Int.zero_add,Int.add_zero,Int.mul_zero,Int.zero_mul,Int.mul_one,Int.one_mul]
  try simp only [heq]
  all_goals omega
theorem delta_four (q e : Int) (h0: 0≤(q + -4)) (h1: 0≤(e + -1)) (h2: 0≤((4)*q + (-1)*e)) (h3: 0≤(e + -4)) (h4: 0≤((-1)*e + 4)) :
    (addedGroupCounts q e).sum-(removedGroupCounts q e).sum=((-12)*q + 12) := by
  exact delta_four_0 q e (by omega) (by omega) (by omega) (by omega) (by omega)
end LuRazSixRowSpectrum
