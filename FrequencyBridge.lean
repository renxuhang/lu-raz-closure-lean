import LuRazFrequencyBase

namespace LuRazCounting

theorem sumTo_filter (P : Nat → Prop) [DecidablePred P] (n : Nat) :
    sumTo (fun i => mark (P i)) n =
      (((List.range n).filter (fun i => decide (P i))).length : Int) := by
  classical
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simp only [sumTo,ih,List.range_succ,List.filter_append,List.length_append]
    by_cases hn : P n <;> simp [mark,hn] <;> omega

theorem finRange_vals (n : Nat) :
    (List.finRange n).map (fun i => i.val) = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem finRange_filter_length (P : Nat → Prop) [DecidablePred P] (n : Nat) :
    ((List.finRange n).filter (fun i => decide (P i.val))).length =
      ((List.range n).filter (fun i => decide (P i))).length := by
  classical
  have hm := congrArg (fun l : List Nat => (l.filter (fun i => decide (P i))).length)
    (finRange_vals n)
  simpa only [List.filter_map,List.length_map,Function.comp_def] using hm

end LuRazCounting
