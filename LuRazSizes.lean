import FrequencyBridge
namespace LuRazParametric
open LuRazCounting RazReimerPredicates
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def rowTally (q i : Nat) : Int :=
  sumTo (fun e => mark (Row q i (e+1))) (4*q)

def setSize (q : Nat) (i : Fin (4*q+3)) : Nat := by
  classical
  exact ((List.finRange (4*q)).filter (fun e => decide (S q i e))).length

theorem rowTally_size (q : Nat) (i : Fin (4*q+3)) :
    rowTally q i.val = (setSize q i : Int) := by
  classical
  unfold rowTally
  rw [sumTo_filter]
  exact congrArg Int.ofNat (finRange_filter_length (fun e => Row q i.val (e+1)) (4*q)).symm

theorem tally_case0 (q i : Nat) (hq : 3 ≤ q) (hc : i = 0) :
    rowTally q i = 4*(q : Int) := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((0) ≤ (e : Int) ∧ (e : Int) ≤ (4*(q : Int)-1))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_0 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (0) (4*(q : Int)-1) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case1 (q i : Nat) (hq : 3 ≤ q) (hc : i = 1) :
    rowTally q i = 2*(q : Int)+1 := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((1) ≤ (e : Int) ∧ (e : Int) ≤ (1)) + mark ((2*(q : Int)) ≤ (e : Int) ∧ (e : Int) ≤ (4*(q : Int)-1))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_1 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (1) (1) + intervalCount (4*q) (2*(q : Int)) (4*(q : Int)-1) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case2 (q i : Nat) (hq : 3 ≤ q) (hc : i = 2) :
    rowTally q i = 2*(q : Int) := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((0) ≤ (e : Int) ∧ (e : Int) ≤ (0)) + mark ((2) ≤ (e : Int) ∧ (e : Int) ≤ (2*(q : Int)-1)) + mark ((4*(q : Int)-1) ≤ (e : Int) ∧ (e : Int) ≤ (4*(q : Int)-1))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_2 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (0) (0) + intervalCount (4*q) (2) (2*(q : Int)-1) + intervalCount (4*q) (4*(q : Int)-1) (4*(q : Int)-1) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case3 (q i : Nat) (hq : 3 ≤ q) (hc : i = 3) :
    rowTally q i = 2*(q : Int) := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((0) ≤ (e : Int) ∧ (e : Int) ≤ (0)) + mark ((3) ≤ (e : Int) ∧ (e : Int) ≤ (2*(q : Int)+1))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_3 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (0) (0) + intervalCount (4*q) (3) (2*(q : Int)+1) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case4 (q i : Nat) (hq : 3 ≤ q) (hc : i = 4) :
    rowTally q i = 2*(q : Int) := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((0) ≤ (e : Int) ∧ (e : Int) ≤ (0)) + mark ((2) ≤ (e : Int) ∧ (e : Int) ≤ (2)) + mark ((2*(q : Int)+2) ≤ (e : Int) ∧ (e : Int) ≤ (4*(q : Int)-1))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_4 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (0) (0) + intervalCount (4*q) (2) (2) + intervalCount (4*q) (2*(q : Int)+2) (4*(q : Int)-1) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case5 (q i : Nat) (hq : 3 ≤ q) (hc : 5 ≤ i ∧ i ≤ q+2) :
    rowTally q i = 2*(q : Int) := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((0) ≤ (e : Int) ∧ (e : Int) ≤ (0)) + mark ((3) ≤ (e : Int) ∧ (e : Int) ≤ (3)) + mark (((i : Int)) ≤ (e : Int) ∧ (e : Int) ≤ (2*(q : Int)+(i : Int)-3))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_5 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (0) (0) + intervalCount (4*q) (3) (3) + intervalCount (4*q) ((i : Int)) (2*(q : Int)+(i : Int)-3) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case6 (q i : Nat) (hq : 3 ≤ q) (hc : q+3 ≤ i ∧ i ≤ 2*q) :
    rowTally q i = 2*(q : Int)-1 := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((0) ≤ (e : Int) ∧ (e : Int) ≤ (0)) + mark ((3) ≤ (e : Int) ∧ (e : Int) ≤ (3)) + mark (((i : Int)) ≤ (e : Int) ∧ (e : Int) ≤ (2*(q : Int)+(i : Int)-4))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_6 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (0) (0) + intervalCount (4*q) (3) (3) + intervalCount (4*q) ((i : Int)) (2*(q : Int)+(i : Int)-4) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case7 (q i : Nat) (hq : 3 ≤ q) (hc : i = 2*q+1) :
    rowTally q i = 2*(q : Int)-1 := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((1) ≤ (e : Int) ∧ (e : Int) ≤ (1)) + mark ((3) ≤ (e : Int) ∧ (e : Int) ≤ (3)) + mark ((2*(q : Int)+1) ≤ (e : Int) ∧ (e : Int) ≤ (4*(q : Int)-3))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_7 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (1) (1) + intervalCount (4*q) (3) (3) + intervalCount (4*q) (2*(q : Int)+1) (4*(q : Int)-3) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case8 (q i : Nat) (hq : 3 ≤ q) (hc : i = 2*q+2) :
    rowTally q i = 2*(q : Int)-1 := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((1) ≤ (e : Int) ∧ (e : Int) ≤ (1)) + mark ((3) ≤ (e : Int) ∧ (e : Int) ≤ (3)) + mark ((2*(q : Int)+2) ≤ (e : Int) ∧ (e : Int) ≤ (4*(q : Int)-2))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_8 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (1) (1) + intervalCount (4*q) (3) (3) + intervalCount (4*q) (2*(q : Int)+2) (4*(q : Int)-2) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case9 (q i : Nat) (hq : 3 ≤ q) (hc : i = 2*q+3) :
    rowTally q i = 2*(q : Int)-1 := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((1) ≤ (e : Int) ∧ (e : Int) ≤ (1)) + mark ((2) ≤ (e : Int) ∧ (e : Int) ≤ (2)) + mark ((2*(q : Int)+3) ≤ (e : Int) ∧ (e : Int) ≤ (4*(q : Int)-1))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_9 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (1) (1) + intervalCount (4*q) (2) (2) + intervalCount (4*q) (2*(q : Int)+3) (4*(q : Int)-1) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case10 (q i : Nat) (hq : 3 ≤ q) (hc : 2*q+4 ≤ i ∧ i ≤ 3*q) :
    rowTally q i = 2*(q : Int)-1 := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((1) ≤ (e : Int) ∧ (e : Int) ≤ (1)) + mark ((2) ≤ (e : Int) ∧ (e : Int) ≤ (2)) + mark ((4) ≤ (e : Int) ∧ (e : Int) ≤ ((i : Int)-2*(q : Int))) + mark (((i : Int)) ≤ (e : Int) ∧ (e : Int) ≤ (4*(q : Int)-1))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_10 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (1) (1) + intervalCount (4*q) (2) (2) + intervalCount (4*q) (4) ((i : Int)-2*(q : Int)) + intervalCount (4*q) ((i : Int)) (4*(q : Int)-1) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case11 (q i : Nat) (hq : 3 ≤ q) (hc : i = 3*q+1) :
    rowTally q i = 2*(q : Int)-1 := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((1) ≤ (e : Int) ∧ (e : Int) ≤ (1)) + mark ((2) ≤ (e : Int) ∧ (e : Int) ≤ (2)) + mark ((4) ≤ (e : Int) ∧ (e : Int) ≤ ((q : Int)+2)) + mark ((3*(q : Int)+1) ≤ (e : Int) ∧ (e : Int) ≤ (4*(q : Int)-2))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_11 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (1) (1) + intervalCount (4*q) (2) (2) + intervalCount (4*q) (4) ((q : Int)+2) + intervalCount (4*q) (3*(q : Int)+1) (4*(q : Int)-2) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case12 (q i : Nat) (hq : 3 ≤ q) (hc : 3*q+2 ≤ i ∧ i+1 ≤ 4*q) :
    rowTally q i = 2*(q : Int) := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((1) ≤ (e : Int) ∧ (e : Int) ≤ (1)) + mark ((2) ≤ (e : Int) ∧ (e : Int) ≤ (2)) + mark ((4) ≤ (e : Int) ∧ (e : Int) ≤ ((i : Int)-2*(q : Int)+1)) + mark (((i : Int)) ≤ (e : Int) ∧ (e : Int) ≤ (4*(q : Int)-1))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_12 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (1) (1) + intervalCount (4*q) (2) (2) + intervalCount (4*q) (4) ((i : Int)-2*(q : Int)+1) + intervalCount (4*q) ((i : Int)) (4*(q : Int)-1) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case13 (q i : Nat) (hq : 3 ≤ q) (hc : i = 4*q) :
    rowTally q i = 2*(q : Int) := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((2) ≤ (e : Int) ∧ (e : Int) ≤ (2)) + mark ((4) ≤ (e : Int) ∧ (e : Int) ≤ (2*(q : Int)+1)) + mark ((3*(q : Int)) ≤ (e : Int) ∧ (e : Int) ≤ (3*(q : Int)))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_13 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (2) (2) + intervalCount (4*q) (4) (2*(q : Int)+1) + intervalCount (4*q) (3*(q : Int)) (3*(q : Int)) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case14 (q i : Nat) (hq : 3 ≤ q) (hc : i = 4*q+1) :
    rowTally q i = (q : Int)-1 := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((3*(q : Int)+1) ≤ (e : Int) ∧ (e : Int) ≤ (4*(q : Int)-1))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_14 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (3*(q : Int)+1) (4*(q : Int)-1) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem tally_case15 (q i : Nat) (hq : 3 ≤ q) (hc : i = 4*q+2) :
    rowTally q i = (q : Int)-1 := by
  unfold rowTally
  calc
    _ = sumTo (fun e => mark ((0) ≤ (e : Int) ∧ (e : Int) ≤ (0)) + mark ((4) ≤ (e : Int) ∧ (e : Int) ≤ ((q : Int)+1))) (4*q) := by
      apply sumTo_congr
      intro e he
      rw [row_case_15 q i (e+1) hq hc]
      unfold mark
      repeat first | omega | split
    _ = intervalCount (4*q) (0) (0) + intervalCount (4*q) (4) ((q : Int)+1) := by simp only [sumTo_add,sumTo_interval]
    _ = _ := by unfold intervalCount; omega

theorem rowTally_lower (q i : Nat) (hq : 3 ≤ q) (hi : i < 4*q+3) :
    (q : Int)-1 ≤ rowTally q i := by
  have hp : (i = 0) ∨ (i = 1) ∨ (i = 2) ∨ (i = 3) ∨ (i = 4) ∨ (5 ≤ i ∧ i ≤ q+2) ∨ (q+3 ≤ i ∧ i ≤ 2*q) ∨ (i = 2*q+1) ∨ (i = 2*q+2) ∨ (i = 2*q+3) ∨ (2*q+4 ≤ i ∧ i ≤ 3*q) ∨ (i = 3*q+1) ∨ (3*q+2 ≤ i ∧ i+1 ≤ 4*q) ∨ (i = 4*q) ∨ (i = 4*q+1) ∨ (i = 4*q+2) := by omega
  rcases hp with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · rw [tally_case0 q i hq h0]; omega
  · rw [tally_case1 q i hq h1]; omega
  · rw [tally_case2 q i hq h2]; omega
  · rw [tally_case3 q i hq h3]; omega
  · rw [tally_case4 q i hq h4]; omega
  · rw [tally_case5 q i hq h5]; omega
  · rw [tally_case6 q i hq h6]; omega
  · rw [tally_case7 q i hq h7]; omega
  · rw [tally_case8 q i hq h8]; omega
  · rw [tally_case9 q i hq h9]; omega
  · rw [tally_case10 q i hq h10]; omega
  · rw [tally_case11 q i hq h11]; omega
  · rw [tally_case12 q i hq h12]; omega
  · rw [tally_case13 q i hq h13]; omega
  · rw [tally_case14 q i hq h14]; omega
  · rw [tally_case15 q i hq h15]; omega

theorem minimum_size_lower (q : Nat) (hq : 3 ≤ q) (i : Fin (4*q+3)) :
    q-1 ≤ setSize q i := by
  have h := rowTally_lower q i.val hq i.isLt
  rw [rowTally_size] at h
  omega

theorem minimum_size_attained (q : Nat) (hq : 3 ≤ q) :
    setSize q ⟨4*q+1,by omega⟩ = q-1 := by
  have h := tally_case14 q (4*q+1) hq rfl
  have hb := rowTally_size q ⟨4*q+1,by omega⟩
  simp only [Fin.val_mk] at hb
  omega

end
end LuRazParametric
