import LuRazParametric
import RangeCounting

namespace LuRazParametric
open LuRazCounting
noncomputable section

def weight (q e i : Nat) : Int := by
  classical
  exact mark (Row q i e)

def piece0 (q e i : Nat) : Prop := (i = 0) ∧ (1 ≤ e ∧ e ≤ 4*q)
def piece1 (q e i : Nat) : Prop := (i = 1) ∧ (e = 2 ∨ (2*q+1 ≤ e ∧ e ≤ 4*q))
def piece2 (q e i : Nat) : Prop := (i = 2) ∧ (e = 1 ∨ (3 ≤ e ∧ e ≤ 2*q) ∨ e = 4*q)
def piece3 (q e i : Nat) : Prop := (i = 3) ∧ (e = 1 ∨ (4 ≤ e ∧ e ≤ 2*q+2))
def piece4 (q e i : Nat) : Prop := (i = 4) ∧ (e = 1 ∨ e = 3 ∨ (2*q+3 ≤ e ∧ e ≤ 4*q))
def piece5 (q e i : Nat) : Prop := (5 ≤ i ∧ i ≤ q+2) ∧ (e = 1 ∨ e = 4 ∨ (i+1 ≤ e ∧ e+2 ≤ 2*q+i))
def piece6 (q e i : Nat) : Prop := (q+3 ≤ i ∧ i ≤ 2*q) ∧ (e = 1 ∨ e = 4 ∨ (i+1 ≤ e ∧ e+3 ≤ 2*q+i))
def piece7 (q e i : Nat) : Prop := (i = 2*q+1) ∧ (e = 2 ∨ e = 4 ∨ (2*q+2 ≤ e ∧ e+2 ≤ 4*q))
def piece8 (q e i : Nat) : Prop := (i = 2*q+2) ∧ (e = 2 ∨ e = 4 ∨ (2*q+3 ≤ e ∧ e+1 ≤ 4*q))
def piece9 (q e i : Nat) : Prop := (i = 2*q+3) ∧ (e = 2 ∨ e = 3 ∨ (2*q+4 ≤ e ∧ e ≤ 4*q))
def piece10 (q e i : Nat) : Prop := (2*q+4 ≤ i ∧ i ≤ 3*q) ∧ (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e+2*q ≤ i+1) ∨ (i+1 ≤ e ∧ e ≤ 4*q))
def piece11 (q e i : Nat) : Prop := (i = 3*q+1) ∧ (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e ≤ q+3) ∨ (3*q+2 ≤ e ∧ e+1 ≤ 4*q))
def piece12 (q e i : Nat) : Prop := (3*q+2 ≤ i ∧ i+1 ≤ 4*q) ∧ (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e+2*q ≤ i+2) ∨ (i+1 ≤ e ∧ e ≤ 4*q))
def piece13 (q e i : Nat) : Prop := (i = 4*q) ∧ (e = 3 ∨ (5 ≤ e ∧ e ≤ 2*q+2) ∨ e = 3*q+1)
def piece14 (q e i : Nat) : Prop := (i = 4*q+1) ∧ (3*q+2 ≤ e ∧ e ≤ 4*q)
def piece15 (q e i : Nat) : Prop := (i = 4*q+2) ∧ (e = 1 ∨ (5 ≤ e ∧ e ≤ q+2))

def parts (q e i : Nat) : Int := by
  classical
  exact mark (piece0 q e i) + mark (piece1 q e i) + mark (piece2 q e i) + mark (piece3 q e i) + mark (piece4 q e i) + mark (piece5 q e i) + mark (piece6 q e i) + mark (piece7 q e i) + mark (piece8 q e i) + mark (piece9 q e i) + mark (piece10 q e i) + mark (piece11 q e i) + mark (piece12 q e i) + mark (piece13 q e i) + mark (piece14 q e i) + mark (piece15 q e i)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem row_weights_decompose (q e i : Nat) (hq : 3 ≤ q)
    (hi : i < 4*q+3) : weight q e i = parts q e i := by
  classical
  have hp : (i = 0) ∨ (i = 1) ∨ (i = 2) ∨ (i = 3) ∨ (i = 4) ∨ (5 ≤ i ∧ i ≤ q+2) ∨ (q+3 ≤ i ∧ i ≤ 2*q) ∨ (i = 2*q+1) ∨ (i = 2*q+2) ∨ (i = 2*q+3) ∨ (2*q+4 ≤ i ∧ i ≤ 3*q) ∨ (i = 3*q+1) ∨ (3*q+2 ≤ i ∧ i+1 ≤ 4*q) ∨ (i = 4*q) ∨ (i = 4*q+1) ∨ (i = 4*q+2) := by omega
  rcases hp with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · unfold weight
    rw [row_case_0 q i e hq h0]
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece0 q e i) = mark (1 ≤ e ∧ e ≤ 4*q) := mark_and_true _ _ h0
    simp only [parts, hk, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, hz11, hz12, hz13, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_1 q i e hq h1]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece1 q e i) = mark (e = 2 ∨ (2*q+1 ≤ e ∧ e ≤ 4*q)) := mark_and_true _ _ h1
    simp only [parts, hk, hz0, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, hz11, hz12, hz13, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_2 q i e hq h2]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece2 q e i) = mark (e = 1 ∨ (3 ≤ e ∧ e ≤ 2*q) ∨ e = 4*q) := mark_and_true _ _ h2
    simp only [parts, hk, hz0, hz1, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, hz11, hz12, hz13, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_3 q i e hq h3]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece3 q e i) = mark (e = 1 ∨ (4 ≤ e ∧ e ≤ 2*q+2)) := mark_and_true _ _ h3
    simp only [parts, hk, hz0, hz1, hz2, hz4, hz5, hz6, hz7, hz8, hz9, hz10, hz11, hz12, hz13, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_4 q i e hq h4]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece4 q e i) = mark (e = 1 ∨ e = 3 ∨ (2*q+3 ≤ e ∧ e ≤ 4*q)) := mark_and_true _ _ h4
    simp only [parts, hk, hz0, hz1, hz2, hz3, hz5, hz6, hz7, hz8, hz9, hz10, hz11, hz12, hz13, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_5 q i e hq h5]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece5 q e i) = mark (e = 1 ∨ e = 4 ∨ (i+1 ≤ e ∧ e+2 ≤ 2*q+i)) := mark_and_true _ _ h5
    simp only [parts, hk, hz0, hz1, hz2, hz3, hz4, hz6, hz7, hz8, hz9, hz10, hz11, hz12, hz13, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_6 q i e hq h6]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece6 q e i) = mark (e = 1 ∨ e = 4 ∨ (i+1 ≤ e ∧ e+3 ≤ 2*q+i)) := mark_and_true _ _ h6
    simp only [parts, hk, hz0, hz1, hz2, hz3, hz4, hz5, hz7, hz8, hz9, hz10, hz11, hz12, hz13, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_7 q i e hq h7]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece7 q e i) = mark (e = 2 ∨ e = 4 ∨ (2*q+2 ≤ e ∧ e+2 ≤ 4*q)) := mark_and_true _ _ h7
    simp only [parts, hk, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz8, hz9, hz10, hz11, hz12, hz13, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_8 q i e hq h8]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece8 q e i) = mark (e = 2 ∨ e = 4 ∨ (2*q+3 ≤ e ∧ e+1 ≤ 4*q)) := mark_and_true _ _ h8
    simp only [parts, hk, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz9, hz10, hz11, hz12, hz13, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_9 q i e hq h9]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece9 q e i) = mark (e = 2 ∨ e = 3 ∨ (2*q+4 ≤ e ∧ e ≤ 4*q)) := mark_and_true _ _ h9
    simp only [parts, hk, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz10, hz11, hz12, hz13, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_10 q i e hq h10]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece10 q e i) = mark (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e+2*q ≤ i+1) ∨ (i+1 ≤ e ∧ e ≤ 4*q)) := mark_and_true _ _ h10
    simp only [parts, hk, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz11, hz12, hz13, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_11 q i e hq h11]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece11 q e i) = mark (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e ≤ q+3) ∨ (3*q+2 ≤ e ∧ e+1 ≤ 4*q)) := mark_and_true _ _ h11
    simp only [parts, hk, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, hz12, hz13, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_12 q i e hq h12]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece12 q e i) = mark (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e+2*q ≤ i+2) ∨ (i+1 ≤ e ∧ e ≤ 4*q)) := mark_and_true _ _ h12
    simp only [parts, hk, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, hz11, hz13, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_13 q i e hq h13]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece13 q e i) = mark (e = 3 ∨ (5 ≤ e ∧ e ≤ 2*q+2) ∨ e = 3*q+1) := mark_and_true _ _ h13
    simp only [parts, hk, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, hz11, hz12, hz14, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_14 q i e hq h14]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz15 : mark (piece15 q e i) = 0 := mark_zero _ (by unfold piece15; omega)
    have hk : mark (piece14 q e i) = mark (3*q+2 ≤ e ∧ e ≤ 4*q) := mark_and_true _ _ h14
    simp only [parts, hk, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, hz11, hz12, hz13, hz15, Int.zero_add, Int.add_zero]
  · unfold weight
    rw [row_case_15 q i e hq h15]
    have hz0 : mark (piece0 q e i) = 0 := mark_zero _ (by unfold piece0; omega)
    have hz1 : mark (piece1 q e i) = 0 := mark_zero _ (by unfold piece1; omega)
    have hz2 : mark (piece2 q e i) = 0 := mark_zero _ (by unfold piece2; omega)
    have hz3 : mark (piece3 q e i) = 0 := mark_zero _ (by unfold piece3; omega)
    have hz4 : mark (piece4 q e i) = 0 := mark_zero _ (by unfold piece4; omega)
    have hz5 : mark (piece5 q e i) = 0 := mark_zero _ (by unfold piece5; omega)
    have hz6 : mark (piece6 q e i) = 0 := mark_zero _ (by unfold piece6; omega)
    have hz7 : mark (piece7 q e i) = 0 := mark_zero _ (by unfold piece7; omega)
    have hz8 : mark (piece8 q e i) = 0 := mark_zero _ (by unfold piece8; omega)
    have hz9 : mark (piece9 q e i) = 0 := mark_zero _ (by unfold piece9; omega)
    have hz10 : mark (piece10 q e i) = 0 := mark_zero _ (by unfold piece10; omega)
    have hz11 : mark (piece11 q e i) = 0 := mark_zero _ (by unfold piece11; omega)
    have hz12 : mark (piece12 q e i) = 0 := mark_zero _ (by unfold piece12; omega)
    have hz13 : mark (piece13 q e i) = 0 := mark_zero _ (by unfold piece13; omega)
    have hz14 : mark (piece14 q e i) = 0 := mark_zero _ (by unfold piece14; omega)
    have hk : mark (piece15 q e i) = mark (e = 1 ∨ (5 ≤ e ∧ e ≤ q+2)) := mark_and_true _ _ h15
    simp only [parts, hk, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hz8, hz9, hz10, hz11, hz12, hz13, hz14, Int.zero_add, Int.add_zero]

def col0 (q e : Nat) : Int :=
  mark (1 ≤ e ∧ e ≤ 4*q)

def col1 (q e : Nat) : Int :=
  mark (e = 2 ∨ (2*q+1 ≤ e ∧ e ≤ 4*q))

def col2 (q e : Nat) : Int :=
  mark (e = 1 ∨ (3 ≤ e ∧ e ≤ 2*q) ∨ e = 4*q)

def col3 (q e : Nat) : Int :=
  mark (e = 1 ∨ (4 ≤ e ∧ e ≤ 2*q+2))

def col4 (q e : Nat) : Int :=
  mark (e = 1 ∨ e = 3 ∨ (2*q+3 ≤ e ∧ e ≤ 4*q))

def col5 (q e : Nat) : Int :=
  if e = 1 ∨ e = 4 then intervalCount (4*q+3) (5) ((q : Int)+2) else intervalCount (4*q+3) (max 5 ((e : Int)+2-2*(q : Int))) (min ((q : Int)+2) ((e : Int)-1))

def col6 (q e : Nat) : Int :=
  if e = 1 ∨ e = 4 then intervalCount (4*q+3) ((q : Int)+3) (2*(q : Int)) else intervalCount (4*q+3) (max ((q : Int)+3) ((e : Int)+3-2*(q : Int))) (min (2*(q : Int)) ((e : Int)-1))

def col7 (q e : Nat) : Int :=
  mark (e = 2 ∨ e = 4 ∨ (2*q+2 ≤ e ∧ e+2 ≤ 4*q))

def col8 (q e : Nat) : Int :=
  mark (e = 2 ∨ e = 4 ∨ (2*q+3 ≤ e ∧ e+1 ≤ 4*q))

def col9 (q e : Nat) : Int :=
  mark (e = 2 ∨ e = 3 ∨ (2*q+4 ≤ e ∧ e ≤ 4*q))

def col10 (q e : Nat) : Int :=
  if e = 2 ∨ e = 3 then intervalCount (4*q+3) (2*(q : Int)+4) (3*(q : Int)) else (if 5 ≤ e then intervalCount (4*q+3) (max (2*(q : Int)+4) ((e : Int)+2*(q : Int)-1)) (3*(q : Int)) else 0) + intervalCount (4*q+3) (2*(q : Int)+4) (min (3*(q : Int)) ((e : Int)-1))

def col11 (q e : Nat) : Int :=
  mark (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e ≤ q+3) ∨ (3*q+2 ≤ e ∧ e+1 ≤ 4*q))

def col12 (q e : Nat) : Int :=
  if e = 2 ∨ e = 3 then intervalCount (4*q+3) (3*(q : Int)+2) (4*(q : Int)-1) else (if 5 ≤ e then intervalCount (4*q+3) (max (3*(q : Int)+2) ((e : Int)+2*(q : Int)-2)) (4*(q : Int)-1) else 0) + intervalCount (4*q+3) (3*(q : Int)+2) (min (4*(q : Int)-1) ((e : Int)-1))

def col13 (q e : Nat) : Int :=
  mark (e = 3 ∨ (5 ≤ e ∧ e ≤ 2*q+2) ∨ e = 3*q+1)

def col14 (q e : Nat) : Int :=
  mark (3*q+2 ≤ e ∧ e ≤ 4*q)

def col15 (q e : Nat) : Int :=
  mark (e = 1 ∨ (5 ≤ e ∧ e ≤ q+2))

theorem piece0_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece0 q e i)) (4*q+3) = col0 q e := by
  simpa only [piece0,col0] using sumTo_point_and (4*q+3) (0) (1 ≤ e ∧ e ≤ 4*q) (by omega)

theorem piece1_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece1 q e i)) (4*q+3) = col1 q e := by
  simpa only [piece1,col1] using sumTo_point_and (4*q+3) (1) (e = 2 ∨ (2*q+1 ≤ e ∧ e ≤ 4*q)) (by omega)

theorem piece2_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece2 q e i)) (4*q+3) = col2 q e := by
  simpa only [piece2,col2] using sumTo_point_and (4*q+3) (2) (e = 1 ∨ (3 ≤ e ∧ e ≤ 2*q) ∨ e = 4*q) (by omega)

theorem piece3_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece3 q e i)) (4*q+3) = col3 q e := by
  simpa only [piece3,col3] using sumTo_point_and (4*q+3) (3) (e = 1 ∨ (4 ≤ e ∧ e ≤ 2*q+2)) (by omega)

theorem piece4_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece4 q e i)) (4*q+3) = col4 q e := by
  simpa only [piece4,col4] using sumTo_point_and (4*q+3) (4) (e = 1 ∨ e = 3 ∨ (2*q+3 ≤ e ∧ e ≤ 4*q)) (by omega)

theorem piece5_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece5 q e i)) (4*q+3) = col5 q e := by
  by_cases hc : e = 1 ∨ e = 4
  · rw [col5,if_pos hc]
    calc
      _ = sumTo (fun i => mark ((5) ≤ (i : Int) ∧ (i : Int) ≤ ((q : Int)+2))) (4*q+3) := by
        apply sumTo_congr
        intro i hi
        apply mark_congr
        unfold piece5
        omega
      _ = _ := sumTo_interval (4*q+3) _ _
  · rw [col5,if_neg hc]
    calc
      _ = sumTo (fun i => mark ((max 5 ((e : Int)+2-2*(q : Int))) ≤ (i : Int) ∧ (i : Int) ≤ (min ((q : Int)+2) ((e : Int)-1)))) (4*q+3) := by
        apply sumTo_congr
        intro i hi
        apply mark_congr
        unfold piece5
        omega
      _ = _ := sumTo_interval (4*q+3) _ _

theorem piece6_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece6 q e i)) (4*q+3) = col6 q e := by
  by_cases hc : e = 1 ∨ e = 4
  · rw [col6,if_pos hc]
    calc
      _ = sumTo (fun i => mark (((q : Int)+3) ≤ (i : Int) ∧ (i : Int) ≤ (2*(q : Int)))) (4*q+3) := by
        apply sumTo_congr
        intro i hi
        apply mark_congr
        unfold piece6
        omega
      _ = _ := sumTo_interval (4*q+3) _ _
  · rw [col6,if_neg hc]
    calc
      _ = sumTo (fun i => mark ((max ((q : Int)+3) ((e : Int)+3-2*(q : Int))) ≤ (i : Int) ∧ (i : Int) ≤ (min (2*(q : Int)) ((e : Int)-1)))) (4*q+3) := by
        apply sumTo_congr
        intro i hi
        apply mark_congr
        unfold piece6
        omega
      _ = _ := sumTo_interval (4*q+3) _ _

theorem piece7_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece7 q e i)) (4*q+3) = col7 q e := by
  simpa only [piece7,col7] using sumTo_point_and (4*q+3) (2*q+1) (e = 2 ∨ e = 4 ∨ (2*q+2 ≤ e ∧ e+2 ≤ 4*q)) (by omega)

theorem piece8_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece8 q e i)) (4*q+3) = col8 q e := by
  simpa only [piece8,col8] using sumTo_point_and (4*q+3) (2*q+2) (e = 2 ∨ e = 4 ∨ (2*q+3 ≤ e ∧ e+1 ≤ 4*q)) (by omega)

theorem piece9_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece9 q e i)) (4*q+3) = col9 q e := by
  simpa only [piece9,col9] using sumTo_point_and (4*q+3) (2*q+3) (e = 2 ∨ e = 3 ∨ (2*q+4 ≤ e ∧ e ≤ 4*q)) (by omega)

theorem piece10_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece10 q e i)) (4*q+3) = col10 q e := by
  by_cases hc : e = 2 ∨ e = 3
  · rw [col10,if_pos hc]
    calc
      _ = sumTo (fun i => mark ((2*(q : Int)+4) ≤ (i : Int) ∧ (i : Int) ≤ (3*(q : Int)))) (4*q+3) := by
        apply sumTo_congr
        intro i hi
        apply mark_congr
        unfold piece10
        omega
      _ = _ := sumTo_interval (4*q+3) _ _
  · rw [col10,if_neg hc]
    by_cases he5 : 5 ≤ e
    · rw [if_pos he5]
      calc
        _ = sumTo (fun i => mark ((max (2*(q : Int)+4) ((e : Int)+2*(q : Int)-1)) ≤ (i : Int) ∧ (i : Int) ≤ (3*(q : Int))) + mark ((2*(q : Int)+4) ≤ (i : Int) ∧ (i : Int) ≤ (min (3*(q : Int)) ((e : Int)-1)))) (4*q+3) := by
          apply sumTo_congr
          intro i hi
          unfold piece10 mark
          repeat first | omega | split
        _ = sumTo (fun i => mark ((max (2*(q : Int)+4) ((e : Int)+2*(q : Int)-1)) ≤ (i : Int) ∧ (i : Int) ≤ (3*(q : Int)))) (4*q+3) + sumTo (fun i => mark ((2*(q : Int)+4) ≤ (i : Int) ∧ (i : Int) ≤ (min (3*(q : Int)) ((e : Int)-1)))) (4*q+3) := sumTo_add _ _ _
        _ = _ := by rw [sumTo_interval,sumTo_interval]
    · rw [if_neg he5,Int.zero_add]
      calc
        _ = sumTo (fun i => mark ((2*(q : Int)+4) ≤ (i : Int) ∧ (i : Int) ≤ (min (3*(q : Int)) ((e : Int)-1)))) (4*q+3) := by
          apply sumTo_congr
          intro i hi
          apply mark_congr
          unfold piece10
          omega
        _ = _ := sumTo_interval (4*q+3) _ _

theorem piece11_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece11 q e i)) (4*q+3) = col11 q e := by
  simpa only [piece11,col11] using sumTo_point_and (4*q+3) (3*q+1) (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e ≤ q+3) ∨ (3*q+2 ≤ e ∧ e+1 ≤ 4*q)) (by omega)

theorem piece12_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece12 q e i)) (4*q+3) = col12 q e := by
  by_cases hc : e = 2 ∨ e = 3
  · rw [col12,if_pos hc]
    calc
      _ = sumTo (fun i => mark ((3*(q : Int)+2) ≤ (i : Int) ∧ (i : Int) ≤ (4*(q : Int)-1))) (4*q+3) := by
        apply sumTo_congr
        intro i hi
        apply mark_congr
        unfold piece12
        omega
      _ = _ := sumTo_interval (4*q+3) _ _
  · rw [col12,if_neg hc]
    by_cases he5 : 5 ≤ e
    · rw [if_pos he5]
      calc
        _ = sumTo (fun i => mark ((max (3*(q : Int)+2) ((e : Int)+2*(q : Int)-2)) ≤ (i : Int) ∧ (i : Int) ≤ (4*(q : Int)-1)) + mark ((3*(q : Int)+2) ≤ (i : Int) ∧ (i : Int) ≤ (min (4*(q : Int)-1) ((e : Int)-1)))) (4*q+3) := by
          apply sumTo_congr
          intro i hi
          unfold piece12 mark
          repeat first | omega | split
        _ = sumTo (fun i => mark ((max (3*(q : Int)+2) ((e : Int)+2*(q : Int)-2)) ≤ (i : Int) ∧ (i : Int) ≤ (4*(q : Int)-1))) (4*q+3) + sumTo (fun i => mark ((3*(q : Int)+2) ≤ (i : Int) ∧ (i : Int) ≤ (min (4*(q : Int)-1) ((e : Int)-1)))) (4*q+3) := sumTo_add _ _ _
        _ = _ := by rw [sumTo_interval,sumTo_interval]
    · rw [if_neg he5,Int.zero_add]
      calc
        _ = sumTo (fun i => mark ((3*(q : Int)+2) ≤ (i : Int) ∧ (i : Int) ≤ (min (4*(q : Int)-1) ((e : Int)-1)))) (4*q+3) := by
          apply sumTo_congr
          intro i hi
          apply mark_congr
          unfold piece12
          omega
        _ = _ := sumTo_interval (4*q+3) _ _

theorem piece13_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece13 q e i)) (4*q+3) = col13 q e := by
  simpa only [piece13,col13] using sumTo_point_and (4*q+3) (4*q) (e = 3 ∨ (5 ≤ e ∧ e ≤ 2*q+2) ∨ e = 3*q+1) (by omega)

theorem piece14_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece14 q e i)) (4*q+3) = col14 q e := by
  simpa only [piece14,col14] using sumTo_point_and (4*q+3) (4*q+1) (3*q+2 ≤ e ∧ e ≤ 4*q) (by omega)

theorem piece15_sum (q e : Nat) (hq : 3 ≤ q) (he1 : 1 ≤ e)
    (he2 : e ≤ 4*q) : sumTo (fun i => mark (piece15 q e i)) (4*q+3) = col15 q e := by
  simpa only [piece15,col15] using sumTo_point_and (4*q+3) (4*q+2) (e = 1 ∨ (5 ≤ e ∧ e ≤ q+2)) (by omega)

def columnTotal (q e : Nat) : Int := col0 q e + col1 q e + col2 q e + col3 q e + col4 q e + col5 q e + col6 q e + col7 q e + col8 q e + col9 q e + col10 q e + col11 q e + col12 q e + col13 q e + col14 q e + col15 q e

theorem frequency_as_columnTotal (q e : Nat) (hq : 3 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) :
    sumTo (weight q e) (4*q+3) = columnTotal q e := by
  calc
    _ = sumTo (parts q e) (4*q+3) := sumTo_congr _ (fun i hi => row_weights_decompose q e i hq hi)
    _ = _ := by
      unfold parts columnTotal
      simp only [sumTo_add]
      rw [piece0_sum q e hq he1 he2, piece1_sum q e hq he1 he2, piece2_sum q e hq he1 he2, piece3_sum q e hq he1 he2, piece4_sum q e hq he1 he2, piece5_sum q e hq he1 he2, piece6_sum q e hq he1 he2, piece7_sum q e hq he1 he2, piece8_sum q e hq he1 he2, piece9_sum q e hq he1 he2, piece10_sum q e hq he1 he2, piece11_sum q e hq he1 he2, piece12_sum q e hq he1 he2, piece13_sum q e hq he1 he2, piece14_sum q e hq he1 he2, piece15_sum q e hq he1 he2]


end
end LuRazParametric
