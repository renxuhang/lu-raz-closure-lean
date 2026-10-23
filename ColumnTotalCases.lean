import LuRazFrequencyBase
namespace LuRazParametric
open LuRazCounting
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
theorem column_small3 (e : Nat) (he1 : 1 ≤ e) (he2 : e ≤ 12) :
    columnTotal 3 e = 7 := by
  have hp : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7 ∨ e = 8 ∨ e = 9 ∨ e = 10 ∨ e = 11 ∨ e = 12 := by omega
  rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
theorem column_small4 (e : Nat) (he1 : 1 ≤ e) (he2 : e ≤ 16) :
    columnTotal 4 e = 9 := by
  have hp : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7 ∨ e = 8 ∨ e = 9 ∨ e = 10 ∨ e = 11 ∨ e = 12 ∨ e = 13 ∨ e = 14 ∨ e = 15 ∨ e = 16 := by omega
  rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
theorem column_small5 (e : Nat) (he1 : 1 ≤ e) (he2 : e ≤ 20) :
    columnTotal 5 e = 11 := by
  have hp : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7 ∨ e = 8 ∨ e = 9 ∨ e = 10 ∨ e = 11 ∨ e = 12 ∨ e = 13 ∨ e = 14 ∨ e = 15 ∨ e = 16 ∨ e = 17 ∨ e = 18 ∨ e = 19 ∨ e = 20 := by omega
  rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
  · subst e
    unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
    simp (disch := decide) only [ite_eq_left,ite_eq_right]
    decide
theorem column_case0 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = 1) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case1 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = 2) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case2 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = 3) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case3 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = 4) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case4 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = 5) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case5 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : 6 ≤ e ∧ e ≤ q+1) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case6 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = q+2) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case7 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = q+3) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case8 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = q+4) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case9 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : q+5 ≤ e ∧ e ≤ 2*q) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case10 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = 2*q+1) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case11 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = 2*q+2) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case12 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = 2*q+3) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case13 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = 2*q+4) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case14 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : 2*q+5 ≤ e ∧ e ≤ 3*q) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case15 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = 3*q+1) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case16 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = 3*q+2) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case17 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : 3*q+3 ≤ e ∧ e+2 ≤ 4*q) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case18 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e+1 = 4*q) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem column_case19 (q e : Nat) (hq : 6 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) (hc : e = 4*q) :
    columnTotal q e = 2*(q : Int)+1 := by
  unfold columnTotal col0 col1 col2 col3 col4 col5 col6 col7 col8 col9 col10 col11 col12 col13 col14 col15 mark
  simp (disch := omega) only [ite_eq_left,ite_eq_right]
  unfold intervalCount
  omega

theorem columnTotal_value (q e : Nat) (hq : 3 ≤ q)
    (he1 : 1 ≤ e) (he2 : e ≤ 4*q) : columnTotal q e = 2*(q : Int)+1 := by
  by_cases hq3 : q = 3
  · subst q
    simpa using column_small3 e he1 he2
  by_cases hq4 : q = 4
  · subst q
    simpa using column_small4 e he1 he2
  by_cases hq5 : q = 5
  · subst q
    simpa using column_small5 e he1 he2
  have hq6 : 6 ≤ q := by omega
  have hp : (e = 1) ∨ (e = 2) ∨ (e = 3) ∨ (e = 4) ∨ (e = 5) ∨ (6 ≤ e ∧ e ≤ q+1) ∨ (e = q+2) ∨ (e = q+3) ∨ (e = q+4) ∨ (q+5 ≤ e ∧ e ≤ 2*q) ∨ (e = 2*q+1) ∨ (e = 2*q+2) ∨ (e = 2*q+3) ∨ (e = 2*q+4) ∨ (2*q+5 ≤ e ∧ e ≤ 3*q) ∨ (e = 3*q+1) ∨ (e = 3*q+2) ∨ (3*q+3 ≤ e ∧ e+2 ≤ 4*q) ∨ (e+1 = 4*q) ∨ (e = 4*q) := by omega
  rcases hp with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19
  · exact column_case0 q e hq6 he1 he2 h0
  · exact column_case1 q e hq6 he1 he2 h1
  · exact column_case2 q e hq6 he1 he2 h2
  · exact column_case3 q e hq6 he1 he2 h3
  · exact column_case4 q e hq6 he1 he2 h4
  · exact column_case5 q e hq6 he1 he2 h5
  · exact column_case6 q e hq6 he1 he2 h6
  · exact column_case7 q e hq6 he1 he2 h7
  · exact column_case8 q e hq6 he1 he2 h8
  · exact column_case9 q e hq6 he1 he2 h9
  · exact column_case10 q e hq6 he1 he2 h10
  · exact column_case11 q e hq6 he1 he2 h11
  · exact column_case12 q e hq6 he1 he2 h12
  · exact column_case13 q e hq6 he1 he2 h13
  · exact column_case14 q e hq6 he1 he2 h14
  · exact column_case15 q e hq6 he1 he2 h15
  · exact column_case16 q e hq6 he1 he2 h16
  · exact column_case17 q e hq6 he1 he2 h17
  · exact column_case18 q e hq6 he1 he2 h18
  · exact column_case19 q e hq6 he1 he2 h19

end
end LuRazParametric
