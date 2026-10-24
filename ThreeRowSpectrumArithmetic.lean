import ThreeRowSpectrumDeltaDefs

namespace LuRazThreeRow
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem tail_delta_left1 (q e : Int) (hq : 4≤q) (hregion : 5≤e ∧ e≤q+2) :
    tailDelta q e = deltaPolynomial q e := by
  have ha0 : 5≤e := by omega
  have ha1 : e≤q+2 := by omega
  have ha2 : ¬(2*q+3≤e) := by omega
  have ha3 : e≤4*q := by omega
  have ha4 : e≤2*q+1 := by omega
  have ha5 : e≤2*q+2 := by omega
  have ha6 : ¬(e=3*q+1) := by omega
  have ha7 : ¬(e=4*q) := by omega
  have ha8 : e≤2*q := by omega
  have ha9 : ¬(3*q+2≤e) := by omega
  have ha10 : ¬(2*q+2≤e) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(4*q-1≤e) := by omega
  have ha13 : ¬(3*q+1≤e) := by omega
  have ha14 : ¬(e=1) := by omega
  have ha15 : ¬(e=2) := by omega
  have ha16 : ¬(e=3) := by omega
  have ha17 : ¬(e=4) := by omega
  have ha18 : ¬(e=2*q+1) := by omega
  have ha19 : ¬(e=2*q+2) := by omega
  have ha20 : e≤3*q := by omega
  have ha21 : ¬(e=4*q-1) := by omega
  simp only [tailDelta,addedTailGroups,removedTailGroups,tailLower,tailUpper,tailMark,deltaPolynomial,
    List.sum_cons,List.sum_nil,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ha13,ha14,ha15,ha16,ha17,ha18,ha19,ha20,ha21,
    and_true,and_false,true_and,false_and,or_true,or_false,true_or,false_or,ite_true,ite_false]
  omega

theorem tail_delta_left2 (q e : Int) (hq : 4≤q) (hregion : q+3≤e ∧ e≤2*q) :
    tailDelta q e = deltaPolynomial q e := by
  have ha0 : 5≤e := by omega
  have ha1 : ¬(e≤q+2) := by omega
  have ha2 : ¬(2*q+3≤e) := by omega
  have ha3 : e≤4*q := by omega
  have ha4 : e≤2*q+1 := by omega
  have ha5 : e≤2*q+2 := by omega
  have ha6 : ¬(e=3*q+1) := by omega
  have ha7 : ¬(e=4*q) := by omega
  have ha8 : e≤2*q := by omega
  have ha9 : ¬(3*q+2≤e) := by omega
  have ha10 : ¬(2*q+2≤e) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(4*q-1≤e) := by omega
  have ha13 : ¬(3*q+1≤e) := by omega
  have ha14 : ¬(e=1) := by omega
  have ha15 : ¬(e=2) := by omega
  have ha16 : ¬(e=3) := by omega
  have ha17 : ¬(e=4) := by omega
  have ha18 : ¬(e=2*q+1) := by omega
  have ha19 : ¬(e=2*q+2) := by omega
  have ha20 : e≤3*q := by omega
  have ha21 : ¬(e=4*q-1) := by omega
  simp only [tailDelta,addedTailGroups,removedTailGroups,tailLower,tailUpper,tailMark,deltaPolynomial,
    List.sum_cons,List.sum_nil,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ha13,ha14,ha15,ha16,ha17,ha18,ha19,ha20,ha21,
    and_true,and_false,true_and,false_and,or_true,or_false,true_or,false_or,ite_true,ite_false]
  omega

theorem tail_delta_h1 (q e : Int) (hq : 4≤q) (hregion : e=2*q+1) :
    tailDelta q e = deltaPolynomial q e := by
  have ha0 : 5≤e := by omega
  have ha1 : ¬(e≤q+2) := by omega
  have ha2 : ¬(2*q+3≤e) := by omega
  have ha3 : e≤4*q := by omega
  have ha4 : e≤2*q+1 := by omega
  have ha5 : e≤2*q+2 := by omega
  have ha6 : ¬(e=3*q+1) := by omega
  have ha7 : ¬(e=4*q) := by omega
  have ha8 : ¬(e≤2*q) := by omega
  have ha9 : ¬(3*q+2≤e) := by omega
  have ha10 : ¬(2*q+2≤e) := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(4*q-1≤e) := by omega
  have ha13 : ¬(3*q+1≤e) := by omega
  have ha14 : ¬(e=1) := by omega
  have ha15 : ¬(e=2) := by omega
  have ha16 : ¬(e=3) := by omega
  have ha17 : ¬(e=4) := by omega
  have ha18 : e=2*q+1 := by omega
  have ha19 : ¬(e=2*q+2) := by omega
  have ha20 : e≤3*q := by omega
  have ha21 : ¬(e=4*q-1) := by omega
  simp only [tailDelta,addedTailGroups,removedTailGroups,tailLower,tailUpper,tailMark,deltaPolynomial,
    List.sum_cons,List.sum_nil,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ha13,ha14,ha15,ha16,ha17,ha18,ha19,ha20,ha21,
    and_true,and_false,true_and,false_and,or_true,or_false,true_or,false_or,ite_true,ite_false]
  omega

theorem tail_delta_h2 (q e : Int) (hq : 4≤q) (hregion : e=2*q+2) :
    tailDelta q e = deltaPolynomial q e := by
  have ha0 : 5≤e := by omega
  have ha1 : ¬(e≤q+2) := by omega
  have ha2 : ¬(2*q+3≤e) := by omega
  have ha3 : e≤4*q := by omega
  have ha4 : ¬(e≤2*q+1) := by omega
  have ha5 : e≤2*q+2 := by omega
  have ha6 : ¬(e=3*q+1) := by omega
  have ha7 : ¬(e=4*q) := by omega
  have ha8 : ¬(e≤2*q) := by omega
  have ha9 : ¬(3*q+2≤e) := by omega
  have ha10 : 2*q+2≤e := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(4*q-1≤e) := by omega
  have ha13 : ¬(3*q+1≤e) := by omega
  have ha14 : ¬(e=1) := by omega
  have ha15 : ¬(e=2) := by omega
  have ha16 : ¬(e=3) := by omega
  have ha17 : ¬(e=4) := by omega
  have ha18 : ¬(e=2*q+1) := by omega
  have ha19 : e=2*q+2 := by omega
  have ha20 : e≤3*q := by omega
  have ha21 : ¬(e=4*q-1) := by omega
  simp only [tailDelta,addedTailGroups,removedTailGroups,tailLower,tailUpper,tailMark,deltaPolynomial,
    List.sum_cons,List.sum_nil,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ha13,ha14,ha15,ha16,ha17,ha18,ha19,ha20,ha21,
    and_true,and_false,true_and,false_and,or_true,or_false,true_or,false_or,ite_true,ite_false]
  omega

theorem tail_delta_right1 (q e : Int) (hq : 4≤q) (hregion : 2*q+3≤e ∧ e≤3*q) :
    tailDelta q e = deltaPolynomial q e := by
  have ha0 : 5≤e := by omega
  have ha1 : ¬(e≤q+2) := by omega
  have ha2 : 2*q+3≤e := by omega
  have ha3 : e≤4*q := by omega
  have ha4 : ¬(e≤2*q+1) := by omega
  have ha5 : ¬(e≤2*q+2) := by omega
  have ha6 : ¬(e=3*q+1) := by omega
  have ha7 : ¬(e=4*q) := by omega
  have ha8 : ¬(e≤2*q) := by omega
  have ha9 : ¬(3*q+2≤e) := by omega
  have ha10 : 2*q+2≤e := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(4*q-1≤e) := by omega
  have ha13 : ¬(3*q+1≤e) := by omega
  have ha14 : ¬(e=1) := by omega
  have ha15 : ¬(e=2) := by omega
  have ha16 : ¬(e=3) := by omega
  have ha17 : ¬(e=4) := by omega
  have ha18 : ¬(e=2*q+1) := by omega
  have ha19 : ¬(e=2*q+2) := by omega
  have ha20 : e≤3*q := by omega
  have ha21 : ¬(e=4*q-1) := by omega
  simp only [tailDelta,addedTailGroups,removedTailGroups,tailLower,tailUpper,tailMark,deltaPolynomial,
    List.sum_cons,List.sum_nil,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ha13,ha14,ha15,ha16,ha17,ha18,ha19,ha20,ha21,
    and_true,and_false,true_and,false_and,or_true,or_false,true_or,false_or,ite_true,ite_false]
  omega

theorem tail_delta_r1 (q e : Int) (hq : 4≤q) (hregion : e=3*q+1) :
    tailDelta q e = deltaPolynomial q e := by
  have ha0 : 5≤e := by omega
  have ha1 : ¬(e≤q+2) := by omega
  have ha2 : 2*q+3≤e := by omega
  have ha3 : e≤4*q := by omega
  have ha4 : ¬(e≤2*q+1) := by omega
  have ha5 : ¬(e≤2*q+2) := by omega
  have ha6 : e=3*q+1 := by omega
  have ha7 : ¬(e=4*q) := by omega
  have ha8 : ¬(e≤2*q) := by omega
  have ha9 : ¬(3*q+2≤e) := by omega
  have ha10 : 2*q+2≤e := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(4*q-1≤e) := by omega
  have ha13 : 3*q+1≤e := by omega
  have ha14 : ¬(e=1) := by omega
  have ha15 : ¬(e=2) := by omega
  have ha16 : ¬(e=3) := by omega
  have ha17 : ¬(e=4) := by omega
  have ha18 : ¬(e=2*q+1) := by omega
  have ha19 : ¬(e=2*q+2) := by omega
  have ha20 : ¬(e≤3*q) := by omega
  have ha21 : ¬(e=4*q-1) := by omega
  simp only [tailDelta,addedTailGroups,removedTailGroups,tailLower,tailUpper,tailMark,deltaPolynomial,
    List.sum_cons,List.sum_nil,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ha13,ha14,ha15,ha16,ha17,ha18,ha19,ha20,ha21,
    and_true,and_false,true_and,false_and,or_true,or_false,true_or,false_or,ite_true,ite_false]
  omega

theorem tail_delta_right2 (q e : Int) (hq : 4≤q) (hregion : 3*q+2≤e ∧ e≤4*q-2) :
    tailDelta q e = deltaPolynomial q e := by
  have ha0 : 5≤e := by omega
  have ha1 : ¬(e≤q+2) := by omega
  have ha2 : 2*q+3≤e := by omega
  have ha3 : e≤4*q := by omega
  have ha4 : ¬(e≤2*q+1) := by omega
  have ha5 : ¬(e≤2*q+2) := by omega
  have ha6 : ¬(e=3*q+1) := by omega
  have ha7 : ¬(e=4*q) := by omega
  have ha8 : ¬(e≤2*q) := by omega
  have ha9 : 3*q+2≤e := by omega
  have ha10 : 2*q+2≤e := by omega
  have ha11 : e≤4*q-2 := by omega
  have ha12 : ¬(4*q-1≤e) := by omega
  have ha13 : 3*q+1≤e := by omega
  have ha14 : ¬(e=1) := by omega
  have ha15 : ¬(e=2) := by omega
  have ha16 : ¬(e=3) := by omega
  have ha17 : ¬(e=4) := by omega
  have ha18 : ¬(e=2*q+1) := by omega
  have ha19 : ¬(e=2*q+2) := by omega
  have ha20 : ¬(e≤3*q) := by omega
  have ha21 : ¬(e=4*q-1) := by omega
  simp only [tailDelta,addedTailGroups,removedTailGroups,tailLower,tailUpper,tailMark,deltaPolynomial,
    List.sum_cons,List.sum_nil,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ha13,ha14,ha15,ha16,ha17,ha18,ha19,ha20,ha21,
    and_true,and_false,true_and,false_and,or_true,or_false,true_or,false_or,ite_true,ite_false]
  omega

theorem tail_delta_n1 (q e : Int) (hq : 4≤q) (hregion : e=4*q-1) :
    tailDelta q e = deltaPolynomial q e := by
  have ha0 : 5≤e := by omega
  have ha1 : ¬(e≤q+2) := by omega
  have ha2 : 2*q+3≤e := by omega
  have ha3 : e≤4*q := by omega
  have ha4 : ¬(e≤2*q+1) := by omega
  have ha5 : ¬(e≤2*q+2) := by omega
  have ha6 : ¬(e=3*q+1) := by omega
  have ha7 : ¬(e=4*q) := by omega
  have ha8 : ¬(e≤2*q) := by omega
  have ha9 : 3*q+2≤e := by omega
  have ha10 : 2*q+2≤e := by omega
  have ha11 : ¬(e≤4*q-2) := by omega
  have ha12 : 4*q-1≤e := by omega
  have ha13 : 3*q+1≤e := by omega
  have ha14 : ¬(e=1) := by omega
  have ha15 : ¬(e=2) := by omega
  have ha16 : ¬(e=3) := by omega
  have ha17 : ¬(e=4) := by omega
  have ha18 : ¬(e=2*q+1) := by omega
  have ha19 : ¬(e=2*q+2) := by omega
  have ha20 : ¬(e≤3*q) := by omega
  have ha21 : e=4*q-1 := by omega
  simp only [tailDelta,addedTailGroups,removedTailGroups,tailLower,tailUpper,tailMark,deltaPolynomial,
    List.sum_cons,List.sum_nil,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ha13,ha14,ha15,ha16,ha17,ha18,ha19,ha20,ha21,
    and_true,and_false,true_and,false_and,or_true,or_false,true_or,false_or,ite_true,ite_false]
  omega

theorem tail_delta_n (q e : Int) (hq : 4≤q) (hregion : e=4*q) :
    tailDelta q e = deltaPolynomial q e := by
  have ha0 : 5≤e := by omega
  have ha1 : ¬(e≤q+2) := by omega
  have ha2 : 2*q+3≤e := by omega
  have ha3 : e≤4*q := by omega
  have ha4 : ¬(e≤2*q+1) := by omega
  have ha5 : ¬(e≤2*q+2) := by omega
  have ha6 : ¬(e=3*q+1) := by omega
  have ha7 : e=4*q := by omega
  have ha8 : ¬(e≤2*q) := by omega
  have ha9 : 3*q+2≤e := by omega
  have ha10 : 2*q+2≤e := by omega
  have ha11 : ¬(e≤4*q-2) := by omega
  have ha12 : 4*q-1≤e := by omega
  have ha13 : 3*q+1≤e := by omega
  have ha14 : ¬(e=1) := by omega
  have ha15 : ¬(e=2) := by omega
  have ha16 : ¬(e=3) := by omega
  have ha17 : ¬(e=4) := by omega
  have ha18 : ¬(e=2*q+1) := by omega
  have ha19 : ¬(e=2*q+2) := by omega
  have ha20 : ¬(e≤3*q) := by omega
  have ha21 : ¬(e=4*q-1) := by omega
  simp only [tailDelta,addedTailGroups,removedTailGroups,tailLower,tailUpper,tailMark,deltaPolynomial,
    List.sum_cons,List.sum_nil,ha0,ha1,ha2,ha3,ha4,ha5,ha6,ha7,ha8,ha9,ha10,ha11,ha12,ha13,ha14,ha15,ha16,ha17,ha18,ha19,ha20,ha21,
    and_true,and_false,true_and,false_and,or_true,or_false,true_or,false_or,ite_true,ite_false]
  omega

theorem tail_delta_arithmetic (q e : Int) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    tailDelta q e = deltaPolynomial q e := by
  by_cases h0 : e≤q+2
  · exact tail_delta_left1 q e hq (by omega)
  by_cases h1 : e≤2*q
  · exact tail_delta_left2 q e hq (by omega)
  by_cases h2 : e=2*q+1
  · exact tail_delta_h1 q e hq h2
  by_cases h3 : e=2*q+2
  · exact tail_delta_h2 q e hq h3
  by_cases h4 : e≤3*q
  · exact tail_delta_right1 q e hq (by omega)
  by_cases h5 : e=3*q+1
  · exact tail_delta_r1 q e hq h5
  by_cases h6 : e≤4*q-2
  · exact tail_delta_right2 q e hq (by omega)
  by_cases h7 : e=4*q-1
  · exact tail_delta_n1 q e hq h7
  exact tail_delta_n q e hq (by omega)

end LuRazThreeRow
