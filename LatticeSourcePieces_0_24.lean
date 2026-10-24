import LuRazTotalClosure
namespace LuRazClosure
namespace SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
def p0Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p0NF (q a b : Nat) : NFSmall := .bOnly
def p0Set (q a b e : Nat) : Prop := (False) ∨ ((((3)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p0_eval (q a b e : Nat) (hq : 4≤q) (hd : p0Domain q a b) :
    (p0NF q a b).eval q e ↔ p0Set q a b e := by
  simp only [p0Domain] at hd
  simp only [p0NF,p0Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p0_generated (q a b : Nat) (hq : 4≤q) (hd : p0Domain q a b) :
    Generated q (p0Set q a b) := by
  exact generated_congr q (NFSmall.generated q hq (p0NF q a b)) (p0_eval q a b · hq hd)
def p1Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p1NF (q a b : Nat) : NFSmall := .aOnly
def p1Set (q a b e : Nat) : Prop := (e=1) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)))
theorem p1_eval (q a b e : Nat) (hq : 4≤q) (hd : p1Domain q a b) :
    (p1NF q a b).eval q e ↔ p1Set q a b e := by
  simp only [p1Domain] at hd
  simp only [p1NF,p1Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p1_generated (q a b : Nat) (hq : 4≤q) (hd : p1Domain q a b) :
    Generated q (p1Set q a b) := by
  exact generated_congr q (NFSmall.generated q hq (p1NF q a b)) (p1_eval q a b · hq hd)
def p2Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p2NF (q a b : Nat) : NFSmall := .ab
def p2Set (q a b e : Nat) : Prop := (e=1) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((3)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p2_eval (q a b e : Nat) (hq : 4≤q) (hd : p2Domain q a b) :
    (p2NF q a b).eval q e ↔ p2Set q a b e := by
  simp only [p2Domain] at hd
  simp only [p2NF,p2Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p2_generated (q a b : Nat) (hq : 4≤q) (hd : p2Domain q a b) :
    Generated q (p2Set q a b) := by
  exact generated_congr q (NFSmall.generated q hq (p2NF q a b)) (p2_eval q a b · hq hd)
def p3Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p3NF (q a b : Nat) : NFSmall := .dOnly
def p3Set (q a b e : Nat) : Prop := (e=2) ∨ ((((2)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p3_eval (q a b e : Nat) (hq : 4≤q) (hd : p3Domain q a b) :
    (p3NF q a b).eval q e ↔ p3Set q a b e := by
  simp only [p3Domain] at hd
  simp only [p3NF,p3Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p3_generated (q a b : Nat) (hq : 4≤q) (hd : p3Domain q a b) :
    Generated q (p3Set q a b) := by
  exact generated_congr q (NFSmall.generated q hq (p3NF q a b)) (p3_eval q a b · hq hd)
def p4Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p4NF (q a b : Nat) : NFSmall := .ad
def p4Set (q a b e : Nat) : Prop := (e=1 ∨ e=2) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((2)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p4_eval (q a b e : Nat) (hq : 4≤q) (hd : p4Domain q a b) :
    (p4NF q a b).eval q e ↔ p4Set q a b e := by
  simp only [p4Domain] at hd
  simp only [p4NF,p4Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p4_generated (q a b : Nat) (hq : 4≤q) (hd : p4Domain q a b) :
    Generated q (p4Set q a b) := by
  exact generated_congr q (NFSmall.generated q hq (p4NF q a b)) (p4_eval q a b · hq hd)
def p5Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p5NF (q a b : Nat) : NFSmall := .cOnly
def p5Set (q a b e : Nat) : Prop := (e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int)+2)) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((3)*(q:Int)+1)))
theorem p5_eval (q a b e : Nat) (hq : 4≤q) (hd : p5Domain q a b) :
    (p5NF q a b).eval q e ↔ p5Set q a b e := by
  simp only [p5Domain] at hd
  simp only [p5NF,p5Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p5_generated (q a b : Nat) (hq : 4≤q) (hd : p5Domain q a b) :
    Generated q (p5Set q a b) := by
  exact generated_congr q (NFSmall.generated q hq (p5NF q a b)) (p5_eval q a b · hq hd)
def p6Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p6NF (q a b : Nat) : NFSmall := .cb
def p6Set (q a b e : Nat) : Prop := (e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int)+2)) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((3)*(q:Int)+1)) ∨ (((3)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p6_eval (q a b e : Nat) (hq : 4≤q) (hd : p6Domain q a b) :
    (p6NF q a b).eval q e ↔ p6Set q a b e := by
  simp only [p6Domain] at hd
  simp only [p6NF,p6Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p6_generated (q a b : Nat) (hq : 4≤q) (hd : p6Domain q a b) :
    Generated q (p6Set q a b) := by
  exact generated_congr q (NFSmall.generated q hq (p6NF q a b)) (p6_eval q a b · hq hd)
def p7Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p7NF (q a b : Nat) : NFSmall := .eOnly
def p7Set (q a b e : Nat) : Prop := (e=1 ∨ e=3) ∨ ((((2)*(q:Int)+3)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p7_eval (q a b e : Nat) (hq : 4≤q) (hd : p7Domain q a b) :
    (p7NF q a b).eval q e ↔ p7Set q a b e := by
  simp only [p7Domain] at hd
  simp only [p7NF,p7Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p7_generated (q a b : Nat) (hq : 4≤q) (hd : p7Domain q a b) :
    Generated q (p7Set q a b) := by
  exact generated_congr q (NFSmall.generated q hq (p7NF q a b)) (p7_eval q a b · hq hd)
def p8Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p8NF (q a b : Nat) : NFSmall := .ae
def p8Set (q a b e : Nat) : Prop := (e=1 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((2)*(q:Int)+3)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p8_eval (q a b e : Nat) (hq : 4≤q) (hd : p8Domain q a b) :
    (p8NF q a b).eval q e ↔ p8Set q a b e := by
  simp only [p8Domain] at hd
  simp only [p8NF,p8Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p8_generated (q a b : Nat) (hq : 4≤q) (hd : p8Domain q a b) :
    Generated q (p8Set q a b) := by
  exact generated_congr q (NFSmall.generated q hq (p8NF q a b)) (p8_eval q a b · hq hd)
def p9Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p9NF (q a b : Nat) : NFSmall := .ce
def p9Set (q a b e : Nat) : Prop := (e=1 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p9_eval (q a b e : Nat) (hq : 4≤q) (hd : p9Domain q a b) :
    (p9NF q a b).eval q e ↔ p9Set q a b e := by
  simp only [p9Domain] at hd
  simp only [p9NF,p9Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p9_generated (q a b : Nat) (hq : 4≤q) (hd : p9Domain q a b) :
    Generated q (p9Set q a b) := by
  exact generated_congr q (NFSmall.generated q hq (p9NF q a b)) (p9_eval q a b · hq hd)
def p10Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p10NF (q a b : Nat) : NFSmall := .ac
def p10Set (q a b e : Nat) : Prop := (e=1 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int)+2)) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((3)*(q:Int)+1)))
theorem p10_eval (q a b e : Nat) (hq : 4≤q) (hd : p10Domain q a b) :
    (p10NF q a b).eval q e ↔ p10Set q a b e := by
  simp only [p10Domain] at hd
  simp only [p10NF,p10Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p10_generated (q a b : Nat) (hq : 4≤q) (hd : p10Domain q a b) :
    Generated q (p10Set q a b) := by
  exact generated_congr q (NFSmall.generated q hq (p10NF q a b)) (p10_eval q a b · hq hd)
def p11Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p11NF (q a b : Nat) : NFSmall := .acb
def p11Set (q a b e : Nat) : Prop := (e=1 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int)+2)) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((3)*(q:Int)+1)) ∨ (((3)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p11_eval (q a b e : Nat) (hq : 4≤q) (hd : p11Domain q a b) :
    (p11NF q a b).eval q e ↔ p11Set q a b e := by
  simp only [p11Domain] at hd
  simp only [p11NF,p11Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p11_generated (q a b : Nat) (hq : 4≤q) (hd : p11Domain q a b) :
    Generated q (p11Set q a b) := by
  exact generated_congr q (NFSmall.generated q hq (p11NF q a b)) (p11_eval q a b · hq hd)
def p12Domain (q a b : Nat) : Prop := (4)≤(a:Int) ∧ (a:Int)≤((1)*(q:Int)+1) ∧ (4)≤(b:Int) ∧ (b:Int)≤((1)*(q:Int)+1) ∧ (b:Int)≤(a:Int)+(0:Int)
def p12NF (q a b : Nat) : NF23 := .lp b a
def p12Set (q a b e : Nat) : Prop := (e=2 ∨ e=3) ∨ ((((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+(1)*(b:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)))) ∧ ¬(a=q+3 ∧ b=q+3 ∧ e=4*q))
theorem p12_valid (q a b : Nat) (hq : 4≤q) (hd : p12Domain q a b) : (p12NF q a b).Valid q := by
  simp only [p12Domain] at hd
  simp only [p12NF,NF23.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p12_eval (q a b e : Nat) (hq : 4≤q) (hd : p12Domain q a b) :
    (p12NF q a b).eval q e ↔ p12Set q a b e := by
  simp only [p12Domain] at hd
  simp only [p12NF,p12Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p12_generated (q a b : Nat) (hq : 4≤q) (hd : p12Domain q a b) :
    Generated q (p12Set q a b) := by
  exact generated_congr q (NF23.generated q hq (p12NF q a b) (p12_valid q a b hq hd)) (p12_eval q a b · hq hd)
def p13Domain (q a b : Nat) : Prop := (4)≤(a:Int) ∧ (a:Int)≤((1)*(q:Int)+1) ∧ ((1)*(q:Int)+3)≤(b:Int) ∧ (b:Int)≤((2)*(q:Int)+1) ∧ (b:Int)≤(a:Int)+(0:Int)
def p13NF (q a b : Nat) : NF23 := .lp b a
def p13Set (q a b e : Nat) : Prop := (e=2 ∨ e=3) ∨ ((((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+(1)*(b:Int)+(-1))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)))) ∧ ¬(a=q+3 ∧ b=q+3 ∧ e=4*q))
theorem p13_valid (q a b : Nat) (hq : 4≤q) (hd : p13Domain q a b) : (p13NF q a b).Valid q := by
  simp only [p13Domain] at hd
  simp only [p13NF,NF23.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p13_eval (q a b e : Nat) (hq : 4≤q) (hd : p13Domain q a b) :
    (p13NF q a b).eval q e ↔ p13Set q a b e := by
  simp only [p13Domain] at hd
  simp only [p13NF,p13Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p13_generated (q a b : Nat) (hq : 4≤q) (hd : p13Domain q a b) :
    Generated q (p13Set q a b) := by
  exact generated_congr q (NF23.generated q hq (p13NF q a b) (p13_valid q a b hq hd)) (p13_eval q a b · hq hd)
def p14Domain (q a b : Nat) : Prop := ((1)*(q:Int)+3)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ (4)≤(b:Int) ∧ (b:Int)≤((1)*(q:Int)+1) ∧ (b:Int)≤(a:Int)+(0:Int)
def p14NF (q a b : Nat) : NF23 := .lp b a
def p14Set (q a b e : Nat) : Prop := (e=2 ∨ e=3) ∨ ((((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+(1)*(b:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)))) ∧ ¬(a=q+3 ∧ b=q+3 ∧ e=4*q))
theorem p14_valid (q a b : Nat) (hq : 4≤q) (hd : p14Domain q a b) : (p14NF q a b).Valid q := by
  simp only [p14Domain] at hd
  simp only [p14NF,NF23.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p14_eval (q a b e : Nat) (hq : 4≤q) (hd : p14Domain q a b) :
    (p14NF q a b).eval q e ↔ p14Set q a b e := by
  simp only [p14Domain] at hd
  simp only [p14NF,p14Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p14_generated (q a b : Nat) (hq : 4≤q) (hd : p14Domain q a b) :
    Generated q (p14Set q a b) := by
  exact generated_congr q (NF23.generated q hq (p14NF q a b) (p14_valid q a b hq hd)) (p14_eval q a b · hq hd)
def p15Domain (q a b : Nat) : Prop := ((1)*(q:Int)+3)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ ((1)*(q:Int)+3)≤(b:Int) ∧ (b:Int)≤((2)*(q:Int)+1) ∧ (b:Int)≤(a:Int)+(0:Int)
def p15NF (q a b : Nat) : NF23 := .lp b a
def p15Set (q a b e : Nat) : Prop := (e=2 ∨ e=3) ∨ ((((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+(1)*(b:Int)+(-1))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)))) ∧ ¬(a=q+3 ∧ b=q+3 ∧ e=4*q))
theorem p15_valid (q a b : Nat) (hq : 4≤q) (hd : p15Domain q a b) : (p15NF q a b).Valid q := by
  simp only [p15Domain] at hd
  simp only [p15NF,NF23.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p15_eval (q a b e : Nat) (hq : 4≤q) (hd : p15Domain q a b) :
    (p15NF q a b).eval q e ↔ p15Set q a b e := by
  simp only [p15Domain] at hd
  simp only [p15NF,p15Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p15_generated (q a b : Nat) (hq : 4≤q) (hd : p15Domain q a b) :
    Generated q (p15Set q a b) := by
  exact generated_congr q (NF23.generated q hq (p15NF q a b) (p15_valid q a b hq hd)) (p15_eval q a b · hq hd)
def p17Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p17NF (q a b : Nat) : NF23 := .filledM
def p17Set (q a b e : Nat) : Prop := (e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+3)) ∨ (((3)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p17_valid (q a b : Nat) (hq : 4≤q) (hd : p17Domain q a b) : (p17NF q a b).Valid q := by
  simp only [p17Domain] at hd
  simp only [p17NF,NF23.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p17_eval (q a b e : Nat) (hq : 4≤q) (hd : p17Domain q a b) :
    (p17NF q a b).eval q e ↔ p17Set q a b e := by
  simp only [p17Domain] at hd
  simp only [p17NF,p17Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p17_generated (q a b : Nat) (hq : 4≤q) (hd : p17Domain q a b) :
    Generated q (p17Set q a b) := by
  exact generated_congr q (NF23.generated q hq (p17NF q a b) (p17_valid q a b hq hd)) (p17_eval q a b · hq hd)
def p18Domain (q a b : Nat) : Prop := (4)≤(a:Int) ∧ (a:Int)≤((1)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p18NF (q a b : Nat) : NF23 := .dgap a
def p18Set (q a b e : Nat) : Prop := (e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p18_valid (q a b : Nat) (hq : 4≤q) (hd : p18Domain q a b) : (p18NF q a b).Valid q := by
  simp only [p18Domain] at hd
  simp only [p18NF,NF23.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p18_eval (q a b e : Nat) (hq : 4≤q) (hd : p18Domain q a b) :
    (p18NF q a b).eval q e ↔ p18Set q a b e := by
  simp only [p18Domain] at hd
  simp only [p18NF,p18Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p18_generated (q a b : Nat) (hq : 4≤q) (hd : p18Domain q a b) :
    Generated q (p18Set q a b) := by
  exact generated_congr q (NF23.generated q hq (p18NF q a b) (p18_valid q a b hq hd)) (p18_eval q a b · hq hd)
def p19Domain (q a b : Nat) : Prop := ((1)*(q:Int)+3)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+(-1)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p19NF (q a b : Nat) : NF23 := .dgap a
def p19Set (q a b e : Nat) : Prop := (e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p19_valid (q a b : Nat) (hq : 4≤q) (hd : p19Domain q a b) : (p19NF q a b).Valid q := by
  simp only [p19Domain] at hd
  simp only [p19NF,NF23.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p19_eval (q a b e : Nat) (hq : 4≤q) (hd : p19Domain q a b) :
    (p19NF q a b).eval q e ↔ p19Set q a b e := by
  simp only [p19Domain] at hd
  simp only [p19NF,p19Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p19_generated (q a b : Nat) (hq : 4≤q) (hd : p19Domain q a b) :
    Generated q (p19Set q a b) := by
  exact generated_congr q (NF23.generated q hq (p19NF q a b) (p19_valid q a b hq hd)) (p19_eval q a b · hq hd)
def p20Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p20NF (q a b : Nat) : NF23 := .full
def p20Set (q a b e : Nat) : Prop := (e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p20_valid (q a b : Nat) (hq : 4≤q) (hd : p20Domain q a b) : (p20NF q a b).Valid q := by
  simp only [p20Domain] at hd
  simp only [p20NF,NF23.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p20_eval (q a b e : Nat) (hq : 4≤q) (hd : p20Domain q a b) :
    (p20NF q a b).eval q e ↔ p20Set q a b e := by
  simp only [p20Domain] at hd
  simp only [p20NF,p20Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p20_generated (q a b : Nat) (hq : 4≤q) (hd : p20Domain q a b) :
    Generated q (p20Set q a b) := by
  exact generated_congr q (NF23.generated q hq (p20NF q a b) (p20_valid q a b hq hd)) (p20_eval q a b · hq hd)
def p21Domain (q a b : Nat) : Prop := (4)≤(a:Int) ∧ (a:Int)≤((1)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p21NF (q a b : Nat) : NF23 := .creg a
def p21Set (q a b e : Nat) : Prop := (e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int)+2)) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((3)*(q:Int)+1)) ∨ (((2)*(q:Int)+(1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p21_valid (q a b : Nat) (hq : 4≤q) (hd : p21Domain q a b) : (p21NF q a b).Valid q := by
  simp only [p21Domain] at hd
  simp only [p21NF,NF23.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p21_eval (q a b e : Nat) (hq : 4≤q) (hd : p21Domain q a b) :
    (p21NF q a b).eval q e ↔ p21Set q a b e := by
  simp only [p21Domain] at hd
  simp only [p21NF,p21Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p21_generated (q a b : Nat) (hq : 4≤q) (hd : p21Domain q a b) :
    Generated q (p21Set q a b) := by
  exact generated_congr q (NF23.generated q hq (p21NF q a b) (p21_valid q a b hq hd)) (p21_eval q a b · hq hd)
def p22Domain (q a b : Nat) : Prop := ((1)*(q:Int)+4)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p22NF (q a b : Nat) : NF23 := .creg a
def p22Set (q a b e : Nat) : Prop := (e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int)+2)) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((3)*(q:Int)+1)) ∨ (((2)*(q:Int)+(1)*(a:Int)+(-1))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p22_valid (q a b : Nat) (hq : 4≤q) (hd : p22Domain q a b) : (p22NF q a b).Valid q := by
  simp only [p22Domain] at hd
  simp only [p22NF,NF23.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p22_eval (q a b e : Nat) (hq : 4≤q) (hd : p22Domain q a b) :
    (p22NF q a b).eval q e ↔ p22Set q a b e := by
  simp only [p22Domain] at hd
  simp only [p22NF,p22Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p22_generated (q a b : Nat) (hq : 4≤q) (hd : p22Domain q a b) :
    Generated q (p22Set q a b) := by
  exact generated_congr q (NF23.generated q hq (p22NF q a b) (p22_valid q a b hq hd)) (p22_eval q a b · hq hd)
def p23Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p23NF (q a b : Nat) : NF23 := .cexception
def p23Set (q a b e : Nat) : Prop := (e=2 ∨ e=3) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int)+2)) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-1))))
theorem p23_valid (q a b : Nat) (hq : 4≤q) (hd : p23Domain q a b) : (p23NF q a b).Valid q := by
  simp only [p23Domain] at hd
  simp only [p23NF,NF23.Valid,P,JReachable,g]
  repeat first | omega | split
theorem p23_eval (q a b e : Nat) (hq : 4≤q) (hd : p23Domain q a b) :
    (p23NF q a b).eval q e ↔ p23Set q a b e := by
  simp only [p23Domain] at hd
  simp only [p23NF,p23Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p23_generated (q a b : Nat) (hq : 4≤q) (hd : p23Domain q a b) :
    Generated q (p23Set q a b) := by
  exact generated_congr q (NF23.generated q hq (p23NF q a b) (p23_valid q a b hq hd)) (p23_eval q a b · hq hd)
#print axioms p0_eval
#print axioms p0_generated
#print axioms p1_eval
#print axioms p1_generated
#print axioms p2_eval
#print axioms p2_generated
#print axioms p3_eval
#print axioms p3_generated
#print axioms p4_eval
#print axioms p4_generated
#print axioms p5_eval
#print axioms p5_generated
#print axioms p6_eval
#print axioms p6_generated
#print axioms p7_eval
#print axioms p7_generated
#print axioms p8_eval
#print axioms p8_generated
#print axioms p9_eval
#print axioms p9_generated
#print axioms p10_eval
#print axioms p10_generated
#print axioms p11_eval
#print axioms p11_generated
#print axioms p12_valid
#print axioms p12_eval
#print axioms p12_generated
#print axioms p13_valid
#print axioms p13_eval
#print axioms p13_generated
#print axioms p14_valid
#print axioms p14_eval
#print axioms p14_generated
#print axioms p15_valid
#print axioms p15_eval
#print axioms p15_generated
#print axioms p17_valid
#print axioms p17_eval
#print axioms p17_generated
#print axioms p18_valid
#print axioms p18_eval
#print axioms p18_generated
#print axioms p19_valid
#print axioms p19_eval
#print axioms p19_generated
#print axioms p20_valid
#print axioms p20_eval
#print axioms p20_generated
#print axioms p21_valid
#print axioms p21_eval
#print axioms p21_generated
#print axioms p22_valid
#print axioms p22_eval
#print axioms p22_generated
#print axioms p23_valid
#print axioms p23_eval
#print axioms p23_generated
end SourcePieces
end LuRazClosure
