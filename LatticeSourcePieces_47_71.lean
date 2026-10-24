import LuRazTotalClosure
namespace LuRazClosure
namespace SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
def p47Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p47NF (q a b : Nat) : NF24 := .k1
def p47Set (q a b e : Nat) : Prop := (e=2 ∨ e=4) ∨ ((((2)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-2))))
theorem p47_eval (q a b e : Nat) (hq : 4≤q) (hd : p47Domain q a b) :
    (p47NF q a b).eval q e ↔ p47Set q a b e := by
  simp only [p47Domain] at hd
  simp only [p47NF,p47Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p47_generated (q a b : Nat) (hq : 4≤q) (hd : p47Domain q a b) :
    Generated q (p47Set q a b) := by
  exact generated_congr q (NF24.generated q hq (p47NF q a b)) (p47_eval q a b · hq hd)
def p48Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p48NF (q a b : Nat) : NF24 := .k2
def p48Set (q a b e : Nat) : Prop := (e=2 ∨ e=4) ∨ ((((2)*(q:Int)+3)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-1))))
theorem p48_eval (q a b e : Nat) (hq : 4≤q) (hd : p48Domain q a b) :
    (p48NF q a b).eval q e ↔ p48Set q a b e := by
  simp only [p48Domain] at hd
  simp only [p48NF,p48Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p48_generated (q a b : Nat) (hq : 4≤q) (hd : p48Domain q a b) :
    Generated q (p48Set q a b) := by
  exact generated_congr q (NF24.generated q hq (p48NF q a b)) (p48_eval q a b · hq hd)
def p49Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p49NF (q a b : Nat) : NF24 := .joinK
def p49Set (q a b e : Nat) : Prop := (e=2 ∨ e=4) ∨ ((((2)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-1))))
theorem p49_eval (q a b e : Nat) (hq : 4≤q) (hd : p49Domain q a b) :
    (p49NF q a b).eval q e ↔ p49Set q a b e := by
  simp only [p49Domain] at hd
  simp only [p49NF,p49Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p49_generated (q a b : Nat) (hq : 4≤q) (hd : p49Domain q a b) :
    Generated q (p49Set q a b) := by
  exact generated_congr q (NF24.generated q hq (p49NF q a b)) (p49_eval q a b · hq hd)
def p50Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p50NF (q a b : Nat) : NF24 := .fill1
def p50Set (q a b e : Nat) : Prop := (e=2 ∨ e=4) ∨ ((((2)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p50_eval (q a b e : Nat) (hq : 4≤q) (hd : p50Domain q a b) :
    (p50NF q a b).eval q e ↔ p50Set q a b e := by
  simp only [p50Domain] at hd
  simp only [p50NF,p50Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p50_generated (q a b : Nat) (hq : 4≤q) (hd : p50Domain q a b) :
    Generated q (p50Set q a b) := by
  exact generated_congr q (NF24.generated q hq (p50NF q a b)) (p50_eval q a b · hq hd)
def p51Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p51NF (q a b : Nat) : NF24 := .fill2
def p51Set (q a b e : Nat) : Prop := (e=2 ∨ e=4) ∨ ((((2)*(q:Int)+3)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p51_eval (q a b e : Nat) (hq : 4≤q) (hd : p51Domain q a b) :
    (p51NF q a b).eval q e ↔ p51Set q a b e := by
  simp only [p51Domain] at hd
  simp only [p51NF,p51Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p51_generated (q a b : Nat) (hq : 4≤q) (hd : p51Domain q a b) :
    Generated q (p51Set q a b) := by
  exact generated_congr q (NF24.generated q hq (p51NF q a b)) (p51_eval q a b · hq hd)
def p52Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p52NF (q a b : Nat) : NF24 := .dBig
def p52Set (q a b e : Nat) : Prop := (e=2 ∨ e=4) ∨ ((((2)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p52_eval (q a b e : Nat) (hq : 4≤q) (hd : p52Domain q a b) :
    (p52NF q a b).eval q e ↔ p52Set q a b e := by
  simp only [p52Domain] at hd
  simp only [p52NF,p52Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p52_generated (q a b : Nat) (hq : 4≤q) (hd : p52Domain q a b) :
    Generated q (p52Set q a b) := by
  exact generated_congr q (NF24.generated q hq (p52NF q a b)) (p52_eval q a b · hq hd)
def p53Domain (q a b : Nat) : Prop := (5)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ ((4)*(q:Int)+(-2))≤(b:Int) ∧ (b:Int)≤((4)*(q:Int))
def p53NF (q a b : Nat) : NF124 := .interval a (b-(4*q-2))
def p53Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=4) ∨ ((((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((1)*(b:Int))))
theorem p53_valid (q a b : Nat) (hq : 4≤q) (hd : p53Domain q a b) : (p53NF q a b).Valid q := by
  simp only [p53Domain] at hd
  simp only [p53NF,NF124.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p53_eval (q a b e : Nat) (hq : 4≤q) (hd : p53Domain q a b) :
    (p53NF q a b).eval q e ↔ p53Set q a b e := by
  simp only [p53Domain] at hd
  simp only [p53NF,p53Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p53_generated (q a b : Nat) (hq : 4≤q) (hd : p53Domain q a b) :
    Generated q (p53Set q a b) := by
  exact generated_congr q (NF124.generated q hq (p53NF q a b) (p53_valid q a b hq hd)) (p53_eval q a b · hq hd)
def p54Domain (q a b : Nat) : Prop := ((1)*(q:Int)+4)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ ((4)*(q:Int)+(-2))≤(b:Int) ∧ (b:Int)≤((4)*(q:Int))
def p54NF (q a b : Nat) : NF124 := .agap a (b-(4*q-2))
def p54Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((1)*(b:Int))))
theorem p54_valid (q a b : Nat) (hq : 4≤q) (hd : p54Domain q a b) : (p54NF q a b).Valid q := by
  simp only [p54Domain] at hd
  simp only [p54NF,NF124.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p54_eval (q a b e : Nat) (hq : 4≤q) (hd : p54Domain q a b) :
    (p54NF q a b).eval q e ↔ p54Set q a b e := by
  simp only [p54Domain] at hd
  simp only [p54NF,p54Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p54_generated (q a b : Nat) (hq : 4≤q) (hd : p54Domain q a b) :
    Generated q (p54Set q a b) := by
  exact generated_congr q (NF124.generated q hq (p54NF q a b) (p54_valid q a b hq hd)) (p54_eval q a b · hq hd)
def p55Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p55NF (q a b : Nat) : NF124 := .ak .k1
def p55Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((2)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-2))))
theorem p55_valid (q a b : Nat) (hq : 4≤q) (hd : p55Domain q a b) : (p55NF q a b).Valid q := by
  simp only [p55Domain] at hd
  simp only [p55NF,NF124.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p55_eval (q a b e : Nat) (hq : 4≤q) (hd : p55Domain q a b) :
    (p55NF q a b).eval q e ↔ p55Set q a b e := by
  simp only [p55Domain] at hd
  simp only [p55NF,p55Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p55_generated (q a b : Nat) (hq : 4≤q) (hd : p55Domain q a b) :
    Generated q (p55Set q a b) := by
  exact generated_congr q (NF124.generated q hq (p55NF q a b) (p55_valid q a b hq hd)) (p55_eval q a b · hq hd)
def p56Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p56NF (q a b : Nat) : NF124 := .ak .k2
def p56Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((2)*(q:Int)+3)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-1))))
theorem p56_valid (q a b : Nat) (hq : 4≤q) (hd : p56Domain q a b) : (p56NF q a b).Valid q := by
  simp only [p56Domain] at hd
  simp only [p56NF,NF124.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p56_eval (q a b e : Nat) (hq : 4≤q) (hd : p56Domain q a b) :
    (p56NF q a b).eval q e ↔ p56Set q a b e := by
  simp only [p56Domain] at hd
  simp only [p56NF,p56Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p56_generated (q a b : Nat) (hq : 4≤q) (hd : p56Domain q a b) :
    Generated q (p56Set q a b) := by
  exact generated_congr q (NF124.generated q hq (p56NF q a b) (p56_valid q a b hq hd)) (p56_eval q a b · hq hd)
def p57Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p57NF (q a b : Nat) : NF124 := .ak .joinK
def p57Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((2)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-1))))
theorem p57_valid (q a b : Nat) (hq : 4≤q) (hd : p57Domain q a b) : (p57NF q a b).Valid q := by
  simp only [p57Domain] at hd
  simp only [p57NF,NF124.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p57_eval (q a b e : Nat) (hq : 4≤q) (hd : p57Domain q a b) :
    (p57NF q a b).eval q e ↔ p57Set q a b e := by
  simp only [p57Domain] at hd
  simp only [p57NF,p57Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p57_generated (q a b : Nat) (hq : 4≤q) (hd : p57Domain q a b) :
    Generated q (p57Set q a b) := by
  exact generated_congr q (NF124.generated q hq (p57NF q a b) (p57_valid q a b hq hd)) (p57_eval q a b · hq hd)
def p58Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p58NF (q a b : Nat) : NF124 := .ak .fill1
def p58Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((2)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p58_valid (q a b : Nat) (hq : 4≤q) (hd : p58Domain q a b) : (p58NF q a b).Valid q := by
  simp only [p58Domain] at hd
  simp only [p58NF,NF124.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p58_eval (q a b e : Nat) (hq : 4≤q) (hd : p58Domain q a b) :
    (p58NF q a b).eval q e ↔ p58Set q a b e := by
  simp only [p58Domain] at hd
  simp only [p58NF,p58Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p58_generated (q a b : Nat) (hq : 4≤q) (hd : p58Domain q a b) :
    Generated q (p58Set q a b) := by
  exact generated_congr q (NF124.generated q hq (p58NF q a b) (p58_valid q a b hq hd)) (p58_eval q a b · hq hd)
def p59Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p59NF (q a b : Nat) : NF124 := .ak .fill2
def p59Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((2)*(q:Int)+3)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p59_valid (q a b : Nat) (hq : 4≤q) (hd : p59Domain q a b) : (p59NF q a b).Valid q := by
  simp only [p59Domain] at hd
  simp only [p59NF,NF124.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p59_eval (q a b e : Nat) (hq : 4≤q) (hd : p59Domain q a b) :
    (p59NF q a b).eval q e ↔ p59Set q a b e := by
  simp only [p59Domain] at hd
  simp only [p59NF,p59Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p59_generated (q a b : Nat) (hq : 4≤q) (hd : p59Domain q a b) :
    Generated q (p59Set q a b) := by
  exact generated_congr q (NF124.generated q hq (p59NF q a b) (p59_valid q a b hq hd)) (p59_eval q a b · hq hd)
def p60Domain (q a b : Nat) : Prop := (5)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p60NF (q a b : Nat) : NF134 := .ej a
def p60Set (q a b e : Nat) : Prop := (e=1 ∨ e=3 ∨ e=4) ∨ ((((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p60_valid (q a b : Nat) (hq : 4≤q) (hd : p60Domain q a b) : (p60NF q a b).Valid q := by
  simp only [p60Domain] at hd
  simp only [p60NF,NF134.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p60_eval (q a b e : Nat) (hq : 4≤q) (hd : p60Domain q a b) :
    (p60NF q a b).eval q e ↔ p60Set q a b e := by
  simp only [p60Domain] at hd
  simp only [p60NF,p60Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p60_generated (q a b : Nat) (hq : 4≤q) (hd : p60Domain q a b) :
    Generated q (p60Set q a b) := by
  exact generated_congr q (NF134.generated q hq (p60NF q a b) (p60_valid q a b hq hd)) (p60_eval q a b · hq hd)
def p61Domain (q a b : Nat) : Prop := ((1)*(q:Int)+4)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p61NF (q a b : Nat) : NF134 := .aej a
def p61Set (q a b e : Nat) : Prop := (e=1 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+2)) ∨ (((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p61_valid (q a b : Nat) (hq : 4≤q) (hd : p61Domain q a b) : (p61NF q a b).Valid q := by
  simp only [p61Domain] at hd
  simp only [p61NF,NF134.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p61_eval (q a b e : Nat) (hq : 4≤q) (hd : p61Domain q a b) :
    (p61NF q a b).eval q e ↔ p61Set q a b e := by
  simp only [p61Domain] at hd
  simp only [p61NF,p61Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p61_generated (q a b : Nat) (hq : 4≤q) (hd : p61Domain q a b) :
    Generated q (p61Set q a b) := by
  exact generated_congr q (NF134.generated q hq (p61NF q a b) (p61_valid q a b hq hd)) (p61_eval q a b · hq hd)
def p62Domain (q a b : Nat) : Prop := ((2)*(q:Int)+2)≤(a:Int) ∧ (a:Int)≤((3)*(q:Int)+(-1)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p62NF (q a b : Nat) : NF134 := .cj a
def p62Set (q a b e : Nat) : Prop := (e=1 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((3)*(q:Int)+1)))
theorem p62_valid (q a b : Nat) (hq : 4≤q) (hd : p62Domain q a b) : (p62NF q a b).Valid q := by
  simp only [p62Domain] at hd
  simp only [p62NF,NF134.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p62_eval (q a b e : Nat) (hq : 4≤q) (hd : p62Domain q a b) :
    (p62NF q a b).eval q e ↔ p62Set q a b e := by
  simp only [p62Domain] at hd
  simp only [p62NF,p62Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p62_generated (q a b : Nat) (hq : 4≤q) (hd : p62Domain q a b) :
    Generated q (p62Set q a b) := by
  exact generated_congr q (NF134.generated q hq (p62NF q a b) (p62_valid q a b hq hd)) (p62_eval q a b · hq hd)
def p63Domain (q a b : Nat) : Prop := ((3)*(q:Int)+1)≤(a:Int) ∧ (a:Int)≤((4)*(q:Int)+(-3)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p63NF (q a b : Nat) : NF134 := .cj a
def p63Set (q a b e : Nat) : Prop := (e=1 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((3)*(q:Int)+1)))
theorem p63_valid (q a b : Nat) (hq : 4≤q) (hd : p63Domain q a b) : (p63NF q a b).Valid q := by
  simp only [p63Domain] at hd
  simp only [p63NF,NF134.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p63_eval (q a b e : Nat) (hq : 4≤q) (hd : p63Domain q a b) :
    (p63NF q a b).eval q e ↔ p63Set q a b e := by
  simp only [p63Domain] at hd
  simp only [p63NF,p63Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p63_generated (q a b : Nat) (hq : 4≤q) (hd : p63Domain q a b) :
    Generated q (p63Set q a b) := by
  exact generated_congr q (NF134.generated q hq (p63NF q a b) (p63_valid q a b hq hd)) (p63_eval q a b · hq hd)
def p64Domain (q a b : Nat) : Prop := ((2)*(q:Int)+2)≤(a:Int) ∧ (a:Int)≤((4)*(q:Int)+(-3)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p64NF (q a b : Nat) : NF134 := .zj a
def p64Set (q a b e : Nat) : Prop := (e=1 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((4)*(q:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p64_valid (q a b : Nat) (hq : 4≤q) (hd : p64Domain q a b) : (p64NF q a b).Valid q := by
  simp only [p64Domain] at hd
  simp only [p64NF,NF134.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p64_eval (q a b e : Nat) (hq : 4≤q) (hd : p64Domain q a b) :
    (p64NF q a b).eval q e ↔ p64Set q a b e := by
  simp only [p64Domain] at hd
  simp only [p64NF,p64Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p64_generated (q a b : Nat) (hq : 4≤q) (hd : p64Domain q a b) :
    Generated q (p64Set q a b) := by
  exact generated_congr q (NF134.generated q hq (p64NF q a b) (p64_valid q a b hq hd)) (p64_eval q a b · hq hd)
def p65Domain (q a b : Nat) : Prop := ((2)*(q:Int)+2)≤(a:Int) ∧ (a:Int)≤((3)*(q:Int)+(-1)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p65NF (q a b : Nat) : NF134 := .czj a
def p65Set (q a b e : Nat) : Prop := (e=1 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((3)*(q:Int)+1)) ∨ (((4)*(q:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p65_valid (q a b : Nat) (hq : 4≤q) (hd : p65Domain q a b) : (p65NF q a b).Valid q := by
  simp only [p65Domain] at hd
  simp only [p65NF,NF134.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p65_eval (q a b e : Nat) (hq : 4≤q) (hd : p65Domain q a b) :
    (p65NF q a b).eval q e ↔ p65Set q a b e := by
  simp only [p65Domain] at hd
  simp only [p65NF,p65Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p65_generated (q a b : Nat) (hq : 4≤q) (hd : p65Domain q a b) :
    Generated q (p65Set q a b) := by
  exact generated_congr q (NF134.generated q hq (p65NF q a b) (p65_valid q a b hq hd)) (p65_eval q a b · hq hd)
def p66Domain (q a b : Nat) : Prop := ((2)*(q:Int)+2)≤(a:Int) ∧ (a:Int)≤((3)*(q:Int)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p66NF (q a b : Nat) : NF134 := .zjb a
def p66Set (q a b e : Nat) : Prop := (e=1 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((3)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p66_valid (q a b : Nat) (hq : 4≤q) (hd : p66Domain q a b) : (p66NF q a b).Valid q := by
  simp only [p66Domain] at hd
  simp only [p66NF,NF134.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p66_eval (q a b e : Nat) (hq : 4≤q) (hd : p66Domain q a b) :
    (p66NF q a b).eval q e ↔ p66Set q a b e := by
  simp only [p66Domain] at hd
  simp only [p66NF,p66Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p66_generated (q a b : Nat) (hq : 4≤q) (hd : p66Domain q a b) :
    Generated q (p66Set q a b) := by
  exact generated_congr q (NF134.generated q hq (p66NF q a b) (p66_valid q a b hq hd)) (p66_eval q a b · hq hd)
def p67Domain (q a b : Nat) : Prop := ((2)*(q:Int)+2)≤(a:Int) ∧ (a:Int)≤((3)*(q:Int)+(-1)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p67NF (q a b : Nat) : NF134 := .cjb a
def p67Set (q a b e : Nat) : Prop := (e=1 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p67_valid (q a b : Nat) (hq : 4≤q) (hd : p67Domain q a b) : (p67NF q a b).Valid q := by
  simp only [p67Domain] at hd
  simp only [p67NF,NF134.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p67_eval (q a b e : Nat) (hq : 4≤q) (hd : p67Domain q a b) :
    (p67NF q a b).eval q e ↔ p67Set q a b e := by
  simp only [p67Domain] at hd
  simp only [p67NF,p67Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p67_generated (q a b : Nat) (hq : 4≤q) (hd : p67Domain q a b) :
    Generated q (p67Set q a b) := by
  exact generated_congr q (NF134.generated q hq (p67NF q a b) (p67_valid q a b hq hd)) (p67_eval q a b · hq hd)
def p68Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p68NF (q a b : Nat) : NF134 := .extra 0
def p68Set (q a b e : Nat) : Prop := (e=1 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int))) ∨ (((4)*(q:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p68_valid (q a b : Nat) (hq : 4≤q) (hd : p68Domain q a b) : (p68NF q a b).Valid q := by
  simp only [p68Domain] at hd
  simp only [p68NF,NF134.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p68_eval (q a b e : Nat) (hq : 4≤q) (hd : p68Domain q a b) :
    (p68NF q a b).eval q e ↔ p68Set q a b e := by
  simp only [p68Domain] at hd
  simp only [p68NF,p68Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p68_generated (q a b : Nat) (hq : 4≤q) (hd : p68Domain q a b) :
    Generated q (p68Set q a b) := by
  exact generated_congr q (NF134.generated q hq (p68NF q a b) (p68_valid q a b hq hd)) (p68_eval q a b · hq hd)
def p69Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p69NF (q a b : Nat) : NF134 := .extra 1
def p69Set (q a b e : Nat) : Prop := (e=1 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int))) ∨ (((4)*(q:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))) ∨ (((3)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p69_valid (q a b : Nat) (hq : 4≤q) (hd : p69Domain q a b) : (p69NF q a b).Valid q := by
  simp only [p69Domain] at hd
  simp only [p69NF,NF134.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p69_eval (q a b e : Nat) (hq : 4≤q) (hd : p69Domain q a b) :
    (p69NF q a b).eval q e ↔ p69Set q a b e := by
  simp only [p69Domain] at hd
  simp only [p69NF,p69Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p69_generated (q a b : Nat) (hq : 4≤q) (hd : p69Domain q a b) :
    Generated q (p69Set q a b) := by
  exact generated_congr q (NF134.generated q hq (p69NF q a b) (p69_valid q a b hq hd)) (p69_eval q a b · hq hd)
def p70Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p70NF (q a b : Nat) : NF134 := .extra 2
def p70Set (q a b e : Nat) : Prop := (e=1 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int))) ∨ (((4)*(q:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))) ∨ (((2)*(q:Int)+3)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p70_valid (q a b : Nat) (hq : 4≤q) (hd : p70Domain q a b) : (p70NF q a b).Valid q := by
  simp only [p70Domain] at hd
  simp only [p70NF,NF134.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p70_eval (q a b e : Nat) (hq : 4≤q) (hd : p70Domain q a b) :
    (p70NF q a b).eval q e ↔ p70Set q a b e := by
  simp only [p70Domain] at hd
  simp only [p70NF,p70Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p70_generated (q a b : Nat) (hq : 4≤q) (hd : p70Domain q a b) :
    Generated q (p70Set q a b) := by
  exact generated_congr q (NF134.generated q hq (p70NF q a b) (p70_valid q a b hq hd)) (p70_eval q a b · hq hd)
#print axioms p47_eval
#print axioms p47_generated
#print axioms p48_eval
#print axioms p48_generated
#print axioms p49_eval
#print axioms p49_generated
#print axioms p50_eval
#print axioms p50_generated
#print axioms p51_eval
#print axioms p51_generated
#print axioms p52_eval
#print axioms p52_generated
#print axioms p53_valid
#print axioms p53_eval
#print axioms p53_generated
#print axioms p54_valid
#print axioms p54_eval
#print axioms p54_generated
#print axioms p55_valid
#print axioms p55_eval
#print axioms p55_generated
#print axioms p56_valid
#print axioms p56_eval
#print axioms p56_generated
#print axioms p57_valid
#print axioms p57_eval
#print axioms p57_generated
#print axioms p58_valid
#print axioms p58_eval
#print axioms p58_generated
#print axioms p59_valid
#print axioms p59_eval
#print axioms p59_generated
#print axioms p60_valid
#print axioms p60_eval
#print axioms p60_generated
#print axioms p61_valid
#print axioms p61_eval
#print axioms p61_generated
#print axioms p62_valid
#print axioms p62_eval
#print axioms p62_generated
#print axioms p63_valid
#print axioms p63_eval
#print axioms p63_generated
#print axioms p64_valid
#print axioms p64_eval
#print axioms p64_generated
#print axioms p65_valid
#print axioms p65_eval
#print axioms p65_generated
#print axioms p66_valid
#print axioms p66_eval
#print axioms p66_generated
#print axioms p67_valid
#print axioms p67_eval
#print axioms p67_generated
#print axioms p68_valid
#print axioms p68_eval
#print axioms p68_generated
#print axioms p69_valid
#print axioms p69_eval
#print axioms p69_generated
#print axioms p70_valid
#print axioms p70_eval
#print axioms p70_generated
end SourcePieces
end LuRazClosure
