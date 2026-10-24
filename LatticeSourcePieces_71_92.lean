import LuRazTotalClosure
namespace LuRazClosure
namespace SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
def p71Domain (q a b : Nat) : Prop := (4)≤(a:Int) ∧ (a:Int)≤((1)*(q:Int)+1) ∧ ((2)*(q:Int)+2)≤(b:Int) ∧ (b:Int)≤((2)*(q:Int)+3)
def p71NF (q a b : Nat) : NF234 := .kr a (b-(2*q+2))
def p71Set (q a b e : Nat) : Prop := (e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((1)*(b:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p71_valid (q a b : Nat) (hq : 4≤q) (hd : p71Domain q a b) : (p71NF q a b).Valid q := by
  simp only [p71Domain] at hd
  simp only [p71NF,NF234.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p71_eval (q a b e : Nat) (hq : 4≤q) (hd : p71Domain q a b) :
    (p71NF q a b).eval q e ↔ p71Set q a b e := by
  simp only [p71Domain] at hd
  simp only [p71NF,p71Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p71_generated (q a b : Nat) (hq : 4≤q) (hd : p71Domain q a b) :
    Generated q (p71Set q a b) := by
  exact generated_congr q (NF234.generated q hq (p71NF q a b) (p71_valid q a b hq hd)) (p71_eval q a b · hq hd)
def p72Domain (q a b : Nat) : Prop := ((1)*(q:Int)+3)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ ((2)*(q:Int)+2)≤(b:Int) ∧ (b:Int)≤((2)*(q:Int)+3)
def p72NF (q a b : Nat) : NF234 := .kr a (b-(2*q+2))
def p72Set (q a b e : Nat) : Prop := (e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((1)*(b:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p72_valid (q a b : Nat) (hq : 4≤q) (hd : p72Domain q a b) : (p72NF q a b).Valid q := by
  simp only [p72Domain] at hd
  simp only [p72NF,NF234.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p72_eval (q a b e : Nat) (hq : 4≤q) (hd : p72Domain q a b) :
    (p72NF q a b).eval q e ↔ p72Set q a b e := by
  simp only [p72Domain] at hd
  simp only [p72NF,p72Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p72_generated (q a b : Nat) (hq : 4≤q) (hd : p72Domain q a b) :
    Generated q (p72Set q a b) := by
  exact generated_congr q (NF234.generated q hq (p72NF q a b) (p72_valid q a b hq hd)) (p72_eval q a b · hq hd)
def p73Domain (q a b : Nat) : Prop := (4)≤(a:Int) ∧ (a:Int)≤((1)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p73NF (q a b : Nat) : NF234 := .dg a
def p73Set (q a b e : Nat) : Prop := (e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p73_valid (q a b : Nat) (hq : 4≤q) (hd : p73Domain q a b) : (p73NF q a b).Valid q := by
  simp only [p73Domain] at hd
  simp only [p73NF,NF234.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p73_eval (q a b e : Nat) (hq : 4≤q) (hd : p73Domain q a b) :
    (p73NF q a b).eval q e ↔ p73Set q a b e := by
  simp only [p73Domain] at hd
  simp only [p73NF,p73Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p73_generated (q a b : Nat) (hq : 4≤q) (hd : p73Domain q a b) :
    Generated q (p73Set q a b) := by
  exact generated_congr q (NF234.generated q hq (p73NF q a b) (p73_valid q a b hq hd)) (p73_eval q a b · hq hd)
def p74Domain (q a b : Nat) : Prop := ((1)*(q:Int)+3)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+(-1)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p74NF (q a b : Nat) : NF234 := .dg a
def p74Set (q a b e : Nat) : Prop := (e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((2)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p74_valid (q a b : Nat) (hq : 4≤q) (hd : p74Domain q a b) : (p74NF q a b).Valid q := by
  simp only [p74Domain] at hd
  simp only [p74NF,NF234.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p74_eval (q a b e : Nat) (hq : 4≤q) (hd : p74Domain q a b) :
    (p74NF q a b).eval q e ↔ p74Set q a b e := by
  simp only [p74Domain] at hd
  simp only [p74NF,p74Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p74_generated (q a b : Nat) (hq : 4≤q) (hd : p74Domain q a b) :
    Generated q (p74Set q a b) := by
  exact generated_congr q (NF234.generated q hq (p74NF q a b) (p74_valid q a b hq hd)) (p74_eval q a b · hq hd)
def p75Domain (q a b : Nat) : Prop := ((2)*(q:Int)+2)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+3) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p75NF (q a b : Nat) : NF234 := .km (a-(2*q+2))
def p75Set (q a b e : Nat) : Prop := (e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+3)) ∨ (((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-1))))
theorem p75_valid (q a b : Nat) (hq : 4≤q) (hd : p75Domain q a b) : (p75NF q a b).Valid q := by
  simp only [p75Domain] at hd
  simp only [p75NF,NF234.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p75_eval (q a b e : Nat) (hq : 4≤q) (hd : p75Domain q a b) :
    (p75NF q a b).eval q e ↔ p75Set q a b e := by
  simp only [p75Domain] at hd
  simp only [p75NF,p75Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p75_generated (q a b : Nat) (hq : 4≤q) (hd : p75Domain q a b) :
    Generated q (p75Set q a b) := by
  exact generated_congr q (NF234.generated q hq (p75NF q a b) (p75_valid q a b hq hd)) (p75_eval q a b · hq hd)
def p76Domain (q a b : Nat) : Prop := ((4)*(q:Int)+(-2))≤(a:Int) ∧ (a:Int)≤((4)*(q:Int)+(-1)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p76NF (q a b : Nat) : NF234 := .ck (a-(4*q-2))
def p76Set (q a b e : Nat) : Prop := (e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))))
theorem p76_valid (q a b : Nat) (hq : 4≤q) (hd : p76Domain q a b) : (p76NF q a b).Valid q := by
  simp only [p76Domain] at hd
  simp only [p76NF,NF234.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p76_eval (q a b e : Nat) (hq : 4≤q) (hd : p76Domain q a b) :
    (p76NF q a b).eval q e ↔ p76Set q a b e := by
  simp only [p76Domain] at hd
  simp only [p76NF,p76Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p76_generated (q a b : Nat) (hq : 4≤q) (hd : p76Domain q a b) :
    Generated q (p76Set q a b) := by
  exact generated_congr q (NF234.generated q hq (p76NF q a b) (p76_valid q a b hq hd)) (p76_eval q a b · hq hd)
def p77Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p77NF (q a b : Nat) : NF234 := .last
def p77Set (q a b e : Nat) : Prop := (e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-2))) ∨ (((4)*(q:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p77_valid (q a b : Nat) (hq : 4≤q) (hd : p77Domain q a b) : (p77NF q a b).Valid q := by
  simp only [p77Domain] at hd
  simp only [p77NF,NF234.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p77_eval (q a b e : Nat) (hq : 4≤q) (hd : p77Domain q a b) :
    (p77NF q a b).eval q e ↔ p77Set q a b e := by
  simp only [p77Domain] at hd
  simp only [p77NF,p77Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p77_generated (q a b : Nat) (hq : 4≤q) (hd : p77Domain q a b) :
    Generated q (p77Set q a b) := by
  exact generated_congr q (NF234.generated q hq (p77NF q a b) (p77_valid q a b hq hd)) (p77_eval q a b · hq hd)
def p78Domain (q a b : Nat) : Prop := ((4)*(q:Int)+(-2))≤(a:Int) ∧ (a:Int)≤((4)*(q:Int)+(-1)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p78NF (q a b : Nat) : NFFull := .noNInterval (a-(4*q-2))
def p78Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))))
theorem p78_valid (q a b : Nat) (hq : 4≤q) (hd : p78Domain q a b) : (p78NF q a b).Valid q := by
  simp only [p78Domain] at hd
  simp only [p78NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p78_eval (q a b e : Nat) (hq : 4≤q) (hd : p78Domain q a b) :
    (p78NF q a b).eval q e ↔ p78Set q a b e := by
  simp only [p78Domain] at hd
  simp only [p78NF,p78Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p78_generated (q a b : Nat) (hq : 4≤q) (hd : p78Domain q a b) :
    Generated q (p78Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p78NF q a b) (p78_valid q a b hq hd)) (p78_eval q a b · hq hd)
def p79Domain (q a b : Nat) : Prop := ((2)*(q:Int)+2)≤(a:Int) ∧ (a:Int)≤((3)*(q:Int)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p79NF (q a b : Nat) : NFFull := .noNMJRight a
def p79Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((3)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-1))))
theorem p79_valid (q a b : Nat) (hq : 4≤q) (hd : p79Domain q a b) : (p79NF q a b).Valid q := by
  simp only [p79Domain] at hd
  simp only [p79NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p79_eval (q a b e : Nat) (hq : 4≤q) (hd : p79Domain q a b) :
    (p79NF q a b).eval q e ↔ p79Set q a b e := by
  simp only [p79Domain] at hd
  simp only [p79NF,p79Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p79_generated (q a b : Nat) (hq : 4≤q) (hd : p79Domain q a b) :
    Generated q (p79Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p79NF q a b) (p79_valid q a b hq hd)) (p79_eval q a b · hq hd)
def p80Domain (q a b : Nat) : Prop := ((1)*(q:Int)+5)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p80NF (q a b : Nat) : NFFull := .noNMJLeft a
def p80Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+3)) ∨ (((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-1))))
theorem p80_valid (q a b : Nat) (hq : 4≤q) (hd : p80Domain q a b) : (p80NF q a b).Valid q := by
  simp only [p80Domain] at hd
  simp only [p80NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p80_eval (q a b e : Nat) (hq : 4≤q) (hd : p80Domain q a b) :
    (p80NF q a b).eval q e ↔ p80Set q a b e := by
  simp only [p80Domain] at hd
  simp only [p80NF,p80Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p80_generated (q a b : Nat) (hq : 4≤q) (hd : p80Domain q a b) :
    Generated q (p80Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p80NF q a b) (p80_valid q a b hq hd)) (p80_eval q a b · hq hd)
def p81Domain (q a b : Nat) : Prop := ((2)*(q:Int)+2)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+3) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p81NF (q a b : Nat) : NFFull := .noNMK (a-(2*q+2))
def p81Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(q:Int)+3)) ∨ (((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-1))))
theorem p81_valid (q a b : Nat) (hq : 4≤q) (hd : p81Domain q a b) : (p81NF q a b).Valid q := by
  simp only [p81Domain] at hd
  simp only [p81NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p81_eval (q a b e : Nat) (hq : 4≤q) (hd : p81Domain q a b) :
    (p81NF q a b).eval q e ↔ p81Set q a b e := by
  simp only [p81Domain] at hd
  simp only [p81NF,p81Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p81_generated (q a b : Nat) (hq : 4≤q) (hd : p81Domain q a b) :
    Generated q (p81Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p81NF q a b) (p81_valid q a b hq hd)) (p81_eval q a b · hq hd)
def p82Domain (q a b : Nat) : Prop := ((2)*(q:Int)+2)≤(a:Int) ∧ (a:Int)≤((3)*(q:Int)+(-1)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p82NF (q a b : Nat) : NFFull := .noNCMJ a
def p82Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-1))))
theorem p82_valid (q a b : Nat) (hq : 4≤q) (hd : p82Domain q a b) : (p82NF q a b).Valid q := by
  simp only [p82Domain] at hd
  simp only [p82NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p82_eval (q a b e : Nat) (hq : 4≤q) (hd : p82Domain q a b) :
    (p82NF q a b).eval q e ↔ p82Set q a b e := by
  simp only [p82Domain] at hd
  simp only [p82NF,p82Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p82_generated (q a b : Nat) (hq : 4≤q) (hd : p82Domain q a b) :
    Generated q (p82Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p82NF q a b) (p82_valid q a b hq hd)) (p82_eval q a b · hq hd)
def p83Domain (q a b : Nat) : Prop := (4)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)) ∧ ((2)*(q:Int)+2)≤(b:Int) ∧ (b:Int)≤((2)*(q:Int)+3)
def p83NF (q a b : Nat) : NFFull := .noH1Short a (b-(2*q+2))
def p83Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((1)*(b:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p83_valid (q a b : Nat) (hq : 4≤q) (hd : p83Domain q a b) : (p83NF q a b).Valid q := by
  simp only [p83Domain] at hd
  simp only [p83NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p83_eval (q a b e : Nat) (hq : 4≤q) (hd : p83Domain q a b) :
    (p83NF q a b).eval q e ↔ p83Set q a b e := by
  simp only [p83Domain] at hd
  simp only [p83NF,p83Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p83_generated (q a b : Nat) (hq : 4≤q) (hd : p83Domain q a b) :
    Generated q (p83Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p83NF q a b) (p83_valid q a b hq hd)) (p83_eval q a b · hq hd)
def p84Domain (q a b : Nat) : Prop := ((2)*(q:Int)+4)≤(a:Int) ∧ (a:Int)≤((4)*(q:Int)+(-1)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p84NF (q a b : Nat) : NFFull := .noH1ZL a
def p84Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int))) ∨ (((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p84_valid (q a b : Nat) (hq : 4≤q) (hd : p84Domain q a b) : (p84NF q a b).Valid q := by
  simp only [p84Domain] at hd
  simp only [p84NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p84_eval (q a b e : Nat) (hq : 4≤q) (hd : p84Domain q a b) :
    (p84NF q a b).eval q e ↔ p84Set q a b e := by
  simp only [p84Domain] at hd
  simp only [p84NF,p84Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p84_generated (q a b : Nat) (hq : 4≤q) (hd : p84Domain q a b) :
    Generated q (p84Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p84NF q a b) (p84_valid q a b hq hd)) (p84_eval q a b · hq hd)
def p85Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p85NF (q a b : Nat) : NFFull := .noH1Exception
def p85Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int))) ∨ (((2)*(q:Int)+2)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int)+(-2))) ∨ (((4)*(q:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p85_valid (q a b : Nat) (hq : 4≤q) (hd : p85Domain q a b) : (p85NF q a b).Valid q := by
  simp only [p85Domain] at hd
  simp only [p85NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p85_eval (q a b e : Nat) (hq : 4≤q) (hd : p85Domain q a b) :
    (p85NF q a b).eval q e ↔ p85Set q a b e := by
  simp only [p85Domain] at hd
  simp only [p85NF,p85Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p85_generated (q a b : Nat) (hq : 4≤q) (hd : p85Domain q a b) :
    Generated q (p85Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p85NF q a b) (p85_valid q a b hq hd)) (p85_eval q a b · hq hd)
def p86Domain (q a b : Nat) : Prop := ((2)*(q:Int)+3)≤(a:Int) ∧ (a:Int)≤((4)*(q:Int)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p86NF (q a b : Nat) : NFFull := .noH2 a
def p86Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((2)*(q:Int)+1)) ∨ (((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p86_valid (q a b : Nat) (hq : 4≤q) (hd : p86Domain q a b) : (p86NF q a b).Valid q := by
  simp only [p86Domain] at hd
  simp only [p86NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p86_eval (q a b e : Nat) (hq : 4≤q) (hd : p86Domain q a b) :
    (p86NF q a b).eval q e ↔ p86Set q a b e := by
  simp only [p86Domain] at hd
  simp only [p86NF,p86Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p86_generated (q a b : Nat) (hq : 4≤q) (hd : p86Domain q a b) :
    Generated q (p86Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p86NF q a b) (p86_valid q a b hq hd)) (p86_eval q a b · hq hd)
def p87Domain (q a b : Nat) : Prop := (6)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+1) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p87NF (q a b : Nat) : NFFull := .noFive a
def p87Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ ((((1)*(a:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p87_valid (q a b : Nat) (hq : 4≤q) (hd : p87Domain q a b) : (p87NF q a b).Valid q := by
  simp only [p87Domain] at hd
  simp only [p87NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p87_eval (q a b e : Nat) (hq : 4≤q) (hd : p87Domain q a b) :
    (p87NF q a b).eval q e ↔ p87Set q a b e := by
  simp only [p87Domain] at hd
  simp only [p87NF,p87Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p87_generated (q a b : Nat) (hq : 4≤q) (hd : p87Domain q a b) :
    Generated q (p87Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p87NF q a b) (p87_valid q a b hq hd)) (p87_eval q a b · hq hd)
def p88Domain (q a b : Nat) : Prop := (5)≤(a:Int) ∧ (a:Int)≤((2)*(q:Int)+(-1)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤((2)*(q:Int)+1) ∧ (a:Int)+(2)≤(b:Int)
def p88NF (q a b : Nat) : NFFull := .leftGap a b
def p88Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((1)*(b:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p88_valid (q a b : Nat) (hq : 4≤q) (hd : p88Domain q a b) : (p88NF q a b).Valid q := by
  simp only [p88Domain] at hd
  simp only [p88NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p88_eval (q a b e : Nat) (hq : 4≤q) (hd : p88Domain q a b) :
    (p88NF q a b).eval q e ↔ p88Set q a b e := by
  simp only [p88Domain] at hd
  simp only [p88NF,p88Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p88_generated (q a b : Nat) (hq : 4≤q) (hd : p88Domain q a b) :
    Generated q (p88Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p88NF q a b) (p88_valid q a b hq hd)) (p88_eval q a b · hq hd)
def p89Domain (q a b : Nat) : Prop := (0:Int)≤(a:Int) ∧ (a:Int)≤(0:Int) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤(0:Int)
def p89NF (q a b : Nat) : NFFull := .full
def p89Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p89_valid (q a b : Nat) (hq : 4≤q) (hd : p89Domain q a b) : (p89NF q a b).Valid q := by
  simp only [p89Domain] at hd
  simp only [p89NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p89_eval (q a b e : Nat) (hq : 4≤q) (hd : p89Domain q a b) :
    (p89NF q a b).eval q e ↔ p89Set q a b e := by
  simp only [p89Domain] at hd
  simp only [p89NF,p89Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p89_generated (q a b : Nat) (hq : 4≤q) (hd : p89Domain q a b) :
    Generated q (p89Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p89NF q a b) (p89_valid q a b hq hd)) (p89_eval q a b · hq hd)
def p90Domain (q a b : Nat) : Prop := ((2)*(q:Int)+2)≤(a:Int) ∧ (a:Int)≤((4)*(q:Int)+(-2)) ∧ (0:Int)≤(b:Int) ∧ (b:Int)≤((4)*(q:Int)) ∧ (a:Int)+(2)≤(b:Int)
def p90NF (q a b : Nat) : NFFull := .rightGap a b
def p90Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((1)*(b:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p90_valid (q a b : Nat) (hq : 4≤q) (hd : p90Domain q a b) : (p90NF q a b).Valid q := by
  simp only [p90Domain] at hd
  simp only [p90NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p90_eval (q a b e : Nat) (hq : 4≤q) (hd : p90Domain q a b) :
    (p90NF q a b).eval q e ↔ p90Set q a b e := by
  simp only [p90Domain] at hd
  simp only [p90NF,p90Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p90_generated (q a b : Nat) (hq : 4≤q) (hd : p90Domain q a b) :
    Generated q (p90Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p90NF q a b) (p90_valid q a b hq hd)) (p90_eval q a b · hq hd)
def p91Domain (q a b : Nat) : Prop := ((2)*(q:Int)+2)≤(a:Int) ∧ (a:Int)≤((3)*(q:Int)+(-1)) ∧ ((3)*(q:Int)+3)≤(b:Int) ∧ (b:Int)≤((4)*(q:Int))
def p91NF (q a b : Nat) : NFFull := .isolatedR a b
def p91Set (q a b e : Nat) : Prop := (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (((5)≤(e:Int) ∧ (e:Int)≤((1)*(a:Int))) ∨ (((3)*(q:Int)+1)≤(e:Int) ∧ (e:Int)≤((3)*(q:Int)+1)) ∨ (((1)*(b:Int))≤(e:Int) ∧ (e:Int)≤((4)*(q:Int))))
theorem p91_valid (q a b : Nat) (hq : 4≤q) (hd : p91Domain q a b) : (p91NF q a b).Valid q := by
  simp only [p91Domain] at hd
  simp only [p91NF,NFFull.Valid,P,JReachable,g]
  repeat first | omega | decide | split
theorem p91_eval (q a b e : Nat) (hq : 4≤q) (hd : p91Domain q a b) :
    (p91NF q a b).eval q e ↔ p91Set q a b e := by
  simp only [p91Domain] at hd
  simp only [p91NF,p91Set,NFSmall.eval,NF23.eval,NF123.eval,NF123.body,NF14.eval,NF24.eval,NF124.eval,NF134.eval,NF234.eval,NFFull.eval,FullHead,T124,T134,T234,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,JRow,TwoPiece,LRow,LNormal,I,beta,false_or,or_false,true_or,or_true,false_and,and_false,true_and,and_true]
  repeat first | omega | split
theorem p91_generated (q a b : Nat) (hq : 4≤q) (hd : p91Domain q a b) :
    Generated q (p91Set q a b) := by
  exact generated_congr q (NFFull.generated q hq (p91NF q a b) (p91_valid q a b hq hd)) (p91_eval q a b · hq hd)
#print axioms p71_valid
#print axioms p71_eval
#print axioms p71_generated
#print axioms p72_valid
#print axioms p72_eval
#print axioms p72_generated
#print axioms p73_valid
#print axioms p73_eval
#print axioms p73_generated
#print axioms p74_valid
#print axioms p74_eval
#print axioms p74_generated
#print axioms p75_valid
#print axioms p75_eval
#print axioms p75_generated
#print axioms p76_valid
#print axioms p76_eval
#print axioms p76_generated
#print axioms p77_valid
#print axioms p77_eval
#print axioms p77_generated
#print axioms p78_valid
#print axioms p78_eval
#print axioms p78_generated
#print axioms p79_valid
#print axioms p79_eval
#print axioms p79_generated
#print axioms p80_valid
#print axioms p80_eval
#print axioms p80_generated
#print axioms p81_valid
#print axioms p81_eval
#print axioms p81_generated
#print axioms p82_valid
#print axioms p82_eval
#print axioms p82_generated
#print axioms p83_valid
#print axioms p83_eval
#print axioms p83_generated
#print axioms p84_valid
#print axioms p84_eval
#print axioms p84_generated
#print axioms p85_valid
#print axioms p85_eval
#print axioms p85_generated
#print axioms p86_valid
#print axioms p86_eval
#print axioms p86_generated
#print axioms p87_valid
#print axioms p87_eval
#print axioms p87_generated
#print axioms p88_valid
#print axioms p88_eval
#print axioms p88_generated
#print axioms p89_valid
#print axioms p89_eval
#print axioms p89_generated
#print axioms p90_valid
#print axioms p90_eval
#print axioms p90_generated
#print axioms p91_valid
#print axioms p91_eval
#print axioms p91_generated
end SourcePieces
end LuRazClosure
