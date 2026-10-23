import LuRazCore134
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def T134 (e : Nat) : Prop := e=1 ∨ e=3 ∨ e=4
inductive NF134 where
  | ej (a : Nat) | aej (a : Nat) | cj (b : Nat) | zj (b : Nat)
  | czj (b : Nat) | zjb (b : Nat) | cjb (b : Nat) | extra (k : Nat)
  deriving DecidableEq, Repr

def NF134.Valid (q : Nat) : NF134 → Prop
  | .ej a => 5≤a ∧ a≤2*q+1
  | .aej a => q+4≤a ∧ a≤2*q+1
  | .cj b => (2*q+2≤b ∧ b≤4*q-3) ∧ b≠3*q
  | .zj b => 2*q+2≤b ∧ b≤4*q-3
  | .czj b | .cjb b => 2*q+2≤b ∧ b≤3*q-1
  | .zjb b => 2*q+2≤b ∧ b≤3*q
  | .extra k => k<3

def NF134.eval (q : Nat) : NF134 → Nat → Prop
  | .ej a => fun e => T134 e ∨ I a (4*q) e
  | .aej a => fun e => T134 e ∨ I 5 (q+2) e ∨ I a (4*q) e
  | .cj b => fun e => T134 e ∨ I 5 b e ∨ e=3*q+1
  | .zj b => fun e => T134 e ∨ I 5 b e ∨ e=4*q
  | .czj b => fun e => T134 e ∨ I 5 b e ∨ e=3*q+1 ∨ e=4*q
  | .zjb b => fun e => T134 e ∨ I 5 b e ∨ I (3*q+2) (4*q) e
  | .cjb b => fun e => T134 e ∨ I 5 b e ∨ I (3*q+1) (4*q) e
  | .extra k => fun e => ZRow q e ∨ (k=1 ∧ BRow q e) ∨ (k=2 ∧ ERow q e)

theorem mixed134_normal (q a b : Nat) (hq : 4≤q) (hab : JReachable q a b)
    (u v d k1 k2 : Prop) (hg : d∨k1∨k2) :
    ∃ z : NF134, z.Valid q ∧ ∀ e, Mixed134 q a b u v d k1 k2 e ↔ z.eval q e := by
  classical
  have hab' := hab
  unfold JReachable at hab'
  by_cases hu : u
  · by_cases hv : v
    · by_cases hd : d
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
          · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
        · by_cases hk2 : k2
          · by_cases hl : b≤3*q-1
            · refine ⟨.cjb b,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
            · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
          · by_cases hl : b≤3*q-1
            · refine ⟨.cjb b,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
            · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
          · by_cases hl : a≤q+3
            · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
            · refine ⟨.aej a,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
        · by_cases hk2 : k2
          · by_cases hl : b≤3*q
            · refine ⟨.zjb b,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
            · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
          · exact False.elim (by simp_all)
    · by_cases hd : d
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
          · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
        · by_cases hk2 : k2
          · by_cases hl : b≤3*q-1
            · refine ⟨.czj b,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
            · refine ⟨.zj (max b (3*q+1)),by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
          · by_cases hl : b=3*q
            · refine ⟨.cj (3*q+1),by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
            · refine ⟨.cj b,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
          · by_cases hl : a≤q+3
            · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
            · refine ⟨.aej a,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
        · by_cases hk2 : k2
          · refine ⟨.zj b,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
          · exact False.elim (by simp_all)
  · by_cases hv : v
    · by_cases hd : d
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
          · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
        · by_cases hk2 : k2
          · by_cases hl : b≤3*q-1
            · refine ⟨.cjb b,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
            · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
          · by_cases hl : b≤3*q-1
            · refine ⟨.cjb b,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
            · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
          · refine ⟨.ej a,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
        · by_cases hk2 : k2
          · by_cases hl : b≤3*q
            · refine ⟨.zjb b,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
            · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
          · exact False.elim (by simp_all)
    · by_cases hd : d
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
          · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
        · by_cases hk2 : k2
          · by_cases hl : b≤3*q-1
            · refine ⟨.czj b,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
            · refine ⟨.zj (max b (3*q+1)),by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
          · by_cases hl : b=3*q
            · refine ⟨.cj (3*q+1),by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
            · refine ⟨.cj b,by simp only [NF134.Valid]; omega,?_⟩
              intro e
              simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
              omega
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
          · refine ⟨.ej a,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
        · by_cases hk2 : k2
          · refine ⟨.zj b,by simp only [NF134.Valid]; omega,?_⟩
            intro e
            simp only [Mixed134,Fixed134,hu,hv,hd,hk1,hk2,true_and,false_and,false_or,or_false,NF134.eval,T134,JRow,ARow,BRow,CRow,ERow,ZRow,I]
            omega
          · exact False.elim (by simp_all)

theorem fixed134_normal (q : Nat) (hq : 4≤q) (u v d k1 : Prop) :
    ∃ z : NF134, z.Valid q ∧ ∀ e, Fixed134 q u v d k1 True e ↔ z.eval q e := by
  classical
  by_cases hu : u
  · by_cases hv : v
    · by_cases hd : d
      · by_cases hk1 : k1
        · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
        · refine ⟨.cjb (2*q+2),by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
      · by_cases hk1 : k1
        · refine ⟨.extra 2,by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
        · refine ⟨.extra 1,by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
    · by_cases hd : d
      · by_cases hk1 : k1
        · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
        · refine ⟨.czj (2*q+2),by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
      · by_cases hk1 : k1
        · refine ⟨.extra 2,by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
        · refine ⟨.extra 0,by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
  · by_cases hv : v
    · by_cases hd : d
      · by_cases hk1 : k1
        · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
        · refine ⟨.cjb (2*q+2),by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
      · by_cases hk1 : k1
        · refine ⟨.extra 2,by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
        · refine ⟨.extra 1,by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
    · by_cases hd : d
      · by_cases hk1 : k1
        · refine ⟨.ej 5,by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
        · refine ⟨.czj (2*q+2),by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
      · by_cases hk1 : k1
        · refine ⟨.extra 2,by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)
        · refine ⟨.extra 0,by simp only [NF134.Valid]; omega,?_⟩
          intro e
          simp only [Fixed134,hu,hv,hd,hk1,true_and,false_and,false_or,or_false,NF134.eval,T134,ARow,BRow,CRow,ERow,ZRow,I]
          first | omega | (simp only [show (0:Nat)≠1 by decide,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,show (2:Nat)≠1 by decide,true_and,false_and,false_or,or_false] <;> omega)

end LuRazClosure
