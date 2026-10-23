import LuRazCore234
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def T234 (e : Nat) : Prop := e=2 ∨ e=3 ∨ e=4
inductive NF234 where
  | kr (p k : Nat) | dg (p : Nat) | km (k : Nat) | ck (k : Nat) | last
  deriving DecidableEq, Repr

def NF234.Valid (q : Nat) : NF234 → Prop
  | .kr p k => P q p ∧ k<2
  | .dg p => P q p ∧ p≤2*q-1
  | .km k | .ck k => k<2
  | .last => True

def NF234.eval (q : Nat) : NF234 → Nat → Prop
  | .kr p k => fun e => T234 e ∨ I 5 p e ∨ I (2*q+2+k) (4*q) e
  | .dg p => fun e => T234 e ∨ I 5 p e ∨ I (2*q+1) (4*q) e
  | .km k => fun e => T234 e ∨ I 5 (q+3) e ∨ I (2*q+2+k) (4*q-1) e
  | .ck k => fun e => T234 e ∨ I 5 (4*q-2+k) e
  | .last => fun e => T234 e ∨ I 5 (4*q-2) e ∨ e=4*q

theorem mixed234_normal (q t p : Nat) (hq : 4≤q)
    (ht : P q t) (hp : P q p) (htp : t≤p) (u v w k1 k2 : Prop) (hK : k1∨k2) :
    ∃ z : NF234, z.Valid q ∧ ∀ e, Mixed234 q t p u v w k1 k2 e ↔ z.eval q e := by
  classical
  have ht' := ht
  have hp' := hp
  unfold P at ht' hp'
  have hpLast : P q (2*q+1) := by unfold P; omega
  by_cases hu : u
  · by_cases hv : v
    · by_cases hw : w
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
            intro e
            simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
            simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
            repeat first | (simp_all <;> omega) | split
          · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
            intro e
            simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
            simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
            repeat first | (simp_all <;> omega) | split
        · by_cases hk2 : k2
          · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
            intro e
            simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
            simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
            repeat first | (simp_all <;> omega) | split
          · exact False.elim (by simp_all)
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
            intro e
            simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
            simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
            repeat first | (simp_all <;> omega) | split
          · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
            intro e
            simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
            simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
            repeat first | (simp_all <;> omega) | split
        · by_cases hk2 : k2
          · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
            intro e
            simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
            simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
            repeat first | (simp_all <;> omega) | split
          · exact False.elim (by simp_all)
    · by_cases hw : w
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
            intro e
            simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
            simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
            repeat first | (simp_all <;> omega) | split
          · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
            intro e
            simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
            simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
            repeat first | (simp_all <;> omega) | split
        · by_cases hk2 : k2
          · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
            intro e
            simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
            simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
            repeat first | (simp_all <;> omega) | split
          · exact False.elim (by simp_all)
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · by_cases he : t=q+3 ∧ p=q+3
            · refine ⟨.ck 1,by simp [NF234.Valid],?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
            · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
          · by_cases he : t=q+3 ∧ p=q+3
            · refine ⟨.ck 1,by simp [NF234.Valid],?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
            · by_cases hl : t=2*q+1
              · refine ⟨.last,True.intro,?_⟩
                intro e
                simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
                simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
                repeat first | (simp_all <;> omega) | split
              · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
                intro e
                simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
                simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
                repeat first | (simp_all <;> omega) | split
        · by_cases hk2 : k2
          · by_cases he : t=q+3 ∧ p=q+3
            · refine ⟨.ck 1,by simp [NF234.Valid],?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
            · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
          · exact False.elim (by simp_all)
  · by_cases hv : v
    · by_cases hw : w
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · by_cases hl : p≤2*q-1
            · refine ⟨.dg p,⟨hp,hl⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
            · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
          · by_cases hl : p≤2*q-1
            · refine ⟨.dg p,⟨hp,hl⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
            · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
        · by_cases hk2 : k2
          · by_cases hl : p≤2*q-1
            · refine ⟨.dg p,⟨hp,hl⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
            · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
          · exact False.elim (by simp_all)
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · by_cases hl : p≤2*q-1
            · refine ⟨.dg p,⟨hp,hl⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
            · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
          · by_cases hl : p≤2*q-1
            · refine ⟨.dg p,⟨hp,hl⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
            · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
        · by_cases hk2 : k2
          · by_cases hl : p≤2*q-1
            · refine ⟨.dg p,⟨hp,hl⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
            · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
          · exact False.elim (by simp_all)
    · by_cases hw : w
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · refine ⟨.kr p 0,⟨hp,by decide⟩,?_⟩
            intro e
            simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
            simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
            repeat first | (simp_all <;> omega) | split
          · refine ⟨.kr p 0,⟨hp,by decide⟩,?_⟩
            intro e
            simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
            simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
            repeat first | (simp_all <;> omega) | split
        · by_cases hk2 : k2
          · refine ⟨.kr p 1,⟨hp,by decide⟩,?_⟩
            intro e
            simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
            simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
            repeat first | (simp_all <;> omega) | split
          · exact False.elim (by simp_all)
      · by_cases hk1 : k1
        · by_cases hk2 : k2
          · by_cases he : t=q+3 ∧ p=q+3
            · refine ⟨.km 0,by simp [NF234.Valid],?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
            · refine ⟨.kr p 0,⟨hp,by decide⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
          · by_cases he : t=q+3 ∧ p=q+3
            · refine ⟨.km 0,by simp [NF234.Valid],?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
            · by_cases hl : t=2*q+1
              · refine ⟨.last,True.intro,?_⟩
                intro e
                simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
                simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
                repeat first | (simp_all <;> omega) | split
              · refine ⟨.kr p 0,⟨hp,by decide⟩,?_⟩
                intro e
                simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
                simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
                repeat first | (simp_all <;> omega) | split
        · by_cases hk2 : k2
          · by_cases he : t=q+3 ∧ p=q+3
            · refine ⟨.km 1,by simp [NF234.Valid],?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
            · refine ⟨.kr p 1,⟨hp,by decide⟩,?_⟩
              intro e
              simp only [Mixed234,Fixed234,hu,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,NF234.eval,T234]
              simp only [LRow,LNormal,CRow,DRow,BRow,K1Row,K2Row,I,beta]
              repeat first | (simp_all <;> omega) | split
          · exact False.elim (by simp_all)

theorem fixed234_normal (q : Nat) (hq : 4≤q) (v w k1 k2 : Prop) (hK : k1∨k2) :
    ∃ z : NF234, z.Valid q ∧ ∀ e, Fixed234 q True v w k1 k2 e ↔ z.eval q e := by
  classical
  have hpLast : P q (2*q+1) := by unfold P; omega
  by_cases hv : v
  · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
    intro e
    simp only [Fixed234,NF234.eval,T234,hv,true_and,CRow,DRow,BRow,K1Row,K2Row,I]
    rcases hK with h | h <;> simp_all <;> omega
  · by_cases hw : w
    · refine ⟨.kr (2*q+1) 0,⟨hpLast,by decide⟩,?_⟩
      intro e
      simp only [Fixed234,NF234.eval,T234,hv,hw,true_and,false_and,false_or,CRow,DRow,BRow,K1Row,K2Row,I]
      rcases hK with h | h <;> simp_all <;> omega
    · by_cases hk2 : k2
      · refine ⟨.ck 1,by simp [NF234.Valid],?_⟩
        intro e
        simp only [Fixed234,NF234.eval,T234,hv,hw,hk2,true_and,false_and,false_or,CRow,DRow,BRow,K1Row,K2Row,I]
        by_cases hk1 : k1 <;> simp_all <;> omega
      · have hk1 : k1 := by simp_all
        refine ⟨.ck 0,by simp [NF234.Valid],?_⟩
        intro e
        simp only [Fixed234,NF234.eval,T234,hv,hw,hk1,hk2,true_and,false_and,false_or,or_false,CRow,DRow,BRow,K1Row,K2Row,I]
        omega
end LuRazClosure
