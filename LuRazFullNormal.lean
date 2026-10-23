import LuRazFullReduction
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def FullHead (e : Nat) : Prop := e=1 ∨ e=2 ∨ e=3 ∨ e=4
inductive NFFull where
  | noNInterval (k : Nat)
  | noNMJRight (b : Nat)
  | noNMJLeft (a : Nat)
  | noNMK (k : Nat)
  | noNCMJ (b : Nat)
  | noH1Short (p k : Nat)
  | noH1ZL (a : Nat)
  | noH1Exception
  | noH2 (a : Nat)
  | noFive (a : Nat)
  | leftGap (p a : Nat)
  | full
  | rightGap (b c : Nat)
  | isolatedR (b c : Nat)
  deriving DecidableEq, Repr

def NFFull.Valid (q : Nat) : NFFull → Prop
  | .noNInterval k | .noNMK k => k<2
  | .noNMJRight b => 2*q+2≤b ∧ b≤3*q
  | .noNMJLeft a => q+5≤a ∧ a≤2*q+1
  | .noNCMJ b => 2*q+2≤b ∧ b≤3*q-1
  | .noH1Short p k => (4≤p ∧ p≤2*q) ∧ k<2
  | .noH1ZL a => 2*q+4≤a ∧ a≤4*q-1
  | .noH1Exception | .full => True
  | .noH2 a => 2*q+3≤a ∧ a≤4*q
  | .noFive a => 6≤a ∧ a≤2*q+1
  | .leftGap p a => (5≤p ∧ p≤2*q-1) ∧ p+2≤a ∧ a≤2*q+1
  | .rightGap b c => (2*q+2≤b ∧ b≤4*q-2) ∧ b+2≤c ∧ c≤4*q
  | .isolatedR b c => (2*q+2≤b ∧ b≤3*q-1) ∧ 3*q+3≤c ∧ c≤4*q

def NFFull.eval (q : Nat) (z : NFFull) (e : Nat) : Prop := FullHead e ∨ match z with
  | .noNInterval k => I 5 (4*q-2+k) e
  | .noNMJRight b => I 5 b e ∨ I (3*q+2) (4*q-1) e
  | .noNMJLeft a => I 5 (q+3) e ∨ I a (4*q-1) e
  | .noNMK k => I 5 (q+3) e ∨ I (2*q+2+k) (4*q-1) e
  | .noNCMJ b => I 5 b e ∨ I (3*q+1) (4*q-1) e
  | .noH1Short p k => I 5 p e ∨ I (2*q+2+k) (4*q) e
  | .noH1ZL a => I 5 (2*q) e ∨ I a (4*q) e
  | .noH1Exception => I 5 (2*q) e ∨ I (2*q+2) (4*q-2) e ∨ e=4*q
  | .noH2 a => I 5 (2*q+1) e ∨ I a (4*q) e
  | .noFive a => I a (4*q) e
  | .leftGap p a => I 5 p e ∨ I a (4*q) e
  | .full => I 5 (4*q) e
  | .rightGap b c => I 5 b e ∨ I c (4*q) e
  | .isolatedR b c => I 5 b e ∨ e=3*q+1 ∨ I c (4*q) e

theorem d134_full_normal (q : Nat) (hq : 4≤q) (z : NF134) (hz : z.Valid q) :
    ∃ w : NFFull, w.Valid q ∧ ∀ e, (DRow q e ∨ z.eval q e) ↔ w.eval q e := by
  cases z with
  | ej a =>
    have ha : 5≤a ∧ a≤2*q+1 := hz
    by_cases he : a=5
    · refine ⟨.full,True.intro,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,NF134.eval,T134,DRow,I]
      omega
    · refine ⟨.noFive a,by change 6≤a ∧ a≤2*q+1; omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,NF134.eval,T134,DRow,I]
      omega
  | aej a =>
    have ha : q+4≤a ∧ a≤2*q+1 := hz
    refine ⟨.leftGap (q+2) a,by change (5≤q+2 ∧ q+2≤2*q-1) ∧ q+2+2≤a ∧ a≤2*q+1; omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,NF134.eval,T134,DRow,I]
    omega
  | cj b =>
    have hb := hz
    simp only [NF134.Valid] at hb
    refine ⟨.full,True.intro,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,NF134.eval,T134,DRow,ZRow,BRow,ERow,I]
    omega
  | zj b =>
    have hb := hz
    simp only [NF134.Valid] at hb
    refine ⟨.full,True.intro,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,NF134.eval,T134,DRow,ZRow,BRow,ERow,I]
    omega
  | czj b =>
    have hb := hz
    simp only [NF134.Valid] at hb
    refine ⟨.full,True.intro,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,NF134.eval,T134,DRow,ZRow,BRow,ERow,I]
    omega
  | zjb b =>
    have hb := hz
    simp only [NF134.Valid] at hb
    refine ⟨.full,True.intro,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,NF134.eval,T134,DRow,ZRow,BRow,ERow,I]
    omega
  | cjb b =>
    have hb := hz
    simp only [NF134.Valid] at hb
    refine ⟨.full,True.intro,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,NF134.eval,T134,DRow,ZRow,BRow,ERow,I]
    omega
  | extra b =>
    have hb := hz
    simp only [NF134.Valid] at hb
    refine ⟨.full,True.intro,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,NF134.eval,T134,DRow,ZRow,BRow,ERow,I]
    omega

theorem a234_full_normal (q : Nat) (hq : 4≤q) (z : NF234) (hz : z.Valid q) (v : Prop) :
    ∃ w : NFFull, w.Valid q ∧ ∀ e, (z.eval q e ∨ ARow q e ∨ (v∧BRow q e)) ↔ w.eval q e := by
  classical
  cases z with
  | kr p k =>
    have hb : P q p ∧ k<2 := hz
    have hp := hb.1
    unfold P at hp
    by_cases hl : p≤2*q
    · refine ⟨.noH1Short (max p (q+2)) k,by change (4≤max p (q+2) ∧ max p (q+2)≤2*q) ∧ k<2; omega,?_⟩
      intro e
      by_cases hv : v <;> simp only [NF234.eval,T234,NFFull.eval,FullHead,ARow,BRow,hv,true_and,false_and,false_or,or_false,I] <;> omega
    · by_cases hk : k=0
      · refine ⟨.full,True.intro,?_⟩
        intro e
        by_cases hv : v <;> simp only [NF234.eval,T234,NFFull.eval,FullHead,ARow,BRow,hv,true_and,false_and,false_or,or_false,I] <;> omega
      · refine ⟨.noH2 (2*q+3),by change 2*q+3≤2*q+3 ∧ 2*q+3≤4*q; omega,?_⟩
        intro e
        by_cases hv : v <;> simp only [NF234.eval,T234,NFFull.eval,FullHead,ARow,BRow,hv,true_and,false_and,false_or,or_false,I] <;> omega
  | dg p =>
    have hb : P q p ∧ p≤2*q-1 := hz
    have hp := hb.1
    unfold P at hp
    refine ⟨.leftGap (max p (q+2)) (2*q+1),by change (5≤max p (q+2) ∧ max p (q+2)≤2*q-1) ∧ max p (q+2)+2≤2*q+1 ∧ 2*q+1≤2*q+1; omega,?_⟩
    intro e
    by_cases hv : v <;> simp only [NF234.eval,T234,NFFull.eval,FullHead,ARow,BRow,hv,true_and,false_and,false_or,or_false,I] <;> omega
  | km k =>
    have hk : k<2 := hz
    by_cases hv : v
    · refine ⟨.noH1Short (q+3) k,by change (4≤q+3 ∧ q+3≤2*q) ∧ k<2; omega,?_⟩
      intro e
      simp only [NF234.eval,T234,NFFull.eval,FullHead,ARow,BRow,hv,true_and,I]
      omega
    · refine ⟨.noNMK k,hk,?_⟩
      intro e
      simp only [NF234.eval,T234,NFFull.eval,FullHead,ARow,BRow,hv,false_and,or_false,I]
      omega
  | ck k =>
    have hk : k<2 := hz
    by_cases hv : v
    · refine ⟨.full,True.intro,?_⟩
      intro e
      simp only [NF234.eval,T234,NFFull.eval,FullHead,ARow,BRow,hv,true_and,I]
      omega
    · refine ⟨.noNInterval k,hk,?_⟩
      intro e
      simp only [NF234.eval,T234,NFFull.eval,FullHead,ARow,BRow,hv,false_and,or_false,I]
      omega
  | last =>
    by_cases hv : v
    · refine ⟨.full,True.intro,?_⟩
      intro e
      simp only [NF234.eval,T234,NFFull.eval,FullHead,ARow,BRow,hv,true_and,I]
      omega
    · refine ⟨.rightGap (4*q-2) (4*q),by change (2*q+2≤4*q-2 ∧ 4*q-2≤4*q-2) ∧ 4*q-2+2≤4*q ∧ 4*q≤4*q; omega,?_⟩
      intro e
      simp only [NF234.eval,T234,NFFull.eval,FullHead,ARow,BRow,hv,false_and,or_false,I]
      omega

end LuRazClosure
