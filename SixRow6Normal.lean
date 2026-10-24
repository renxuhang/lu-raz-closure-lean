import SixRow6Parts
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
inductive NF6 where
  | lp (t p : Nat) | filled | creg (t : Nat) | cex | er (p : Nat)
  deriving DecidableEq, Repr
def NF6.Valid (q : Nat) : NF6→Prop
  | .lp t p => P q t ∧ P q p ∧ t≤p ∧ p≤2*q
  | .filled | .cex => True
  | .creg t => P q t ∧ t≤2*q ∧ t≠q+3
  | .er p => P q p
def NF6.eval (q : Nat) : NF6→Nat→Prop
  | .lp t p => LRow q t p
  | .filled => NF23.eval q .filledM
  | .creg t => fun e=>e=2 ∨ e=3 ∨ I 5 (2*q+1) e ∨ e=3*q+1 ∨ I (beta q t) (4*q) e
  | .cex => fun e=>e=2 ∨ e=3 ∨ I 5 (2*q+1) e ∨ I (3*q+1) (4*q-1) e
  | .er p => fun e=>e=2 ∨ e=3 ∨ I 5 p e ∨ I (2*q+3) (4*q) e

theorem fixed6_normal (q : Nat) (hq : 4≤q) (u v w : Prop) (hv : v) :
    ∃z : NF6,z.Valid q ∧ ∀e,Fixed6 q u v w e ↔ z.eval q e := by
  classical
  by_cases hu : u
  · refine ⟨.er (2*q+1),?_,?_⟩
    · unfold NF6.Valid P; omega
    · intro e
      by_cases hw : w <;> simp only [Fixed6,NF6.eval,hu,hv,hw,true_and,false_and,false_or,or_false,C6,E6,LuRazClosure.BRow,I] <;> omega
  · refine ⟨.er 4,?_,?_⟩
    · unfold NF6.Valid P; omega
    · intro e
      by_cases hw : w <;> simp only [Fixed6,NF6.eval,hu,hv,hw,true_and,false_and,false_or,or_false,C6,E6,LuRazClosure.BRow,I] <;> omega

theorem mixed6_normal (q t p : Nat) (hq : 4≤q)
    (ht : P q t) (hp : P q p) (htp : t≤p) (hph : p≤2*q) (u v w : Prop) :
    ∃z : NF6,z.Valid q ∧ ∀e,Mixed6 q t p u v w e ↔ z.eval q e := by
  classical
  have ht' := ht
  have hp' := hp
  unfold P at ht' hp'
  have hpe : P q (q+3) := by unfold P; omega
  have hpr : P q (q+1) := by unfold P; omega
  by_cases hv : v
  · by_cases hu : u
    · refine ⟨.er (2*q+1),by unfold NF6.Valid P; omega,?_⟩
      intro e
      by_cases hw : w <;> simp only [Mixed6,Fixed6,NF6.eval,hu,hv,hw,true_and,false_and,false_or,or_false,C6,E6,LRow,LNormal,LuRazClosure.BRow,I,beta] <;>
        repeat first | omega | (simp_all <;> omega) | split
    · refine ⟨.er p,hp,?_⟩
      intro e
      by_cases hw : w <;> simp only [Mixed6,Fixed6,NF6.eval,hu,hv,hw,true_and,false_and,false_or,or_false,C6,E6,LRow,LNormal,LuRazClosure.BRow,I,beta] <;>
        repeat first | omega | (simp_all <;> omega) | split
  · by_cases hu : u
    · by_cases hw : w
      · by_cases htl : t≤q+1
        · refine ⟨.creg t,⟨ht,by omega,by omega⟩,?_⟩
          intro e
          simp only [Mixed6,Fixed6,NF6.eval,hu,hv,hw,true_and,false_and,false_or,or_false,C6,E6,LRow,LNormal,LuRazClosure.BRow,I,beta]
          repeat first | omega | (simp_all <;> omega) | split
        · refine ⟨.creg (q+1),⟨hpr,by omega,by omega⟩,?_⟩
          intro e
          simp only [Mixed6,Fixed6,NF6.eval,hu,hv,hw,true_and,false_and,false_or,or_false,C6,E6,LRow,LNormal,LuRazClosure.BRow,I,beta]
          repeat first | omega | (simp_all <;> omega) | split
      · by_cases he : t=q+3 ∧ p=q+3
        · refine ⟨.cex,True.intro,?_⟩
          intro e
          simp only [Mixed6,Fixed6,NF6.eval,hu,hv,hw,true_and,false_and,false_or,or_false,C6,E6,LRow,LNormal,LuRazClosure.BRow,I,beta]
          repeat first | omega | (simp_all <;> omega) | split
        · by_cases hte : t=q+3
          · refine ⟨.creg (q+1),⟨hpr,by omega,by omega⟩,?_⟩
            intro e
            simp only [Mixed6,Fixed6,NF6.eval,hu,hv,hw,true_and,false_and,false_or,or_false,C6,E6,LRow,LNormal,LuRazClosure.BRow,I,beta]
            repeat first | omega | (simp_all <;> omega) | split
          · refine ⟨.creg t,⟨ht,by omega,hte⟩,?_⟩
            intro e
            simp only [Mixed6,Fixed6,NF6.eval,hu,hv,hw,true_and,false_and,false_or,or_false,C6,E6,LRow,LNormal,LuRazClosure.BRow,I,beta]
            repeat first | omega | (simp_all <;> omega) | split
    · by_cases hw : w
      · by_cases htl : t≤q+1
        · refine ⟨.lp t p,⟨ht,hp,htp,hph⟩,?_⟩
          intro e
          simp only [Mixed6,Fixed6,NF6.eval,hu,hv,hw,true_and,false_and,false_or,or_false,C6,E6,LRow,LNormal,LuRazClosure.BRow,I,beta]
          repeat first | omega | (simp_all <;> omega) | split
        · by_cases hpe0 : p=q+3
          · refine ⟨.filled,True.intro,?_⟩
            intro e
            simp only [Mixed6,Fixed6,NF6.eval,NF23.eval,hu,hv,hw,true_and,false_and,false_or,or_false,C6,E6,LRow,LNormal,LuRazClosure.BRow,I,beta]
            repeat first | omega | (simp_all <;> omega) | split
          · refine ⟨.lp (q+3) p,⟨hpe,hp,by omega,hph⟩,?_⟩
            intro e
            simp only [Mixed6,Fixed6,NF6.eval,hu,hv,hw,true_and,false_and,false_or,or_false,C6,E6,LRow,LNormal,LuRazClosure.BRow,I,beta]
            repeat first | omega | (simp_all <;> omega) | split
      · exact ⟨.lp t p,⟨ht,hp,htp,hph⟩,by intro e; simp [Mixed6,Fixed6,NF6.eval,hu,hv,hw]⟩

theorem core6_normal (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : Generated q R) (hc : Core23 R) : ∃z : NF6,z.Valid q ∧ ∀e,R e ↔ z.eval q e := by
  obtain ⟨u,v,w,hn⟩ := core6_parts q hq R hg hc
  rcases hn with ⟨hv,hn⟩|⟨t,p,ht,hp,htp,hph,hn⟩
  · obtain ⟨z,hz,he⟩ := fixed6_normal q hq u v w hv
    exact ⟨z,hz,fun e=>(hn e).trans (he e)⟩
  · obtain ⟨z,hz,he⟩ := mixed6_normal q t p hq ht hp htp hph u v w
    exact ⟨z,hz,fun e=>(hn e).trans (he e)⟩
end LuRazSixRowClosure
