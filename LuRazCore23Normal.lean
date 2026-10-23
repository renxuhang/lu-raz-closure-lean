import LuRazCore23

namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

inductive NF23 where
  | lp (t p : Nat)
  | filledM
  | dgap (p : Nat)
  | full
  | creg (t : Nat)
  | cexception
  deriving DecidableEq, Repr

def NF23.Valid (q : Nat) : NF23 → Prop
  | .lp t p => P q t ∧ P q p ∧ t≤p
  | .filledM => True
  | .dgap p => P q p ∧ p≤2*q-1
  | .full => True
  | .creg t => P q t ∧ t≠q+3
  | .cexception => True

def NF23.eval (q : Nat) : NF23 → Nat → Prop
  | .lp t p => LRow q t p
  | .filledM => fun e => e=2 ∨ e=3 ∨ I 5 (q+3) e ∨ I (3*q+2) (4*q) e
  | .dgap p => fun e => e=2 ∨ e=3 ∨ I 5 p e ∨ I (2*q+1) (4*q) e
  | .full => fun e => e=2 ∨ e=3 ∨ I 5 (4*q) e
  | .creg t => fun e => e=2 ∨ e=3 ∨ I 5 (2*q+2) e ∨ e=3*q+1 ∨ I (beta q t) (4*q) e
  | .cexception => fun e => e=2 ∨ e=3 ∨ I 5 (2*q+2) e ∨ I (3*q+1) (4*q-1) e

theorem mixed23_normal (q t p : Nat) (hq : 4≤q)
    (ht : P q t) (hp : P q p) (htp : t≤p) (u v w : Prop) :
    ∃ z : NF23, z.Valid q ∧ ∀ e, Mixed23 q t p u v w e ↔ z.eval q e := by
  classical
  have ht' := ht
  have hp' := hp
  unfold P at ht' hp'
  have hpe : P q (q+3) := by unfold P; omega
  have hpr : P q (q+1) := by unfold P; omega
  by_cases hv : v
  · by_cases hu : u
    · refine ⟨.full,True.intro,?_⟩
      intro e
      simp only [Mixed23,NF23.eval,hu,hv,true_and]
      simp only [LRow,LNormal,CRow,DRow,BRow,I,beta]
      repeat first | (simp_all <;> omega) | split
    · by_cases hpl : p≤2*q-1
      · refine ⟨.dgap p,⟨hp,hpl⟩,?_⟩
        intro e
        simp only [Mixed23,NF23.eval,hu,hv,true_and,false_and,false_or]
        simp only [LRow,LNormal,CRow,DRow,BRow,I,beta]
        repeat first | (simp_all <;> omega) | split
      · refine ⟨.full,True.intro,?_⟩
        intro e
        simp only [Mixed23,NF23.eval,hu,hv,true_and,false_and,false_or]
        simp only [LRow,LNormal,CRow,DRow,BRow,I,beta]
        repeat first | (simp_all <;> omega) | split
  · by_cases hu : u
    · by_cases hw : w
      · by_cases htl : t≤q+1
        · refine ⟨.creg t,⟨ht,by omega⟩,?_⟩
          intro e
          simp only [Mixed23,NF23.eval,hu,hv,hw,true_and,false_and,false_or]
          simp only [LRow,LNormal,CRow,DRow,BRow,I,beta]
          repeat first | (simp_all <;> omega) | split
        · refine ⟨.creg (q+1),⟨hpr,by omega⟩,?_⟩
          intro e
          simp only [Mixed23,NF23.eval,hu,hv,hw,true_and,false_and,false_or]
          simp only [LRow,LNormal,CRow,DRow,BRow,I,beta]
          repeat first | (simp_all <;> omega) | split
      · by_cases he : t=q+3 ∧ p=q+3
        · refine ⟨.cexception,True.intro,?_⟩
          intro e
          simp only [Mixed23,NF23.eval,hu,hv,hw,true_and,false_and,false_or,or_false]
          simp only [LRow,LNormal,CRow,DRow,BRow,I,beta]
          repeat first | (simp_all <;> omega) | split
        · by_cases hte : t=q+3
          · refine ⟨.creg (q+1),⟨hpr,by omega⟩,?_⟩
            intro e
            simp only [Mixed23,NF23.eval,hu,hv,hw,true_and,false_and,false_or,or_false]
            simp only [LRow,LNormal,CRow,DRow,BRow,I,beta]
            repeat first | (simp_all <;> omega) | split
          · refine ⟨.creg t,⟨ht,hte⟩,?_⟩
            intro e
            simp only [Mixed23,NF23.eval,hu,hv,hw,true_and,false_and,false_or,or_false]
            simp only [LRow,LNormal,CRow,DRow,BRow,I,beta]
            repeat first | (simp_all <;> omega) | split
    · by_cases hw : w
      · by_cases htl : t≤q+1
        · refine ⟨.lp t p,⟨ht,hp,htp⟩,?_⟩
          intro e
          simp only [Mixed23,NF23.eval,hu,hv,hw,true_and,false_and,false_or]
          simp only [LRow,LNormal,CRow,DRow,BRow,I,beta]
          repeat first | (simp_all <;> omega) | split
        · by_cases hpe' : p=q+3
          · refine ⟨.filledM,True.intro,?_⟩
            intro e
            simp only [Mixed23,NF23.eval,hu,hv,hw,true_and,false_and,false_or]
            simp only [LRow,LNormal,CRow,DRow,BRow,I,beta]
            repeat first | (simp_all <;> omega) | split
          · refine ⟨.lp (q+3) p,⟨hpe,hp,by omega⟩,?_⟩
            intro e
            simp only [Mixed23,NF23.eval,hu,hv,hw,true_and,false_and,false_or]
            simp only [LRow,LNormal,CRow,DRow,BRow,I,beta]
            repeat first | (simp_all <;> omega) | split
      · refine ⟨.lp t p,⟨ht,hp,htp⟩,?_⟩
        intro e
        simp only [Mixed23,NF23.eval,hu,hv,hw,false_and,or_false]

theorem NF23.generated (q : Nat) (hq : 4≤q) (z : NF23) (hz : z.Valid q) :
    Generated q (z.eval q) := by
  have hpe : P q (q+3) := by unfold P; omega
  have hp4 : P q 4 := by unfold P; omega
  cases z with
  | lp t p => exact generated_L q t p hq hz.1 hz.2.1 hz.2.2
  | filledM =>
    apply generated_congr q (mixed23_generated q (q+3) (q+3) hq hpe hpe (by omega) False False True)
    intro e
    change Mixed23 q (q+3) (q+3) False False True e ↔ _
    simp only [Mixed23,NF23.eval,false_and,false_or,true_and,LRow,LNormal,I,beta,BRow]
    repeat first | (simp_all <;> omega) | split
  | dgap p =>
    have hp : P q p ∧ p≤2*q-1 := hz
    have hp' := hp.1
    unfold P at hp'
    apply generated_congr q (mixed23_generated q p p hq hp.1 hp.1 (by omega) False True False)
    intro e
    change Mixed23 q p p False True False e ↔ _
    simp only [Mixed23,NF23.eval,false_and,false_or,or_false,true_and,LRow,LNormal,I,beta,DRow]
    repeat first | (simp_all <;> omega) | split
  | full =>
    apply generated_congr q (generated_join q (generated_C q hq) (generated_D q hq))
    intro e
    change (CRow q e ∨ DRow q e) ↔ (e=2 ∨ e=3 ∨ I 5 (4*q) e)
    unfold CRow DRow I
    omega
  | creg t =>
    have ht : P q t ∧ t≠q+3 := hz
    have ht' := ht.1
    unfold P at ht'
    apply generated_congr q (mixed23_generated q t t hq ht.1 ht.1 (by omega) True False False)
    intro e
    change Mixed23 q t t True False False e ↔ _
    simp only [Mixed23,NF23.eval,false_and,false_or,or_false,true_and,LRow,LNormal,I,beta,CRow]
    repeat first | (simp_all <;> omega) | split
  | cexception =>
    apply generated_congr q (mixed23_generated q (q+3) (q+3) hq hpe hpe (by omega) True False False)
    intro e
    change Mixed23 q (q+3) (q+3) True False False e ↔ _
    simp only [Mixed23,NF23.eval,false_and,false_or,or_false,true_and,LRow,LNormal,I,beta,CRow]
    repeat first | (simp_all <;> omega) | split

theorem NF23.core (q : Nat) (hq : 4≤q) (z : NF23) (hz : z.Valid q) : Core23 (z.eval q) := by
  cases z <;> simp only [NF23.Valid,P] at hz <;>
    simp only [Core23,NF23.eval,LRow,LNormal,I,beta] <;> repeat first | (simp_all <;> omega) | split

theorem core23_closure_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    (Generated q R ∧ Core23 R) ↔ ∃ z : NF23, z.Valid q ∧ ∀ e, R e ↔ z.eval q e := by
  constructor
  · rintro ⟨hg,hc⟩
    obtain ⟨t,p,ht,hp,htp,u,v,w,heq⟩ := full_core23_mixed q hq R hg hc
    obtain ⟨z,hz,he⟩ := mixed23_normal q t p hq ht hp htp u v w
    exact ⟨z,hz,fun e => (heq e).trans (he e)⟩
  · rintro ⟨z,hz,heq⟩
    refine ⟨generated_congr q (NF23.generated q hq z hz) (fun e => (heq e).symm),?_⟩
    have hc := NF23.core q hq z hz
    exact ⟨fun h => hc.1 ((heq 1).mp h),(heq 2).mpr hc.2.1,
      (heq 3).mpr hc.2.2.1,fun h => hc.2.2.2 ((heq 4).mp h)⟩

end LuRazClosure

