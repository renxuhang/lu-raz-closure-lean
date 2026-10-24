import SixRowClosureDefs

namespace LuRazSixRowClosure.Small
open LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

def SA (q e : Nat) : Prop := e=1 ∨ I 5 (q+2) e
def SB (q e : Nat) : Prop := I (3*q+2) (4*q) e
def SC (q e : Nat) : Prop := e=3 ∨ I 5 (2*q+1) e ∨ e=3*q+1 ∨ e=4*q-1
def SZ (q e : Nat) : Prop := e=1 ∨ e=3 ∨ I 5 (2*q) e ∨ e=4*q-1 ∨ e=4*q
def SL (q e : Nat) : Prop := e=1 ∨ e=3 ∨ I 5 (2*q+2) e

def Mix (q : Nat) (a b c z l : Prop) (e : Nat) : Prop :=
  (a ∧ SA q e) ∨ (b ∧ SB q e) ∨ (c ∧ SC q e) ∨ (z ∧ SZ q e) ∨ (l ∧ SL q e)

inductive Normal where
  | a
  | b
  | ab
  | c
  | ac
  | cb
  | acb
  | z
  | zb
  | cz
  | l
  | lb
  | cl
  | clb
  | zl
  | czl
  deriving DecidableEq, Repr

def Normal.eval (q : Nat) : Normal → Nat → Prop
  | .a => fun e => SA q e
  | .b => fun e => SB q e
  | .ab => fun e => SA q e ∨ SB q e
  | .c => fun e => SC q e
  | .ac => fun e => SA q e ∨ SC q e
  | .cb => fun e => SB q e ∨ SC q e
  | .acb => fun e => SA q e ∨ SB q e ∨ SC q e
  | .z => fun e => SZ q e
  | .zb => fun e => SB q e ∨ SZ q e
  | .cz => fun e => SC q e ∨ SZ q e
  | .l => fun e => SL q e
  | .lb => fun e => SB q e ∨ SL q e
  | .cl => fun e => SC q e ∨ SL q e
  | .clb => fun e => SB q e ∨ SC q e ∨ SL q e
  | .zl => fun e => SZ q e ∨ SL q e
  | .czl => fun e => SC q e ∨ SZ q e ∨ SL q e

theorem mix_normal (q : Nat) (hq : 4≤q) (a b c z l : Prop)
    (hne : a ∨ b ∨ c ∨ z ∨ l) :
    ∃ x : Normal, ∀e,Mix q a b c z l e ↔ x.eval q e := by
  classical
  by_cases ha : a
  ·
    by_cases hb : b
    ·
      by_cases hc : c
      ·
        by_cases hz : z
        ·
          by_cases hl : l
          ·
            refine ⟨.clb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.acb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
        ·
          by_cases hl : l
          ·
            refine ⟨.clb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.acb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
      ·
        by_cases hz : z
        ·
          by_cases hl : l
          ·
            refine ⟨.lb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.zb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
        ·
          by_cases hl : l
          ·
            refine ⟨.lb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.ab,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
    ·
      by_cases hc : c
      ·
        by_cases hz : z
        ·
          by_cases hl : l
          ·
            refine ⟨.czl,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.cz,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
        ·
          by_cases hl : l
          ·
            refine ⟨.cl,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.ac,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
      ·
        by_cases hz : z
        ·
          by_cases hl : l
          ·
            refine ⟨.zl,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.z,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
        ·
          by_cases hl : l
          ·
            refine ⟨.l,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.a,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
  ·
    by_cases hb : b
    ·
      by_cases hc : c
      ·
        by_cases hz : z
        ·
          by_cases hl : l
          ·
            refine ⟨.clb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.acb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
        ·
          by_cases hl : l
          ·
            refine ⟨.clb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.cb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
      ·
        by_cases hz : z
        ·
          by_cases hl : l
          ·
            refine ⟨.lb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.zb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
        ·
          by_cases hl : l
          ·
            refine ⟨.lb,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.b,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
    ·
      by_cases hc : c
      ·
        by_cases hz : z
        ·
          by_cases hl : l
          ·
            refine ⟨.czl,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.cz,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
        ·
          by_cases hl : l
          ·
            refine ⟨.cl,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.c,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
      ·
        by_cases hz : z
        ·
          by_cases hl : l
          ·
            refine ⟨.zl,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            refine ⟨.z,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
        ·
          by_cases hl : l
          ·
            refine ⟨.l,?_⟩
            intro e
            simp only [Mix,Normal.eval,ha,hb,hc,hz,hl,true_and,false_and,false_or,or_false]
            all_goals (simp only [SA,SB,SC,SZ,SL,I] <;> omega)
          ·
            exact False.elim (by simp_all)

end LuRazSixRowClosure.Small
