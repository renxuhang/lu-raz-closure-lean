import SixRowClosureDefs

namespace LuRazSixRowClosure.Difference
open LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def A (q e : Nat) : Prop := I 5 (q+2) e
def B (q e : Nat) : Prop := I (3*q+2) (4*q) e
def C (q e : Nat) : Prop := I 5 (2*q+2) e ∨ e=3*q+1
def Ct (q e : Nat) : Prop := I 5 (2*q+1) e ∨ e=3*q+1
def Cp (q e : Nat) : Prop := Ct q e ∨ e=4*q-1
def Lp (q e : Nat) : Prop := I 5 (2*q+1) e ∨ e=4*q
def Zp (q e : Nat) : Prop := I 5 (2*q) e ∨ I (4*q-1) (4*q) e
def Ep (q e : Nat) : Prop := I (2*q+3) (4*q-2) e ∨ e=4*q
def Lnew (q e : Nat) : Prop := I 5 (2*q+2) e
def Suffix (q t e : Nat) : Prop :=
  (t≤q+1 ∧ I (2*q+t) (4*q) e) ∨ (q+1<t ∧ I (2*q+t-1) (4*q) e)

inductive RemovedForm where
  | r2
  | r3
  | r4 (k : Nat)
  | r5
  | r6regular (t : Nat)
  | r6exception
  | r6d (p : Nat)
  | r7fresh (k : Nat)
  | r7e (p : Nat)
  | r7d (p : Nat)
  | r10 (t : Nat)
  | r11j (a : Nat)
  | r11aj (a : Nat)
  | r11ak (t : Nat)
  | r12 (k : Nat)
  | r13cj (b : Nat)
  | r13zj (b : Nat)
  | r13czj (b : Nat)
  | r13points (k : Nat)
  | r14points (k : Nat)
  | r14line (t : Nat)
  | r14c (t : Nat)
  | r15points (k : Nat)
  | r15right (a : Nat)
  | r15gap (a : Nat)
  | r15line (t : Nat)
  | r15short (p t : Nat)
  deriving DecidableEq, Repr

def RemovedForm.Valid (q : Nat) : RemovedForm → Prop
  | .r2 => True
  | .r3 => True
  | .r4 k => k≤1
  | .r5 => True
  | .r6regular t => P q t ∧ t≤2*q ∧ t≠q+3
  | .r6exception => True
  | .r6d p => p=0 ∨ (P q p ∧ p≤2*q-1)
  | .r7fresh k => k≤2
  | .r7e p => 4≤p ∧ p≤q+1
  | .r7d p => 4≤p ∧ p≤2*q-1
  | .r10 t => t=2*q+2 ∨ t=2*q+3
  | .r11j a => 5≤a ∧ a≤2*q+1
  | .r11aj a => q+4≤a ∧ a≤2*q+1
  | .r11ak t => t=2*q+2 ∨ t=2*q+3
  | .r12 k => k≤3
  | .r13cj b => 2*q+2≤b ∧ b≤3*q-1
  | .r13zj b => 2*q+2≤b ∧ b≤4*q-3
  | .r13czj b => 2*q+2≤b ∧ b≤3*q-1
  | .r13points k => k≤2
  | .r14points k => k≤2
  | .r14line t => 2*q+4≤t ∧ t≤4*q-1
  | .r14c t => 2*q+4≤t ∧ t≤4*q-1 ∧ t≠3*q+2
  | .r15points k => k≤1
  | .r15right a => 6≤a ∧ a≤2*q+2
  | .r15gap a => q+4≤a ∧ a≤2*q+2
  | .r15line t => 2*q+4≤t ∧ t≤4*q-1
  | .r15short p t => 4≤p ∧ p≤q+1 ∧ (t=2*q+2 ∨ t=2*q+3)

def RemovedForm.eval (q : Nat) : RemovedForm → Nat → Prop
  | .r2 => fun e => (e=2) ∨ (I (2*q+1) (4*q) e)
  | .r3 => fun e => (e=1 ∨ e=2) ∨ (A q e ∨ I (2*q+1) (4*q) e)
  | .r4 k => fun e => (e=3) ∨ ((k=0 ∧ C q e) ∨ (k=1 ∧ (C q e ∨ B q e)))
  | .r5 => fun e => (e=1 ∨ e=3) ∨ (C q e)
  | .r6regular t => fun e => (e=2 ∨ e=3) ∨ (C q e ∨ Suffix q t e)
  | .r6exception => fun e => (e=2 ∨ e=3) ∨ (C q e ∨ I (3*q+1) (4*q-1) e)
  | .r6d p => fun e => (e=2 ∨ e=3) ∨ ((p=0 ∧ I 5 (4*q) e) ∨ (p≠0 ∧ (I 5 p e ∨ I (2*q+1) (4*q) e)))
  | .r7fresh k => fun e => (e=1 ∨ e=2 ∨ e=3) ∨ ((k=0 ∧ Ep q e) ∨ (k=1 ∧ (A q e ∨ Ep q e)) ∨ (k=2 ∧ (I 5 (4*q-2) e ∨ e=4*q)))
  | .r7e p => fun e => (e=1 ∨ e=2 ∨ e=3) ∨ (I 5 p e ∨ I (2*q+3) (4*q) e)
  | .r7d p => fun e => (e=1 ∨ e=2 ∨ e=3) ∨ (I 5 p e ∨ I (2*q+1) (4*q) e)
  | .r10 t => fun e => (e=2 ∨ e=4) ∨ (I t (4*q-1) e)
  | .r11j a => fun e => (e=1 ∨ e=2 ∨ e=4) ∨ (I a (4*q-1) e)
  | .r11aj a => fun e => (e=1 ∨ e=2 ∨ e=4) ∨ (A q e ∨ I a (4*q-1) e)
  | .r11ak t => fun e => (e=1 ∨ e=2 ∨ e=4) ∨ (A q e ∨ I t (4*q-1) e)
  | .r12 k => fun e => (e=3 ∨ e=4) ∨ (Lp q e ∨ ((k=1 ∨ k=3) ∧ B q e) ∨ (2≤k ∧ C q e))
  | .r13cj b => fun e => (e=1 ∨ e=3 ∨ e=4) ∨ (I 5 b e ∨ e=3*q+1)
  | .r13zj b => fun e => (e=1 ∨ e=3 ∨ e=4) ∨ (I 5 b e ∨ e=4*q)
  | .r13czj b => fun e => (e=1 ∨ e=3 ∨ e=4) ∨ (I 5 b e ∨ e=3*q+1 ∨ e=4*q)
  | .r13points k => fun e => (e=1 ∨ e=3 ∨ e=4) ∨ ((k=0 ∧ Lp q e) ∨ (k=1 ∧ (Lp q e ∨ B q e)) ∨ (k=2 ∧ (I 5 (2*q+1) e ∨ I (4*q-1) (4*q) e)))
  | .r14points k => fun e => (e=2 ∨ e=3 ∨ e=4) ∨ ((k=0 ∧ I 5 (4*q-2) e) ∨ (k=1 ∧ (I 5 (q+3) e ∨ I (2*q+3) (4*q-1) e)) ∨ (k=2 ∧ (I 5 (4*q-2) e ∨ e=4*q)))
  | .r14line t => fun e => (e=2 ∨ e=3 ∨ e=4) ∨ (I 5 (2*q+1) e ∨ I t (4*q) e)
  | .r14c t => fun e => (e=2 ∨ e=3 ∨ e=4) ∨ (C q e ∨ I t (4*q) e)
  | .r15points k => fun e => (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ ((k=0 ∧ (I 5 (q+3) e ∨ I (2*q+3) (4*q-1) e)) ∨ (k=1 ∧ (I 5 (2*q+1) e ∨ I (2*q+3) (4*q-2) e ∨ e=4*q)))
  | .r15right a => fun e => (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (I a (4*q-2) e ∨ e=4*q)
  | .r15gap a => fun e => (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (A q e ∨ I a (4*q-2) e ∨ e=4*q)
  | .r15line t => fun e => (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (I 5 (2*q+1) e ∨ I t (4*q) e)
  | .r15short p t => fun e => (e=1 ∨ e=2 ∨ e=3 ∨ e=4) ∨ (I 5 p e ∨ I t (4*q) e)

inductive AddedForm where
  | n4 (k : Nat)
  | n5 (k : Nat)
  | n6regular (t : Nat)
  | n6exception
  | n6e (p : Nat)
  | n7regular (t : Nat)
  | n7exception
  | n7right (t : Nat)
  | n7point
  | n10 (t : Nat)
  | n11j (a : Nat)
  | n11aj (a : Nat)
  | n11ak (t : Nat)
  | n13plain (b : Nat)
  | n13isolated (b : Nat)
  | n13right (b : Nat)
  deriving DecidableEq, Repr

def AddedForm.Valid (q : Nat) : AddedForm → Prop
  | .n4 k => k≤1
  | .n5 k => k≤6
  | .n6regular t => P q t ∧ t≤2*q ∧ t≠q+3
  | .n6exception => True
  | .n6e p => P q p
  | .n7regular t => P q t ∧ t≤2*q ∧ t≠q+3
  | .n7exception => True
  | .n7right t => t=0 ∨ (3*q+2≤t ∧ t≤4*q-1)
  | .n7point => True
  | .n10 t => t=2*q+1 ∨ t=2*q+2 ∨ t=2*q+3
  | .n11j a => 5≤a ∧ a≤2*q+1
  | .n11aj a => q+4≤a ∧ a≤2*q+1
  | .n11ak t => t=2*q+2 ∨ t=2*q+3
  | .n13plain b => 2*q+2≤b ∧ b≤3*q
  | .n13isolated b => 2*q+2≤b ∧ b≤3*q-1
  | .n13right b => 3*q+1≤b ∧ b≤4*q-3

def AddedForm.eval (q : Nat) : AddedForm → Nat → Prop
  | .n4 k => fun e => (e=3) ∨ ((k=0 ∧ Cp q e) ∨ (k=1 ∧ (Cp q e ∨ B q e)))
  | .n5 k => fun e => (e=1 ∨ e=3) ∨ ((k=0 ∧ Lnew q e) ∨ (k=1 ∧ Cp q e) ∨ (k=2 ∧ (Lnew q e ∨ Cp q e)) ∨ (k=3 ∧ (Lnew q e ∨ Zp q e)) ∨ (k=4 ∧ (Cp q e ∨ Zp q e)) ∨ (k=5 ∧ (Lnew q e ∨ B q e)) ∨ (k=6 ∧ (Cp q e ∨ B q e)))
  | .n6regular t => fun e => (e=2 ∨ e=3) ∨ (Ct q e ∨ Suffix q t e)
  | .n6exception => fun e => (e=2 ∨ e=3) ∨ (Ct q e ∨ I (3*q+1) (4*q-1) e)
  | .n6e p => fun e => (e=2 ∨ e=3) ∨ (I 5 p e ∨ I (2*q+3) (4*q) e)
  | .n7regular t => fun e => (e=1 ∨ e=2 ∨ e=3) ∨ (Ct q e ∨ Suffix q t e)
  | .n7exception => fun e => (e=1 ∨ e=2 ∨ e=3) ∨ (Ct q e ∨ I (3*q+1) (4*q-1) e)
  | .n7right t => fun e => (e=1 ∨ e=2 ∨ e=3) ∨ (Lnew q e ∨ (t=0 ∧ I (3*q+2) (4*q-1) e) ∨ (t≠0 ∧ I t (4*q) e))
  | .n7point => fun e => (e=1 ∨ e=2 ∨ e=3) ∨ (I 5 (2*q+1) e ∨ I (2*q+3) (4*q) e)
  | .n10 t => fun e => (e=2 ∨ e=4) ∨ (I t (4*q-2) e ∨ e=4*q)
  | .n11j a => fun e => (e=1 ∨ e=2 ∨ e=4) ∨ (I a (4*q-2) e ∨ e=4*q)
  | .n11aj a => fun e => (e=1 ∨ e=2 ∨ e=4) ∨ (A q e ∨ I a (4*q-2) e ∨ e=4*q)
  | .n11ak t => fun e => (e=1 ∨ e=2 ∨ e=4) ∨ (A q e ∨ I t (4*q-2) e ∨ e=4*q)
  | .n13plain b => fun e => (e=1 ∨ e=3 ∨ e=4) ∨ (I 5 b e)
  | .n13isolated b => fun e => (e=1 ∨ e=3 ∨ e=4) ∨ (I 5 b e ∨ e=3*q+1 ∨ e=4*q-1)
  | .n13right b => fun e => (e=1 ∨ e=3 ∨ e=4) ∨ (I 5 b e ∨ e=4*q-1)

end LuRazSixRowClosure.Difference
