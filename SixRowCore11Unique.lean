import SixRowCore11Normal

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def swapLast11 (q e : Nat) : Nat :=
  if e=4*q-1 then 4*q else if e=4*q then 4*q-1 else e

theorem swapLast11_involutive (q e : Nat) (hq : 4≤q) :
    swapLast11 q (swapLast11 q e)=e := by
  by_cases ha : e=4*q-1 <;> by_cases hb : e=4*q <;>
    simp [swapLast11,ha,hb,show 4*q≠4*q-1 by omega,show 4*q-1≠4*q by omega] <;> omega

def NF11.toOld : NF11 → NF124
  | .interval a k => .interval a k
  | .agap a k => .agap a k
  | .ak 0 => .ak .k1
  | .ak 1 => .ak .k2
  | .ak 2 => .ak .joinK
  | .ak 3 => .ak .fill1
  | .ak 4 => .ak .fill2
  | .ak _ => .ak .dBig

def NF11.fromOld : NF124 → NF11
  | .interval a k => .interval a k
  | .agap a k => .agap a k
  | .ak .k1 => .ak 0
  | .ak .k2 => .ak 1
  | .ak .joinK => .ak 2
  | .ak .fill1 => .ak 3
  | .ak .fill2 => .ak 4
  | .ak .dBig => .ak 5

theorem NF11.toOld_valid (q : Nat) (w : NF11) (hw : w.Valid q) : w.toOld.Valid q := by
  cases w with
  | interval a k => exact hw
  | agap a k => exact hw
  | ak k =>
    have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by simpa [NF11.Valid] using (show k<5 from hw) |> (fun h => by omega)
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp [NF11.toOld,NF124.Valid]

theorem NF11.fromOld_toOld (q : Nat) (w : NF11) (hw : w.Valid q) :
    fromOld w.toOld=w := by
  cases w with
  | interval a k => rfl
  | agap a k => rfl
  | ak k =>
    have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by have : k<5 := hw; omega
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem NF11.transpose_eval (q : Nat) (hq : 4≤q) (w : NF11) (hw : w.Valid q) (e : Nat) :
    w.eval q e ↔ w.toOld.eval q (swapLast11 q e) := by
  cases w with
  | interval a k =>
    have ha := hw.1
    have hk : k=0 ∨ k=1 ∨ k=2 := by have : k<3 := hw.2; omega
    rcases hk with rfl | rfl | rfl <;>
      by_cases he1 : e=4*q-1 <;> by_cases he2 : e=4*q <;>
      simp [he1,he2,show 4*q≠4*q-1 by omega,NF11.toOld,NF11.eval,Head11,Tail11,NF124.eval,T124,swapLast11,I] <;> omega
  | agap a k =>
    have ha := hw.1
    have hk : k=0 ∨ k=1 ∨ k=2 := by have : k<3 := hw.2; omega
    rcases hk with rfl | rfl | rfl <;>
      by_cases he1 : e=4*q-1 <;> by_cases he2 : e=4*q <;>
      simp [he1,he2,show 4*q≠4*q-1 by omega,NF11.toOld,NF11.eval,Head11,Tail11,NF124.eval,T124,ARow,swapLast11,I] <;> omega
  | ak k =>
    have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by have : k<5 := hw; omega
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      by_cases he1 : e=4*q-1 <;> by_cases he2 : e=4*q <;>
      simp [he1,he2,show 4*q≠4*q-1 by omega,NF11.toOld,NF11.eval,FixedPick11,NF124.eval,NF24.eval,ARow,K1Row,K2Row,KPrime14,LuRazClosure.BRow,swapLast11,I] <;> omega

theorem NF11.unique (q : Nat) (hq : 4≤q) (a b : NF11)
    (ha : a.Valid q) (hb : b.Valid q) (he : ∀e,a.eval q e ↔ b.eval q e) : a=b := by
  have hh : ∀e,a.toOld.eval q e ↔ b.toOld.eval q e := by
    intro e
    have h := he (swapLast11 q e)
    rw [a.transpose_eval q hq ha, b.transpose_eval q hq hb,swapLast11_involutive q e hq] at h
    exact h
  have h := NF124.unique q hq a.toOld b.toOld (a.toOld_valid q ha) (b.toOld_valid q hb) hh
  have hh := congrArg NF11.fromOld h
  simpa [a.fromOld_toOld q ha,b.fromOld_toOld q hb] using hh

end LuRazSixRowClosure




