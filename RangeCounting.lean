import Std

namespace LuRazCounting

def sumTo (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n+1 => sumTo f n + f n

noncomputable def mark (P : Prop) : Int := by
  classical
  exact if P then 1 else 0

theorem mark_zero (P : Prop) (h : ¬ P) : mark P = 0 := by
  classical
  exact if_neg h
theorem mark_and_true (P Q : Prop)
    (h : P) : mark (P ∧ Q) = mark Q := by
  classical
  by_cases hq : Q <;> simp [mark,h,hq]

theorem mark_congr {P Q : Prop} (h : P ↔ Q) : mark P = mark Q := by
  classical
  by_cases hp : P <;> by_cases hq : Q <;> simp_all [mark]

theorem sumTo_zero (n : Nat) : sumTo (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumTo,ih]

theorem sumTo_add (f g : Nat → Int) (n : Nat) :
    sumTo (fun i => f i + g i) n = sumTo f n + sumTo g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumTo,ih]; omega

theorem sumTo_congr {f g : Nat → Int} (n : Nat)
    (h : ∀ i, i < n → f i = g i) : sumTo f n = sumTo g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumTo]
    rw [ih (fun i hi => h i (by omega)),h n (by omega)]

def intervalCount (n : Nat) (lo hi : Int) : Int :=
  max 0 (min (n : Int) (hi+1) - max 0 lo)

theorem sumTo_interval (n : Nat) (lo hi : Int) :
    sumTo (fun i => mark (lo ≤ (i : Int) ∧ (i : Int) ≤ hi)) n =
      intervalCount n lo hi := by
  induction n with
  | zero => simp [sumTo,intervalCount]; omega
  | succ n ih =>
    simp only [sumTo,ih]
    unfold intervalCount mark
    split <;> omega

theorem sumTo_singleton (n k : Nat) (hk : k < n) :
    sumTo (fun i => mark (i = k)) n = 1 := by
  calc
    _ = sumTo (fun i => mark ((k : Int) ≤ i ∧ (i : Int) ≤ k)) n := by
      apply sumTo_congr
      intro i _
      apply mark_congr
      omega
    _ = intervalCount n k k := sumTo_interval n k k
    _ = 1 := by unfold intervalCount; omega

theorem sumTo_point_and (n k : Nat) (P : Prop) (hk : k < n) :
    sumTo (fun i => mark (i = k ∧ P)) n = mark P := by
  classical
  by_cases hp : P
  · calc
      _ = sumTo (fun i => mark (i = k)) n := by
        apply sumTo_congr
        intro i _
        apply mark_congr
        simp [hp]
      _ = 1 := sumTo_singleton n k hk
      _ = mark P := by simp [mark,hp]
  · calc
      _ = sumTo (fun _ => 0) n := by
        apply sumTo_congr
        intro i _
        simp [mark,hp]
      _ = 0 := sumTo_zero n
      _ = mark P := by simp [mark,hp]

end LuRazCounting
