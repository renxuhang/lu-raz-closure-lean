import VariantSpectrumTools
import ThreeRowSpectrumDeltaDefs

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration LuRazCounting LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable
noncomputable section

theorem count_lower (s n : Nat) (f : Nat → Nat → Prop) (e : Nat) (P : Prop) (last : Int)
    (h : ∀ a∈List.range' s n, f a e ↔ P ∨ ((a:Int)≤(e:Int) ∧ (e:Int)≤last)) :
    CountAt ((List.range' s n).map f) e=
      tailLower (s:Int) ((s:Int)+(n:Int)-1) last (e:Int) P := by
  have h' : ∀ a∈List.range' s n,
      f a e ↔ P ∨ ((e:Int)≤last ∧ 0≤(a:Int) ∧ (a:Int)≤(e:Int)) := by
    intro a ha
    rw [h a ha]
    by_cases hp : P <;> simp [hp] <;> omega
  rw [count_line s n f e P ((e:Int)≤last) 0 (e:Int) h']
  unfold lineTally tailLower
  repeat first | omega | split

theorem count_upper (s n : Nat) (f : Nat → Nat → Prop) (e : Nat) (P : Prop) (first : Int)
    (h : ∀ a∈List.range' s n, f a e ↔ P ∨ (first≤(e:Int) ∧ (e:Int)≤(a:Int))) :
    CountAt ((List.range' s n).map f) e=
      tailUpper (s:Int) ((s:Int)+(n:Int)-1) first (e:Int) P := by
  have h' : ∀ a∈List.range' s n,
      f a e ↔ P ∨ (first≤(e:Int) ∧ (e:Int)≤(a:Int) ∧ (a:Int)≤(s:Int)+(n:Int)-1) := by
    intro a ha
    have hb := (range_mem a s n).mp ha
    rw [h a ha]
    by_cases hp : P <;> simp [hp] <;> omega
  rw [count_line s n f e P (first≤(e:Int)) (e:Int) ((s:Int)+(n:Int)-1) h']
  unfold lineTally tailUpper
  repeat first | omega | split

theorem tail_mark_eq (P Q : Prop) (h : P↔Q) : mark P=tailMark Q := by
  rw [mark_congr h]
  rfl

end
end LuRazThreeRow

