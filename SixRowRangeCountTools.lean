import SixRowDifferenceCountsDefs
import SixRowDifferenceLists
import VariantSpectrumTools

namespace LuRazSixRowSpectrum
open LuRazClosure LuRazEnumeration LuRazThreeRow LuRazSixRowClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable
noncomputable section

theorem indicator_as_bool (P : Prop) [Decidable P] :
    (((if P then (1:Int) else 0)+1≤0) ∨ 1≤(if P then (1:Int) else 0)) ↔ P := by
  by_cases hp : P <;> simp [hp]

def lowerRangeCount (s n e : Nat) (shift last : Int) (fixed : Prop) : Int :=
  if fixed then (n:Int) else if (e:Int)≤last then
    max 0 (min ((s:Int)+(n:Int)-1) ((e:Int)-shift)-(s:Int)+1) else 0

def upperRangeCount (s n e : Nat) (first : Int) (fixed : Prop) : Int :=
  if fixed then (n:Int) else if first≤(e:Int) then
    max 0 (((s:Int)+(n:Int)-1)-max (s:Int) (e:Int)+1) else 0

theorem count_lower_range (s n e : Nat) (f : Nat → Nat → Prop)
    (shift last : Int) (fixed : Prop)
    (h : ∀a∈List.range' s n,
      f a e ↔ fixed ∨ ((a:Int)+shift≤(e:Int) ∧ (e:Int)≤last)) :
    CountAt ((List.range' s n).map f) e=lowerRangeCount s n e shift last fixed := by
  have hm : ∀a∈List.range' s n,
      f a e ↔ fixed ∨ ((e:Int)≤last ∧ 0≤(a:Int) ∧ (a:Int)≤(e:Int)-shift) := by
    intro a ha
    rw [h a ha]
    by_cases hp : fixed <;> simp [hp] <;> omega
  rw [count_line s n f e fixed ((e:Int)≤last) 0 ((e:Int)-shift) hm]
  have hs : max (s:Int) 0=(s:Int) := by omega
  simp only [lineTally,lowerRangeCount,hs]

theorem count_upper_range (s n e : Nat) (f : Nat → Nat → Prop)
    (first : Int) (fixed : Prop)
    (h : ∀a∈List.range' s n,
      f a e ↔ fixed ∨ (first≤(e:Int) ∧ (e:Int)≤(a:Int))) :
    CountAt ((List.range' s n).map f) e=upperRangeCount s n e first fixed := by
  have hm : ∀a∈List.range' s n,
      f a e ↔ fixed ∨ (first≤(e:Int) ∧ (e:Int)≤(a:Int) ∧
        (a:Int)≤(s:Int)+(n:Int)-1) := by
    intro a ha
    have hb := (range_mem a s n).mp ha
    rw [h a ha]
    by_cases hp : fixed <;> simp [hp] <;> omega
  rw [count_line s n f e fixed (first≤(e:Int)) (e:Int) ((s:Int)+(n:Int)-1) hm]
  simp [lineTally,upperRangeCount]

end
end LuRazSixRowSpectrum

