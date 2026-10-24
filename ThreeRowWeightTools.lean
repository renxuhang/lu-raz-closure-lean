import VariantCoreFrequencyParts
import ThreeRowSpectrumSum

namespace LuRazThreeRow
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
noncomputable section

/-- Cardinality of a predicate on the one-based ground set {1,...,4q}. -/
def familyMemberSize (q : Nat) (R : Nat → Prop) : Int :=
  tally (List.range' 1 (4*q)) R

/-- Total cardinality, summed over the members of an arbitrary family list. -/
def familyTotalWeight (q : Nat) (l : List (Nat → Prop)) : Int :=
  (l.map (familyMemberSize q)).sum

theorem family_weight_double_count (q : Nat) (l : List (Nat → Prop)) :
    familyTotalWeight q l=
      ((List.range' 1 (4*q)).map (CountAt l)).sum := by
  unfold familyTotalWeight familyMemberSize CountAt
  change (l.map (fun R => tally (List.range' 1 (4*q)) R)).sum=
    ((List.range' 1 (4*q)).map (fun e => tally l (fun R => R e))).sum
  simp only [tally_as_sum]
  exact sum_swap l (List.range' 1 (4*q)) (fun R e => LuRazCounting.mark (R e))

/-- The total-weight formula follows from any established actual frequency bridge. -/
theorem family_weight_formula_of_spectrum (q : Nat) (l : List (Nat → Prop))
    (hq : 4≤q)
    (hs : ∀ e : Nat, 1≤e → e≤4*q →
      2*CountAt l e=spectrumPolynomial2 (q:Int) (e:Int)) :
    2*familyTotalWeight q l=
      69*(q:Int)*(q:Int)*(q:Int)+85*(q:Int)*(q:Int)-88*(q:Int)-86 := by
  calc
    2*familyTotalWeight q l=
        ((List.range' 1 (4*q)).map (fun e => 2*CountAt l e)).sum := by
      rw [family_weight_double_count,sum_scale]
    _=((List.range' 1 (4*q)).map
        (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro e he
      have hb := (LuRazEnumeration.range_mem e 1 (4*q)).mp he
      exact hs e (by omega) (by omega)
    _=69*(q:Int)*(q:Int)*(q:Int)+85*(q:Int)*(q:Int)-88*(q:Int)-86 :=
      spectrum_polynomial_sum q hq

#print axioms family_weight_double_count
#print axioms family_weight_formula_of_spectrum
end
end LuRazThreeRow
