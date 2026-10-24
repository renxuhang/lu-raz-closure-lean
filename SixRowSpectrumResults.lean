import SixRowCompleteSpectrum
import SixRowSpectrumSharpBounds
import SixRowWeightTools
import SixRowWeightBridge

namespace LuRazSixRowSpectrum

open LuRazThreeRow LuRazSixRowClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The cardinality of the actual duplicate-free nonempty B-closure. -/
noncomputable def sixRowCardinality (q : Nat) : Int :=
  (LuRazSixRowClosure.ClosureMembers q).length

theorem six_row_cardinality_formula (q : Nat) (hq : 4≤q) :
    2*sixRowCardinality q=23*(q:Int)*(q:Int)+7*(q:Int)+2 :=
  LuRazSixRowClosure.closure_members_length q hq

theorem six_row_frequency_minimum_value (q : Nat) (hq : 4≤q) :
    2*sixRowFrequency q (3*q)=15*(q:Int)*(q:Int)+7*(q:Int)-14 := by
  have hs := six_row_frequency_spectrum q (3*q) hq (by omega) (by omega)
  have hc : ((3*q:Nat):Int)=3*(q:Int) := by omega
  rw [hc,spectrum_at_threeq (q:Int) (by omega)] at hs
  exact hs

theorem six_row_frequency_minimum_exact (q e : Nat) (hq : 4≤q)
    (he : 1≤e) (hen : e≤4*q) :
    sixRowFrequency q (3*q)≤sixRowFrequency q e ∧
      (sixRowFrequency q e=sixRowFrequency q (3*q) ↔ e=3*q) := by
  have hs := six_row_frequency_spectrum q e hq he hen
  have hm := six_row_frequency_minimum_value q hq
  have hp := spectrum_min_exact (q:Int) (e:Int) (by omega) (by omega) (by omega)
  omega

theorem six_row_frequency_maximum_value (q : Nat) (hq : 4≤q) :
    2*sixRowFrequency q (q+2)=19*(q:Int)*(q:Int)+(q:Int)+2 := by
  have hs := six_row_frequency_spectrum q (q+2) hq (by omega) (by omega)
  have hc : ((q+2:Nat):Int)=(q:Int)+2 := by omega
  rw [hc,spectrum_at_qplus2 (q:Int) (by omega)] at hs
  exact hs

theorem six_row_frequency_one_gap (q : Nat) (hq : 4≤q) :
    sixRowFrequency q (q+2)=sixRowFrequency q 1+1 := by
  have hs := six_row_frequency_spectrum q 1 hq (by omega) (by omega)
  change 2*sixRowFrequency q 1=spectrumPolynomial2 (q:Int) 1 at hs
  have hp : spectrumPolynomial2 (q:Int) 1=19*(q:Int)*(q:Int)+(q:Int) := by
    simp [spectrumPolynomial2]
  rw [hp] at hs
  have hm := six_row_frequency_maximum_value q hq
  omega

theorem six_row_frequency_maximum_exact (q e : Nat) (hq : 5≤q)
    (he : 1≤e) (hen : e≤4*q) :
    sixRowFrequency q e≤sixRowFrequency q (q+2) ∧
      (sixRowFrequency q e=sixRowFrequency q (q+2) ↔ e=q+2) := by
  have hs := six_row_frequency_spectrum q e (by omega) he hen
  have hm := six_row_frequency_maximum_value q (by omega)
  have hp := spectrum_max_exact (q:Int) (e:Int) (by omega) (by omega) (by omega)
  omega

theorem six_row_frequency_q4_maximum (e : Nat) (he : 1≤e) (hen : e≤16) :
    sixRowFrequency 4 e≤155 ∧ (sixRowFrequency 4 e=155 ↔ e=6 ∨ e=15) := by
  have hs := six_row_frequency_spectrum 4 e (by decide) he hen
  change 2*sixRowFrequency 4 e=spectrumPolynomial2 4 (e:Int) at hs
  have hp := spectrum_q4_max (e:Int) (by omega) (by omega)
  omega

theorem six_row_frequency_maximum_bound (q e : Nat) (hq : 4≤q)
    (he : 1≤e) (hen : e≤4*q) :
    sixRowFrequency q e≤sixRowFrequency q (q+2) := by
  have hs := six_row_frequency_spectrum q e hq he hen
  have hm := six_row_frequency_maximum_value q hq
  have hp := spectrum_max_bound (q:Int) (e:Int) (by omega) (by omega) (by omega)
  omega

theorem six_row_frequency_maximum_threshold (q : Nat) (hq : 4≤q) :
    (∀ e : Nat, 1≤e → e≤4*q → e≠q+2 →
      sixRowFrequency q e<sixRowFrequency q (q+2)) ↔ 5≤q := by
  constructor
  · intro h
    by_cases h5 : 5≤q
    · exact h5
    have h4 : q=4 := by omega
    subst q
    have ht := h 15 (by decide) (by decide) (by decide)
    change sixRowFrequency 4 15<sixRowFrequency 4 6 at ht
    have h6 := (six_row_frequency_q4_maximum 6 (by decide) (by decide)).2.mpr (Or.inl rfl)
    have h15 := (six_row_frequency_q4_maximum 15 (by decide) (by decide)).2.mpr (Or.inr rfl)
    omega
  · intro h5 e he hen hne
    have hm := six_row_frequency_maximum_exact q e h5 he hen
    omega

theorem six_row_frequency_uniform_lower (q e : Nat) (hq : 4≤q)
    (he : 1≤e) (hen : e≤4*q) :
    127*sixRowCardinality q≤199*sixRowFrequency q e := by
  have hs := six_row_frequency_spectrum q e hq he hen
  have hc := six_row_cardinality_formula q hq
  have hp := spectrum_uniform_lower (q:Int) (e:Int) (by omega) (by omega) (by omega)
  omega

theorem six_row_frequency_strict_half (q e : Nat) (hq : 4≤q)
    (he : 1≤e) (hen : e≤4*q) :
    sixRowCardinality q<2*sixRowFrequency q e := by
  have hs := six_row_frequency_spectrum q e hq he hen
  have hc := six_row_cardinality_formula q hq
  have hp := spectrum_strict_half (q:Int) (e:Int) (by omega) (by omega) (by omega)
  omega

theorem six_row_frequency_strict_upper (q e : Nat) (hq : 4≤q)
    (he : 1≤e) (hen : e≤4*q) :
    23*sixRowFrequency q e<19*sixRowCardinality q := by
  have hs := six_row_frequency_spectrum q e hq he hen
  have hc := six_row_cardinality_formula q hq
  have hp := spectrum_strict_upper (q:Int) (e:Int) (by omega) (by omega) (by omega)
  omega

/-- The sharp uniform rational lower frequency bound for the actual closure. -/
theorem six_row_frequency_uniform_lower_sharp (a b : Int) (hb : 0<b) :
    (∀ q e : Nat, 4≤q → 1≤e → e≤4*q →
      a*sixRowCardinality q≤b*sixRowFrequency q e) ↔ 199*a≤127*b := by
  constructor
  · intro h
    have h4 := h 4 12 (by decide) (by decide) (by decide)
    have hc := six_row_cardinality_formula 4 (by decide)
    have hf := six_row_frequency_minimum_value 4 (by decide)
    change 2*sixRowFrequency 4 12=254 at hf
    have hc4 : sixRowCardinality 4=199 := by omega
    have hf4 : sixRowFrequency 4 12=127 := by omega
    simpa only [hc4,hf4,Int.mul_comm] using h4
  · intro hab q e hq he hen
    have hs := six_row_frequency_spectrum q e hq he hen
    have hc := six_row_cardinality_formula q hq
    have hp := (spectrum_uniform_lower_sharp a b hb).mpr hab
      (q:Int) (e:Int) (by omega) (by omega) (by omega)
    rw [←hs,←hc] at hp
    grind

theorem six_row_frequency_uniform_lower_equality (q e : Nat) (hq : 4≤q)
    (he : 1≤e) (hen : e≤4*q) :
    127*sixRowCardinality q=199*sixRowFrequency q e ↔ q=4 ∧ e=12 := by
  constructor
  · intro h
    have hs := six_row_frequency_spectrum q e hq he hen
    have hc := six_row_cardinality_formula q hq
    have hm := spectrum_min_exact (q:Int) (e:Int) (by omega) (by omega) (by omega)
    have hb := RatioArithmetic.minimum_uniform_bound (q:Int) (by omega)
    have heq : 127*(23*(q:Int)*(q:Int)+7*(q:Int)+2)=
        199*(15*(q:Int)*(q:Int)+7*(q:Int)-14) := by omega
    have h4 := (RatioArithmetic.minimum_uniform_equality (q:Int) (by omega)).mp heq
    have hp := hm.2.mp (show spectrumPolynomial2 (q:Int) (e:Int)=
      15*(q:Int)*(q:Int)+7*(q:Int)-14 by omega)
    omega
  · rintro ⟨rfl,rfl⟩
    have hc := six_row_cardinality_formula 4 (by decide)
    have hf := six_row_frequency_minimum_value 4 (by decide)
    change 2*sixRowFrequency 4 12=254 at hf
    omega

/-- The strongest possible minimum-element abundance within this parameter family occurs at q=13. -/
theorem six_row_minimum_ratio_parameter_maximum (q : Nat) (hq : 4≤q) :
    995*sixRowFrequency q (3*q)≤653*sixRowCardinality q ∧
      (995*sixRowFrequency q (3*q)=653*sixRowCardinality q ↔ q=13) := by
  have hf := six_row_frequency_minimum_value q hq
  have hc := six_row_cardinality_formula q hq
  have hp := RatioArithmetic.minimum_parameter_maximum (q:Int) (by omega)
  omega

theorem six_row_frequency_fifteen_twenty_three_threshold (q : Nat) (hq : 4≤q) :
    (∀ e : Nat, 1≤e → e≤4*q →
      15*sixRowCardinality q<23*sixRowFrequency q e) ↔ 7≤q := by
  constructor
  · intro h
    have hm := h (3*q) (by omega) (by omega)
    have hf := six_row_frequency_minimum_value q hq
    have hc := six_row_cardinality_formula q hq
    have hp : 15*(23*(q:Int)*(q:Int)+7*(q:Int)+2)<
        23*(15*(q:Int)*(q:Int)+7*(q:Int)-14) := by omega
    have ht := (RatioArithmetic.minimum_fifteen_twenty_three_threshold (q:Int)).mp hp
    omega
  · intro h7 e he hen
    have hs := six_row_frequency_spectrum q e hq he hen
    have hc := six_row_cardinality_formula q hq
    have hp := (spectrum_fifteen_twenty_three_threshold (q:Int) (by omega)).mpr
      (by omega) (e:Int) (by omega) (by omega)
    omega

theorem six_row_frequency_minimum_tail_sharp (a b : Int) (Q : Nat)
    (hb : 0<b) (ha : 15*b<23*a) (hQ : 4≤Q) :
    ∃ q : Nat, Q≤q ∧ b*sixRowFrequency q (3*q)<a*sixRowCardinality q := by
  obtain ⟨q,hq,hr⟩ := spectrum_minimum_tail_sharp a b (Q:Int) hb ha (by omega)
  let n := q.toNat
  have hnq : (n:Int)=q := by dsimp [n]; omega
  have hn : Q≤n := by omega
  have hs := six_row_frequency_spectrum n (3*n) (by omega) (by omega) (by omega)
  have hc := six_row_cardinality_formula n (by omega)
  have h3 : ((3*n:Nat):Int)=3*q := by omega
  rw [hnq,h3] at hs
  rw [hnq] at hc
  rw [←hs,←hc] at hr
  refine ⟨n,hn,?_⟩
  grind

theorem six_row_frequency_maximum_tail_sharp (a b : Int) (Q : Nat)
    (ha0 : 0≤a) (hb : 0<b) (ha : 23*a<19*b) (hQ : 4≤Q) :
    ∃ q : Nat, Q≤q ∧ a*sixRowCardinality q<b*sixRowFrequency q (q+2) := by
  obtain ⟨q,hq,hr⟩ := spectrum_maximum_tail_sharp a b (Q:Int) ha0 hb ha (by omega)
  let n := q.toNat
  have hnq : (n:Int)=q := by dsimp [n]; omega
  have hn : Q≤n := by omega
  have hs := six_row_frequency_spectrum n (n+2) (by omega) (by omega) (by omega)
  have hc := six_row_cardinality_formula n (by omega)
  have h2 : ((n+2:Nat):Int)=q+2 := by omega
  rw [hnq,h2] at hs
  rw [hnq] at hc
  rw [←hs,←hc] at hr
  refine ⟨n,hn,?_⟩
  grind

/-- The finite source has precisely the same all-coordinate sharp abundance bound. -/
theorem six_row_finite_frequency_bounds (q : Nat) (e : Fin (4*q)) (hq : 4≤q) :
    127*((FinClosureMembers q).length : Int)≤199*sixRowFinFrequency q e ∧
      23*sixRowFinFrequency q e<19*((FinClosureMembers q).length : Int) := by
  have hl := six_row_frequency_uniform_lower q (e.val+1) hq (by omega) (by omega)
  have hu := six_row_frequency_strict_upper q (e.val+1) hq (by omega) (by omega)
  have hc : ((FinClosureMembers q).length : Int)=sixRowCardinality q := by
    simp only [FinClosureMembers,List.length_map,sixRowCardinality]
  rw [six_row_fin_frequency_eq,hc]
  exact ⟨hl,hu⟩

theorem six_row_finite_frequency_minimum_exact (q : Nat) (e : Fin (4*q)) (hq : 4≤q) :
    sixRowFrequency q (3*q)≤sixRowFinFrequency q e ∧
      (sixRowFinFrequency q e=sixRowFrequency q (3*q) ↔ e.val+1=3*q) := by
  rw [six_row_fin_frequency_eq]
  exact six_row_frequency_minimum_exact q (e.val+1) hq (by omega) (by omega)

theorem six_row_finite_frequency_maximum_exact (q : Nat) (e : Fin (4*q)) (hq : 5≤q) :
    sixRowFinFrequency q e≤sixRowFrequency q (q+2) ∧
      (sixRowFinFrequency q e=sixRowFrequency q (q+2) ↔ e.val+1=q+2) := by
  rw [six_row_fin_frequency_eq]
  exact six_row_frequency_maximum_exact q (e.val+1) hq (by omega) (by omega)

theorem six_row_total_weight_formula (q : Nat) (hq : 4≤q) :
    2*sixRowTotalWeight q=
      69*(q:Int)*(q:Int)*(q:Int)+15*(q:Int)*(q:Int)-18*(q:Int)-34 := by
  exact family_weight_formula_of_spectrum q (LuRazSixRowClosure.ClosureMembers q) hq
    (fun e he hen => six_row_frequency_spectrum q e hq he hen)

theorem six_row_finite_total_weight_formula (q : Nat) (hq : 4≤q) :
    2*sixRowFiniteTotalWeight q=
      69*(q:Int)*(q:Int)*(q:Int)+15*(q:Int)*(q:Int)-18*(q:Int)-34 := by
  rw [six_row_finite_total_weight_eq]
  exact six_row_total_weight_formula q hq

/-- The exact average-size deficit, expressed without division. -/
theorem six_row_mean_size_deficit (q : Nat) (hq : 4≤q) :
    3*(q:Int)*sixRowCardinality q-sixRowTotalWeight q=
      3*(q:Int)*(q:Int)+12*(q:Int)+17 := by
  have hc := six_row_cardinality_formula q hq
  have hw := six_row_total_weight_formula q hq
  have hp := congrArg (fun z : Int => 3*(q:Int)*z) hc
  grind

theorem six_row_mean_size_below_threeq (q : Nat) (hq : 4≤q) :
    sixRowTotalWeight q<3*(q:Int)*sixRowCardinality q := by
  have hd := six_row_mean_size_deficit q hq
  have h : 0≤(q:Int)*(q:Int) := Int.mul_nonneg (by omega) (by omega)
  grind

theorem six_row_total_weight_improvement (q : Nat) (hq : 4≤q) :
    variantTotalWeight q-sixRowTotalWeight q=
      35*(q:Int)*(q:Int)-35*(q:Int)-26 := by
  have ho := variant_total_weight_formula q hq
  have hn := six_row_total_weight_formula q hq
  grind

#print axioms six_row_cardinality_formula
#print axioms six_row_frequency_minimum_value
#print axioms six_row_frequency_minimum_exact
#print axioms six_row_frequency_maximum_value
#print axioms six_row_frequency_one_gap
#print axioms six_row_frequency_maximum_exact
#print axioms six_row_frequency_q4_maximum
#print axioms six_row_frequency_maximum_bound
#print axioms six_row_frequency_maximum_threshold
#print axioms six_row_frequency_uniform_lower
#print axioms six_row_frequency_strict_half
#print axioms six_row_frequency_strict_upper
#print axioms six_row_frequency_uniform_lower_sharp
#print axioms six_row_frequency_uniform_lower_equality
#print axioms six_row_minimum_ratio_parameter_maximum
#print axioms six_row_frequency_fifteen_twenty_three_threshold
#print axioms six_row_frequency_minimum_tail_sharp
#print axioms six_row_frequency_maximum_tail_sharp
#print axioms six_row_finite_frequency_bounds
#print axioms six_row_finite_frequency_minimum_exact
#print axioms six_row_finite_frequency_maximum_exact
#print axioms six_row_total_weight_formula
#print axioms six_row_finite_total_weight_formula
#print axioms six_row_mean_size_deficit
#print axioms six_row_mean_size_below_threeq
#print axioms six_row_total_weight_improvement

end LuRazSixRowSpectrum
