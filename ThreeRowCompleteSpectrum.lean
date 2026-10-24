import VariantTailAggregate
import VariantFiniteDifference
import ThreeRowSpectrumArithmetic
import ThreeRowSpectrumOldRelation
import ThreeRowSpectrumExtrema
import ThreeRowWeightTools

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

/-- Frequency in a duplicate-free enumeration of the actual modified closure. -/
noncomputable def variantFrequency (q e : Nat) : Int := CountAt (VariantClosureMembers q) e

/-- The entire frequency spectrum, for every coordinate and every q ≥ 4. -/
theorem variant_frequency_spectrum (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    2*variantFrequency q e=spectrumPolynomial2 (q:Int) (e:Int) := by
  unfold variantFrequency
  by_cases hc : e≤4
  · obtain ⟨l,hn,hle,_,hf⟩ := core_frequency_exact q e hq ⟨he,hc⟩
    have hp : (VariantClosureMembers q).Perm l := by
      apply (List.perm_ext_iff_of_nodup (variant_closure_members_nodup q hq) hn).mpr
      intro R
      rw [variant_closure_members_exact q hq R,hle R]
    rw [count_at_perm _ _ hp e]
    have hcases : e=1 ∨ e=2 ∨ e=3 ∨ e=4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;>
      simpa [NewCoreFrequency2,spectrumPolynomial2] using hf
  · rw [variant_closure_count_delta q e hq,delta_raw_tail q e hq (by omega) hen,
      tail_delta_arithmetic (q:Int) (e:Int) (by omega) (by omega) (by omega),Int.mul_add,
      LuRazClosure.SourcePieces.elementFrequency_spectrum q e hq he hen]
    exact spectrum_old_relation (q:Int) (e:Int) (by omega) (by omega) (by omega)

/-- The spectrum counts actual finite subsets containing the specified coordinate. -/
theorem variant_frequency_finite (q e : Nat) (hq : 4≤q) (he : 1≤e) (hen : e≤4*q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ T ⟨e-1,by omega⟩) ∧
      2*(l.length : Int)=spectrumPolynomial2 (q:Int) (e:Int) := by
  classical
  let f := (VariantClosureMembers q).filter (fun R => decide (R e))
  have hfn : f.Nodup := List.Nodup.sublist List.filter_sublist (variant_closure_members_nodup q hq)
  have hfe : ∀ R, R∈f ↔ Generated q R ∧ R e := by
    intro R
    simp only [f,List.mem_filter,decide_eq_true_eq,variant_closure_members_exact q hq R]
  have ht := transfer_enumeration q hq (fun R => R e) f hfn hfe
  refine ⟨f.map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (lift_at q T e ⟨he,hen⟩))
  · simpa only [List.length_map,variantFrequency,CountAt,f] using variant_frequency_spectrum q e hq he hen

theorem variant_frequency_order (q a b : Nat) (hq : 4≤q)
    (ha : 1≤a ∧ a≤4*q) (hb : 1≤b ∧ b≤4*q) :
    variantFrequency q a<variantFrequency q b ↔
      spectrumPolynomial2 (q:Int) (a:Int)<spectrumPolynomial2 (q:Int) (b:Int) := by
  have hfa := variant_frequency_spectrum q a hq ha.1 ha.2
  have hfb := variant_frequency_spectrum q b hq hb.1 hb.2
  omega

theorem variant_frequency_maximum_threshold (q : Nat) (hq : 4≤q) :
    (∀ e : Nat, 1≤e → e≤4*q → e≠1 → variantFrequency q e<variantFrequency q 1) ↔ 9≤q := by
  constructor
  · intro h
    have ht := (spectrum_maximum_threshold (q:Int) (by omega)).mp
    apply Int.ofNat_le.mp
    apply ht
    intro e he hen hne
    have heq : (e.toNat:Int)=e := by omega
    have hcomp := (variant_frequency_order q e.toNat 1 hq (by omega) (by omega)).mp
      (h e.toNat (by omega) (by omega) (by omega))
    simpa only [heq,Int.natCast_one] using hcomp
  · intro h e he hen hne
    apply (variant_frequency_order q e 1 hq ⟨he,hen⟩ (by omega)).mpr
    have hcomp := spectrum_max_strict (q:Int) (e:Int) (by omega) (by omega) (by omega) (by omega)
    simp only [Int.natCast_one]
    rw [spectrum_at_one (q:Int) (by omega)]
    exact hcomp

theorem variant_frequency_minimum_threshold (q : Nat) (hq : 4≤q) :
    (∀ e : Nat, 1≤e → e≤4*q → e≠3*q → variantFrequency q (3*q)<variantFrequency q e) ↔ 6≤q := by
  have h3 : ((3*q:Nat):Int)=3*(q:Int) := by omega
  constructor
  · intro h
    have ht := (spectrum_minimum_threshold (q:Int) (by omega)).mp
    apply Int.ofNat_le.mp
    apply ht
    intro e he hen hne
    have heq : (e.toNat:Int)=e := by omega
    have hcomp := (variant_frequency_order q (3*q) e.toNat hq (by omega) (by omega)).mp
      (h e.toNat (by omega) (by omega) (by omega))
    simpa only [heq,h3] using hcomp
  · intro h e he hen hne
    apply (variant_frequency_order q (3*q) e hq (by omega) ⟨he,hen⟩).mpr
    rw [h3,spectrum_at_threeq (q:Int) (by omega)]
    exact spectrum_min_strict (q:Int) (e:Int) (by omega) (by omega) (by omega) (by omega)

noncomputable def variantTotalWeight (q : Nat) : Int := familyTotalWeight q (VariantClosureMembers q)

/-- Total set cardinalities in the actual closure, derived by double counting incidences. -/
theorem variant_total_weight_formula (q : Nat) (hq : 4≤q) :
    2*variantTotalWeight q=69*(q:Int)*(q:Int)*(q:Int)+85*(q:Int)*(q:Int)-88*(q:Int)-86 := by
  exact family_weight_formula_of_spectrum q (VariantClosureMembers q) hq
    (fun e he hen => variant_frequency_spectrum q e hq he hen)

end LuRazThreeRow
