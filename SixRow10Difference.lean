import SixRow10Exact
import SixRowDifferencePredicates
namespace LuRazSixRowClosure
open LuRazClosure Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem old10_last (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : LuRazThreeRow.Generated q R) (hc : Core24 R) : R (4*q) → R (4*q-1) := by
  have hold := (LuRazThreeRow.no_three_unchanged q hq R hc.2.2.1).mp hg
  obtain ⟨z,he⟩ := (core24_closure_exact q hq R).mp ⟨hold,hc⟩
  have hh : z.eval q (4*q) → z.eval q (4*q-1) := by
    cases z <;> simp only [NF24.eval,K1Row,K2Row,DRow,BRow,I] <;> simp_all <;> omega
  exact fun h=>(he _).mpr (hh ((he _).mp h))
theorem new10_last (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : Generated q R) (hc : Core24 R) : R (4*q-1) → R (4*q) := by
  obtain ⟨z,he⟩ := (Low.core10_exhaustive q hq R).mp ⟨hg,hc⟩
  have hh : z.eval q (4*q-1) → z.eval q (4*q) := by
    cases z <;> simp only [Low.NF10.eval,Low.K0,Low.K1,Low.K2,BRow,I] <;> simp_all <;> omega
  exact fun h=>(he _).mpr (hh ((he _).mp h))

theorem old10_partition (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : LuRazThreeRow.Generated q R) (hc : Core24 R) : Generated q R ∨ RemovedAt q 10 R := by
  have hold := (LuRazThreeRow.no_three_unchanged q hq R hc.2.2.1).mp hg
  obtain ⟨z,he⟩ := (core24_closure_exact q hq R).mp ⟨hold,hc⟩
  cases z with
  | k1 => exact Or.inl (generated_congr q (Low.NF10.generated q hq .k1) (fun e=>(he e).symm))
  | k2 =>
    right; refine ⟨.r10 (2*q+3),Or.inr rfl,rfl,?_⟩
    intro e; refine Iff.trans ?_ (he e).symm
    simp only [RemovedForm.eval,NF24.eval,K2Row,I,or_assoc]
  | joinK =>
    right; refine ⟨.r10 (2*q+2),Or.inl rfl,rfl,?_⟩
    intro e; refine Iff.trans ?_ (he e).symm
    simp only [RemovedForm.eval,NF24.eval,K1Row,K2Row,I]
    omega
  | fill1 => exact Or.inl (generated_congr q (Low.NF10.generated q hq .fill1) (fun e=>(he e).symm))
  | fill2 =>
    left; apply generated_congr q (Low.NF10.generated q hq .fill2)
    intro e; refine Iff.trans ?_ (he e).symm
    simp only [Low.NF10.eval,Low.K2,NF24.eval,K2Row,BRow,I]
    omega
  | dBig =>
    left; apply generated_congr q (Low.NF10.generated q hq .dBig)
    intro e; refine Iff.trans ?_ (he e).symm
    simp only [Low.NF10.eval,Low.K0,NF24.eval,K1Row,DRow,BRow,I]
    omega

theorem removed10_old_generated (q : Nat) (hq : 4≤q) (R : Nat→Prop) (h : RemovedAt q 10 R) :
    LuRazThreeRow.Generated q R := by
  obtain ⟨f,hf,ht,he⟩ := h
  cases f <;> simp only [RemovedForm.core] at ht
  case r10 t =>
    have ht : t=2*q+2 ∨ t=2*q+3 := hf
    rcases ht with rfl|rfl
    · have hz := NF24.core q hq .joinK
      have hv := (LuRazThreeRow.no_three_unchanged q hq _ hz.2.2.1).mpr (NF24.generated q hq .joinK)
      apply LuRazThreeRow.generated_congr q hv
      intro e; refine Iff.trans ?_ (he e)
      simp only [NF24.eval,K1Row,K2Row,RemovedForm.eval,I]; omega
    · have hz := NF24.core q hq .k2
      have hv := (LuRazThreeRow.no_three_unchanged q hq _ hz.2.2.1).mpr (NF24.generated q hq .k2)
      apply LuRazThreeRow.generated_congr q hv
      intro e; refine Iff.trans ?_ (he e)
      simp only [NF24.eval,K2Row,RemovedForm.eval,or_assoc]
  all_goals contradiction

theorem core10_removed_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 10 R) :
    (LuRazThreeRow.Generated q R ∧ ¬Generated q R) ↔ RemovedAt q 10 R := by
  have hc10 : Core24 R := by simpa [CoreMask,Core24] using hc
  constructor
  · rintro ⟨hg,hn⟩
    exact (old10_partition q hq R hg hc10).elim (fun h=>False.elim (hn h)) id
  · intro h
    refine ⟨removed10_old_generated q hq R h,?_⟩
    intro hg
    obtain ⟨f,hf,ht,he⟩ := h
    have hh := new10_last q hq R hg hc10
    cases f <;> simp only [RemovedForm.core] at ht
    case r10 t =>
      have ht : t=2*q+2 ∨ t=2*q+3 := hf
      have hlast : R (4*q-1) := (he _).mp (by simp only [RemovedForm.eval,I]; omega)
      have hn := (he (4*q)).mpr (hh hlast)
      simp only [RemovedForm.eval,I] at hn
      omega
    all_goals contradiction

theorem new10_partition (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : Generated q R) (hc : Core24 R) : LuRazThreeRow.Generated q R ∨ AddedAt q 10 R := by
  obtain ⟨z,he⟩ := (Low.core10_exhaustive q hq R).mp ⟨hg,hc⟩
  have old (w : NF24) : LuRazThreeRow.Generated q (w.eval q) :=
    (LuRazThreeRow.no_three_unchanged q hq _ (w.core q hq).2.2.1).mpr (w.generated q hq)
  cases z with
  | k1 => exact Or.inl (LuRazThreeRow.generated_congr q (old .k1) (fun e=>(he e).symm))
  | k2 =>
    right; refine ⟨.n10 (2*q+3),Or.inr (Or.inr rfl),rfl,?_⟩
    intro e; refine Iff.trans ?_ (he e).symm
    simp only [AddedForm.eval,Low.NF10.eval,Low.K2,I]; omega
  | joinK =>
    right; refine ⟨.n10 (2*q+2),Or.inr (Or.inl rfl),rfl,?_⟩
    intro e; refine Iff.trans ?_ (he e).symm
    simp only [AddedForm.eval,Low.NF10.eval,Low.K1,Low.K2,I]; omega
  | fill1 => exact Or.inl (LuRazThreeRow.generated_congr q (old .fill1) (fun e=>(he e).symm))
  | fill2 =>
    left; apply LuRazThreeRow.generated_congr q (old .fill2)
    intro e; refine Iff.trans ?_ (he e).symm
    simp only [NF24.eval,K2Row,Low.NF10.eval,Low.K2,BRow,I]; omega
  | dSmall =>
    right; refine ⟨.n10 (2*q+1),Or.inl rfl,rfl,?_⟩
    intro e; refine Iff.trans ?_ (he e).symm
    simp only [AddedForm.eval,Low.NF10.eval,Low.K0,I]; omega
  | dBig =>
    left; apply LuRazThreeRow.generated_congr q (old .dBig)
    intro e; refine Iff.trans ?_ (he e).symm
    simp only [NF24.eval,K1Row,DRow,Low.NF10.eval,Low.K0,BRow,I]; omega

theorem added10_new_generated (q : Nat) (hq : 4≤q) (R : Nat→Prop) (h : AddedAt q 10 R) : Generated q R := by
  obtain ⟨f,hf,ht,he⟩ := h
  cases f <;> simp only [AddedForm.core] at ht
  case n10 t =>
    have ht : t=2*q+1 ∨ t=2*q+2 ∨ t=2*q+3 := hf
    rcases ht with rfl|rfl|rfl
    · apply generated_congr q (Low.NF10.generated q hq .dSmall)
      intro e; refine Iff.trans ?_ (he e)
      simp only [Low.NF10.eval,Low.K0,AddedForm.eval,I]; omega
    · apply generated_congr q (Low.NF10.generated q hq .joinK)
      intro e; refine Iff.trans ?_ (he e)
      simp only [Low.NF10.eval,Low.K1,Low.K2,AddedForm.eval,I]; omega
    · apply generated_congr q (Low.NF10.generated q hq .k2)
      intro e; refine Iff.trans ?_ (he e)
      simp only [Low.NF10.eval,Low.K2,AddedForm.eval,I]; omega
  all_goals contradiction

theorem core10_added_at (q : Nat) (hq : 4≤q) (R : Nat→Prop) (hc : CoreMask 10 R) :
    (Generated q R ∧ ¬LuRazThreeRow.Generated q R) ↔ AddedAt q 10 R := by
  have hc10 : Core24 R := by simpa [CoreMask,Core24] using hc
  constructor
  · rintro ⟨hg,hn⟩
    exact (new10_partition q hq R hg hc10).elim (fun h=>False.elim (hn h)) id
  · intro h
    refine ⟨added10_new_generated q hq R h,?_⟩
    intro hg
    obtain ⟨f,hf,ht,he⟩ := h
    have hh := old10_last q hq R hg hc10
    cases f <;> simp only [AddedForm.core] at ht
    case n10 t =>
      have hlast : R (4*q) := (he _).mp (by simp [AddedForm.eval])
      have hn := (he (4*q-1)).mpr (hh hlast)
      simp only [AddedForm.eval,I] at hn
      omega
    all_goals contradiction
end LuRazSixRowClosure
