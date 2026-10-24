import SixRowLargeEnumeration
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

theorem NF7.cut_conditions (q : Nat) (hq : 4≤q) (z : NF7) (hz : z.Valid q) :
    z.eval q (4*q-1) ∧ z.eval q (q+2) ∧
    (z.eval q (2*q+1) → z.eval q (2*q)) := by
  cases z with
  | old z =>
    have hzv := hz.1
    have hzk := hz.2
    cases z <;> simp only [NF123.Valid,Keep7,P] at hzv hzk <;>
      simp only [NF7.eval,NF123.eval,NF123.body,NF23.eval,LRow,LNormal,TwoPiece,I,beta] <;>
      repeat first | omega | (simp_all <;> omega) | split
  | creg t =>
    simp only [NF7.Valid,P] at hz
    simp only [NF7.eval,NF6.eval,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | cex | rex | point =>
    simp only [NF7.eval,NF6.eval,I]
    simp_all <;> omega
  | right c =>
    have hc : 3*q+2≤c ∧ c≤4*q-1 := hz
    simp only [NF7.eval,I]
    simp_all <;> omega

theorem core7_cut_conditions (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : Generated q R) (hc : Core123 R) :
    R (4*q-1) ∧ R (q+2) ∧ (R (2*q+1) → R (2*q)) := by
  obtain ⟨z,hz,he⟩ := core7_normal q hq R hg hc
  have hh := NF7.cut_conditions q hq z hz
  exact ⟨(he _).mpr hh.1,(he _).mpr hh.2.1,fun h=>(he _).mpr (hh.2.2 ((he _).mp h))⟩

theorem old7_shape (q : Nat) (hq : 4≤q) (R : Nat→Prop)
    (hg : LuRazThreeRow.Generated q R) (hc : Core123 R) :
    (R (2*q+1) → R (2*q+2)) ∧ (R (2*q+2) → R (3*q+1)) := by
  rcases (LuRazThreeRow.core123_exhaustive q hq R).mp ⟨hg,hc⟩ with ⟨z,hz,he⟩|⟨z,he⟩
  · have hp : (z.eval q (2*q+1) → z.eval q (2*q+2)) ∧
        (z.eval q (2*q+2) → z.eval q (3*q+1)) := by
      have hzv := hz.1
      have hzc := hz.2
      cases z <;> simp only [NF123.Valid,LuRazThreeRow.Cut123,P] at hzv hzc <;>
        simp only [NF123.eval,NF123.body,NF23.eval,LRow,LNormal,TwoPiece,I,beta] <;>
        repeat first | omega | (simp_all <;> omega) | split
    exact ⟨fun h=>(he _).mpr (hp.1 ((he _).mp h)),fun h=>(he _).mpr (hp.2 ((he _).mp h))⟩
  · have hp : (z.eval q (2*q+1) → z.eval q (2*q+2)) ∧
        (z.eval q (2*q+2) → z.eval q (3*q+1)) := by
      cases z <;> simp only [LuRazThreeRow.Fresh123.eval,LuRazThreeRow.EPrime,ARow,CRow,I] <;> omega
    exact ⟨fun h=>(he _).mpr (hp.1 ((he _).mp h)),fun h=>(he _).mpr (hp.2 ((he _).mp h))⟩

theorem fresh7_not_v (q : Nat) (hq : 4≤q) (z : NF7) (hz : z.Valid q) (hf : z.Fresh) :
    ¬LuRazThreeRow.Generated q (z.eval q) := by
  intro hg
  have hh := old7_shape q hq _ hg (z.core q hq hz)
  have h1 := hh.1
  have h2 := hh.2
  cases z <;> simp only [NF7.Fresh,NF7.Valid,P] at hf hz <;>
    simp only [NF7.eval,NF6.eval,I,beta] at h1 h2 <;>
    repeat first | omega | (simp_all <;> omega) | split at h1 <;> split at h2

theorem keep7_cut123 (q : Nat) (z : NF123) (hk : Keep7 q z) : LuRazThreeRow.Cut123 q z := by
  cases z <;> simp_all [Keep7,LuRazThreeRow.Cut123]
end LuRazSixRowClosure
