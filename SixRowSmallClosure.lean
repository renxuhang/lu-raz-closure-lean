import SixRowSmallParts
namespace LuRazSixRowClosure.Small
open LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem Normal.generated (q : Nat) (hq : 4≤q) (x : Normal) : Generated q (x.eval q) := by
  have ga : Generated q (SA q) := generated_a0 q hq
  have gb : Generated q (SB q) := generated_b0 q hq
  have gc : Generated q (SC q) := generated_c6 q hq
  have gz : Generated q (SZ q) := generated_z7 q hq
  have gl : Generated q (SL q) := generated_h7 q hq
  cases x with
  | a => exact ga
  | b => exact gb
  | ab => exact (generated_join q ga gb)
  | c => exact gc
  | ac => exact (generated_join q ga gc)
  | cb => exact (generated_join q gb gc)
  | acb => exact (generated_join q ga (generated_join q gb gc))
  | z => exact gz
  | zb => exact (generated_join q gb gz)
  | cz => exact (generated_join q gc gz)
  | l => exact gl
  | lb => exact (generated_join q gb gl)
  | cl => exact (generated_join q gc gl)
  | clb => exact (generated_join q gb (generated_join q gc gl))
  | zl => exact (generated_join q gz gl)
  | czl => exact (generated_join q gc (generated_join q gz gl))

theorem Normal.small (q : Nat) (hq : 4≤q) (x : Normal) : ¬x.eval q 2 ∧ ¬x.eval q 4 := by
  cases x <;> simp only [Normal.eval,SA,SB,SC,SZ,SL,I] <;> omega

theorem Normal.unique (q : Nat) (hq : 4≤q) (x y : Normal)
    (he : ∀e,x.eval q e ↔ y.eval q e) : x=y := by
  cases x with
  | a =>
    cases y with
    | a =>
      rfl
    | b =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | b =>
    cases y with
    | a =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      rfl
    | ab =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | ab =>
    cases y with
    | a =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      rfl
    | c =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | c =>
    cases y with
    | a =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      rfl
    | ac =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | ac =>
    cases y with
    | a =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      rfl
    | cb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (4*q)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | cb =>
    cases y with
    | a =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      rfl
    | acb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | acb =>
    cases y with
    | a =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      rfl
    | z =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | z =>
    cases y with
    | a =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      rfl
    | zb =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | zb =>
    cases y with
    | a =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      rfl
    | cz =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | cz =>
    cases y with
    | a =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (4*q)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      rfl
    | l =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | l =>
    cases y with
    | a =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      rfl
    | lb =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (4*q-1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | lb =>
    cases y with
    | a =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      rfl
    | cl =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | cl =>
    cases y with
    | a =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      rfl
    | clb =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (4*q)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | clb =>
    cases y with
    | a =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      rfl
    | zl =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | zl =>
    cases y with
    | a =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (4*q-1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      rfl
    | czl =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
  | czl =>
    cases y with
    | a =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | b =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ab =>
      have h := he (3)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | c =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | ac =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cb =>
      have h := he (1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | acb =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | z =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zb =>
      have h := he (2*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cz =>
      have h := he (2*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | l =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | lb =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | cl =>
      have h := he (4*q)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | clb =>
      have h := he (3*q+2)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | zl =>
      have h := he (3*q+1)
      simp only [Normal.eval,SA,SB,SC,SZ,SL,I] at h
      exfalso
      simp_all <;> omega
    | czl =>
      rfl

theorem exhaustive (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ ¬R 2 ∧ ¬R 4 ↔ ∃x : Normal,∀e,R e ↔ x.eval q e := by
  constructor
  · rintro ⟨hg,h2,h4⟩
    exact normal_of_generated q hq R hg h2 h4
  · rintro ⟨x,he⟩
    have hc := x.small q hq
    exact ⟨generated_congr q (x.generated q hq) (fun e=>(he e).symm),
      fun h=>hc.1 ((he 2).mp h),fun h=>hc.2 ((he 4).mp h)⟩

end LuRazSixRowClosure.Small
