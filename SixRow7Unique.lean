import SixRow7Exact
import SixRow6Unique
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
theorem keep7_shape (q : Nat) (hq : 4≤q) (z : NF123)
    (hz : z.Valid q) (hk : Keep7 q z) :
    (z.eval q (2*q+1) → z.eval q (2*q+2)) ∧
    (z.eval q (2*q+2) → z.eval q (3*q+1)) := by
  cases z <;> simp only [NF123.Valid,Keep7,P] at hz hk <;>
    simp only [NF123.eval,NF123.body,NF23.eval,LRow,LNormal,TwoPiece,I,beta] <;>
    repeat first | omega | (simp_all <;> omega) | split

def NF7.Fresh : NF7→Prop | .old _ => False | _ => True
theorem fresh7_not_old (q : Nat) (hq : 4≤q) (z : NF7) (hz : z.Valid q) (hf : z.Fresh)
    (w : NF123) (hw : w.Valid q) (hk : Keep7 q w) :
    ¬(∀e,z.eval q e ↔ w.eval q e) := by
  intro he
  have hold := keep7_shape q hq w hw hk
  have h1 : z.eval q (2*q+1) → z.eval q (2*q+2) :=
    fun h=>(he (2*q+2)).mpr (hold.1 ((he (2*q+1)).mp h))
  have h2 : z.eval q (2*q+2) → z.eval q (3*q+1) :=
    fun h=>(he (3*q+1)).mpr (hold.2 ((he (2*q+2)).mp h))
  cases z <;> simp only [NF7.Fresh,NF7.Valid,P] at hf hz <;>
    simp only [NF7.eval,NF6.eval,I,beta] at h1 h2 <;>
    repeat first | omega | (simp_all <;> omega) | split at h1 <;> split at h2

theorem NF7.unique (q : Nat) (hq : 4≤q) (z w : NF7)
    (hz : z.Valid q) (hw : w.Valid q) (he : ∀e,z.eval q e ↔ w.eval q e) : z=w := by
  cases z with
  | old z =>
    cases w with
    | old z2 =>
      have hh := NF123.unique q hq z z2 hz.1 hw.1 he
      cases hh
      rfl
    | creg t2 =>
      exact False.elim (fresh7_not_old q hq (.creg t2) hw True.intro z hz.1 hz.2 (fun e=>(he e).symm))
    | cex =>
      exact False.elim (fresh7_not_old q hq (.cex) hw True.intro z hz.1 hz.2 (fun e=>(he e).symm))
    | right c2 =>
      exact False.elim (fresh7_not_old q hq (.right c2) hw True.intro z hz.1 hz.2 (fun e=>(he e).symm))
    | rex =>
      exact False.elim (fresh7_not_old q hq (.rex) hw True.intro z hz.1 hz.2 (fun e=>(he e).symm))
    | point =>
      exact False.elim (fresh7_not_old q hq (.point) hw True.intro z hz.1 hz.2 (fun e=>(he e).symm))
  | creg t =>
    cases w with
    | old z2 =>
      exact False.elim (fresh7_not_old q hq (.creg t) hz True.intro z2 hw.1 hw.2 he)
    | creg t2 =>
      have hc := NF6.core q hq (.creg t) hz
      have hd := NF6.core q hq (.creg t2) hw
      have he6 : ∀e,NF6.eval q (.creg t) e ↔ NF6.eval q (.creg t2) e := by
        intro e
        by_cases he1 : e=1
        · subst e; exact iff_of_false hc.1 hd.1
        · simpa only [NF7.eval,he1,false_or] using he e
      have hh := NF6.unique q hq (.creg t) (.creg t2) hz hw he6
      cases hh <;> rfl
    | cex =>
      have hc := NF6.core q hq (.creg t) hz
      have hd := NF6.core q hq (.cex) hw
      have he6 : ∀e,NF6.eval q (.creg t) e ↔ NF6.eval q (.cex) e := by
        intro e
        by_cases he1 : e=1
        · subst e; exact iff_of_false hc.1 hd.1
        · simpa only [NF7.eval,he1,false_or] using he e
      have hh := NF6.unique q hq (.creg t) (.cex) hz hw he6
      cases hh <;> rfl
    | right c2 =>
      have hh := he (2*q+2)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | rex =>
      have hh := he (2*q+2)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | point =>
      have hh := he (2*q+3)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
  | cex =>
    cases w with
    | old z2 =>
      exact False.elim (fresh7_not_old q hq (.cex) hz True.intro z2 hw.1 hw.2 he)
    | creg t2 =>
      have hc := NF6.core q hq (.cex) hz
      have hd := NF6.core q hq (.creg t2) hw
      have he6 : ∀e,NF6.eval q (.cex) e ↔ NF6.eval q (.creg t2) e := by
        intro e
        by_cases he1 : e=1
        · subst e; exact iff_of_false hc.1 hd.1
        · simpa only [NF7.eval,he1,false_or] using he e
      have hh := NF6.unique q hq (.cex) (.creg t2) hz hw he6
      cases hh <;> rfl
    | cex =>
      have hc := NF6.core q hq (.cex) hz
      have hd := NF6.core q hq (.cex) hw
      have he6 : ∀e,NF6.eval q (.cex) e ↔ NF6.eval q (.cex) e := by
        intro e
        by_cases he1 : e=1
        · subst e; exact iff_of_false hc.1 hd.1
        · simpa only [NF7.eval,he1,false_or] using he e
      have hh := NF6.unique q hq (.cex) (.cex) hz hw he6
      cases hh <;> rfl
    | right c2 =>
      have hh := he (2*q+2)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | rex =>
      have hh := he (2*q+2)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | point =>
      have hh := he (2*q+3)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
  | right c =>
    cases w with
    | old z2 =>
      exact False.elim (fresh7_not_old q hq (.right c) hz True.intro z2 hw.1 hw.2 he)
    | creg t2 =>
      have hh := he (2*q+2)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | cex =>
      have hh := he (2*q+2)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | right c2 =>
      have h1 := he c
      have h2 := he c2
      have hcv : 3*q+2≤c ∧ c≤4*q-1 := hz
      have hdv : 3*q+2≤c2 ∧ c2≤4*q-1 := hw
      have hh : c=c2 := by
        simp only [NF7.eval,I] at h1 h2
        omega
      cases hh
      rfl
    | rex =>
      have hh := he (4*q)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | point =>
      have hh := he (2*q+2)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
  | rex =>
    cases w with
    | old z2 =>
      exact False.elim (fresh7_not_old q hq (.rex) hz True.intro z2 hw.1 hw.2 he)
    | creg t2 =>
      have hh := he (2*q+2)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | cex =>
      have hh := he (2*q+2)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | right c2 =>
      have hh := he (4*q)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | rex =>
      rfl
    | point =>
      have hh := he (2*q+2)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
  | point =>
    cases w with
    | old z2 =>
      exact False.elim (fresh7_not_old q hq (.point) hz True.intro z2 hw.1 hw.2 he)
    | creg t2 =>
      have hh := he (2*q+3)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | cex =>
      have hh := he (2*q+3)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | right c2 =>
      have hh := he (2*q+2)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | rex =>
      have hh := he (2*q+2)
      simp only [NF7.Valid,P] at hz hw
      simp only [NF7.eval,NF6.eval,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | point =>
      rfl
end LuRazSixRowClosure
