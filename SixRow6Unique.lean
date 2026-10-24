import SixRow6Exact
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
theorem NF6.unique (q : Nat) (hq : 4≤q) (z w : NF6)
    (hz : z.Valid q) (hw : w.Valid q) (he : ∀e,z.eval q e ↔ w.eval q e) : z=w := by
  cases z with
  | lp t p =>
    cases w with
    | lp t2 p2 =>
      have hh := NF23.unique q hq (.lp t p) (.lp t2 p2) ⟨hz.1,hz.2.1,hz.2.2.1⟩ ⟨hw.1,hw.2.1,hw.2.2.1⟩ he
      cases hh <;> rfl
    | filled =>
      have hh := NF23.unique q hq (.lp t p) (.filledM) ⟨hz.1,hz.2.1,hz.2.2.1⟩ True.intro he
      cases hh <;> rfl
    | creg t2 =>
      have hh := he (2*q+1)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | cex =>
      have hh := he (2*q+1)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | er p2 =>
      have hh := he (2*q+3)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
  | filled =>
    cases w with
    | lp t2 p2 =>
      have hh := NF23.unique q hq (.filledM) (.lp t2 p2) True.intro ⟨hw.1,hw.2.1,hw.2.2.1⟩ he
      cases hh <;> rfl
    | filled =>
      have hh := NF23.unique q hq (.filledM) (.filledM) True.intro True.intro he
      cases hh <;> rfl
    | creg t2 =>
      have hh := he (2*q+1)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | cex =>
      have hh := he (2*q+1)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | er p2 =>
      have hh := he (2*q+3)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
  | creg t =>
    cases w with
    | lp t2 p2 =>
      have hh := he (2*q+1)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | filled =>
      have hh := he (2*q+1)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | creg t2 =>
      have hzo : ∀e,NF23.eval q (.creg t) e ↔ (NF6.eval q (.creg t) e ∨ e=2*q+2) := by
        intro e; simp only [NF23.eval,NF6.eval,I]; omega
      have hwo : ∀e,NF23.eval q (.creg t2) e ↔ (NF6.eval q (.creg t2) e ∨ e=2*q+2) := by
        intro e; simp only [NF23.eval,NF6.eval,I]; omega
      have hh := NF23.unique q hq (.creg t) (.creg t2) ⟨hz.1,hz.2.2⟩ ⟨hw.1,hw.2.2⟩
        (fun e=>(hzo e).trans ((or_congr (he e) Iff.rfl).trans (hwo e).symm))
      cases hh <;> rfl
    | cex =>
      have hzo : ∀e,NF23.eval q (.creg t) e ↔ (NF6.eval q (.creg t) e ∨ e=2*q+2) := by
        intro e; simp only [NF23.eval,NF6.eval,I]; omega
      have hwo : ∀e,NF23.eval q (.cexception) e ↔ (NF6.eval q (.cex) e ∨ e=2*q+2) := by
        intro e; simp only [NF23.eval,NF6.eval,I]; omega
      have hh := NF23.unique q hq (.creg t) (.cexception) ⟨hz.1,hz.2.2⟩ True.intro
        (fun e=>(hzo e).trans ((or_congr (he e) Iff.rfl).trans (hwo e).symm))
      cases hh <;> rfl
    | er p2 =>
      have hh := he (2*q+3)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
  | cex =>
    cases w with
    | lp t2 p2 =>
      have hh := he (2*q+1)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | filled =>
      have hh := he (2*q+1)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | creg t2 =>
      have hzo : ∀e,NF23.eval q (.cexception) e ↔ (NF6.eval q (.cex) e ∨ e=2*q+2) := by
        intro e; simp only [NF23.eval,NF6.eval,I]; omega
      have hwo : ∀e,NF23.eval q (.creg t2) e ↔ (NF6.eval q (.creg t2) e ∨ e=2*q+2) := by
        intro e; simp only [NF23.eval,NF6.eval,I]; omega
      have hh := NF23.unique q hq (.cexception) (.creg t2) True.intro ⟨hw.1,hw.2.2⟩
        (fun e=>(hzo e).trans ((or_congr (he e) Iff.rfl).trans (hwo e).symm))
      cases hh <;> rfl
    | cex =>
      have hzo : ∀e,NF23.eval q (.cexception) e ↔ (NF6.eval q (.cex) e ∨ e=2*q+2) := by
        intro e; simp only [NF23.eval,NF6.eval,I]; omega
      have hwo : ∀e,NF23.eval q (.cexception) e ↔ (NF6.eval q (.cex) e ∨ e=2*q+2) := by
        intro e; simp only [NF23.eval,NF6.eval,I]; omega
      have hh := NF23.unique q hq (.cexception) (.cexception) True.intro True.intro
        (fun e=>(hzo e).trans ((or_congr (he e) Iff.rfl).trans (hwo e).symm))
      cases hh <;> rfl
    | er p2 =>
      have hh := he (2*q+3)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
  | er p =>
    cases w with
    | lp t2 p2 =>
      have hh := he (2*q+3)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | filled =>
      have hh := he (2*q+3)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | creg t2 =>
      have hh := he (2*q+3)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | cex =>
      have hh := he (2*q+3)
      simp only [NF6.Valid,P] at hz hw
      simp only [NF6.eval,NF23.eval,LRow,LNormal,I,beta] at hh
      repeat first | omega | (simp_all <;> omega) | split at hh
    | er p2 =>
      have h1 := he (p+1)
      have h2 := he (p2+1)
      simp only [NF6.Valid,P] at hz hw
      have hp : p=p2 := by
        simp only [NF6.eval,I] at h1 h2
        omega
      cases hp
      rfl
end LuRazSixRowClosure
