import LuRazSmallNormal
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem NFSmall.unique (q : Nat) (hq : 4≤q) (z w : NFSmall)
    (heq : ∀ e, z.eval q e ↔ w.eval q e) : z=w := by
  cases z with
  | bOnly =>
    cases w with
    | bOnly =>
      rfl
    | aOnly =>
      have h := heq (1)
      change (BRow q (1)) ↔ (ARow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ab =>
      have h := heq (1)
      change (BRow q (1)) ↔ (ARow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | dOnly =>
      have h := heq (2)
      change (BRow q (2)) ↔ (DRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ad =>
      have h := heq (1)
      change (BRow q (1)) ↔ (ARow q (1) ∨ DRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cOnly =>
      have h := heq (3)
      change (BRow q (3)) ↔ (CRow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cb =>
      have h := heq (3)
      change (BRow q (3)) ↔ (CRow q (3) ∨ BRow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | eOnly =>
      have h := heq (1)
      change (BRow q (1)) ↔ (ERow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ae =>
      have h := heq (1)
      change (BRow q (1)) ↔ (ARow q (1) ∨ ERow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ce =>
      have h := heq (1)
      change (BRow q (1)) ↔ (CRow q (1) ∨ ERow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ac =>
      have h := heq (1)
      change (BRow q (1)) ↔ (ARow q (1) ∨ CRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | acb =>
      have h := heq (1)
      change (BRow q (1)) ↔ (ARow q (1) ∨ CRow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
  | aOnly =>
    cases w with
    | bOnly =>
      have h := heq (1)
      change (ARow q (1)) ↔ (BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | aOnly =>
      rfl
    | ab =>
      have h := heq (4*q)
      change (ARow q (4*q)) ↔ (ARow q (4*q) ∨ BRow q (4*q)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | dOnly =>
      have h := heq (1)
      change (ARow q (1)) ↔ (DRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ad =>
      have h := heq (2)
      change (ARow q (2)) ↔ (ARow q (2) ∨ DRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cOnly =>
      have h := heq (1)
      change (ARow q (1)) ↔ (CRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cb =>
      have h := heq (1)
      change (ARow q (1)) ↔ (CRow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | eOnly =>
      have h := heq (3)
      change (ARow q (3)) ↔ (ERow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ae =>
      have h := heq (3)
      change (ARow q (3)) ↔ (ARow q (3) ∨ ERow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ce =>
      have h := heq (3)
      change (ARow q (3)) ↔ (CRow q (3) ∨ ERow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ac =>
      have h := heq (3)
      change (ARow q (3)) ↔ (ARow q (3) ∨ CRow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | acb =>
      have h := heq (3)
      change (ARow q (3)) ↔ (ARow q (3) ∨ CRow q (3) ∨ BRow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
  | ab =>
    cases w with
    | bOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ BRow q (1)) ↔ (BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | aOnly =>
      have h := heq (4*q)
      change (ARow q (4*q) ∨ BRow q (4*q)) ↔ (ARow q (4*q)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ab =>
      rfl
    | dOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ BRow q (1)) ↔ (DRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ad =>
      have h := heq (2)
      change (ARow q (2) ∨ BRow q (2)) ↔ (ARow q (2) ∨ DRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ BRow q (1)) ↔ (CRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cb =>
      have h := heq (1)
      change (ARow q (1) ∨ BRow q (1)) ↔ (CRow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | eOnly =>
      have h := heq (3)
      change (ARow q (3) ∨ BRow q (3)) ↔ (ERow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ae =>
      have h := heq (3)
      change (ARow q (3) ∨ BRow q (3)) ↔ (ARow q (3) ∨ ERow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ce =>
      have h := heq (3)
      change (ARow q (3) ∨ BRow q (3)) ↔ (CRow q (3) ∨ ERow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ac =>
      have h := heq (3)
      change (ARow q (3) ∨ BRow q (3)) ↔ (ARow q (3) ∨ CRow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | acb =>
      have h := heq (3)
      change (ARow q (3) ∨ BRow q (3)) ↔ (ARow q (3) ∨ CRow q (3) ∨ BRow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
  | dOnly =>
    cases w with
    | bOnly =>
      have h := heq (2)
      change (DRow q (2)) ↔ (BRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | aOnly =>
      have h := heq (1)
      change (DRow q (1)) ↔ (ARow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ab =>
      have h := heq (1)
      change (DRow q (1)) ↔ (ARow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | dOnly =>
      rfl
    | ad =>
      have h := heq (1)
      change (DRow q (1)) ↔ (ARow q (1) ∨ DRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cOnly =>
      have h := heq (2)
      change (DRow q (2)) ↔ (CRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cb =>
      have h := heq (2)
      change (DRow q (2)) ↔ (CRow q (2) ∨ BRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | eOnly =>
      have h := heq (1)
      change (DRow q (1)) ↔ (ERow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ae =>
      have h := heq (1)
      change (DRow q (1)) ↔ (ARow q (1) ∨ ERow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ce =>
      have h := heq (1)
      change (DRow q (1)) ↔ (CRow q (1) ∨ ERow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ac =>
      have h := heq (1)
      change (DRow q (1)) ↔ (ARow q (1) ∨ CRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | acb =>
      have h := heq (1)
      change (DRow q (1)) ↔ (ARow q (1) ∨ CRow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
  | ad =>
    cases w with
    | bOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ DRow q (1)) ↔ (BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | aOnly =>
      have h := heq (2)
      change (ARow q (2) ∨ DRow q (2)) ↔ (ARow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ab =>
      have h := heq (2)
      change (ARow q (2) ∨ DRow q (2)) ↔ (ARow q (2) ∨ BRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | dOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ DRow q (1)) ↔ (DRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ad =>
      rfl
    | cOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ DRow q (1)) ↔ (CRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cb =>
      have h := heq (1)
      change (ARow q (1) ∨ DRow q (1)) ↔ (CRow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | eOnly =>
      have h := heq (2)
      change (ARow q (2) ∨ DRow q (2)) ↔ (ERow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ae =>
      have h := heq (2)
      change (ARow q (2) ∨ DRow q (2)) ↔ (ARow q (2) ∨ ERow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ce =>
      have h := heq (2)
      change (ARow q (2) ∨ DRow q (2)) ↔ (CRow q (2) ∨ ERow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ac =>
      have h := heq (2)
      change (ARow q (2) ∨ DRow q (2)) ↔ (ARow q (2) ∨ CRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | acb =>
      have h := heq (2)
      change (ARow q (2) ∨ DRow q (2)) ↔ (ARow q (2) ∨ CRow q (2) ∨ BRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
  | cOnly =>
    cases w with
    | bOnly =>
      have h := heq (3)
      change (CRow q (3)) ↔ (BRow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | aOnly =>
      have h := heq (1)
      change (CRow q (1)) ↔ (ARow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ab =>
      have h := heq (1)
      change (CRow q (1)) ↔ (ARow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | dOnly =>
      have h := heq (2)
      change (CRow q (2)) ↔ (DRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ad =>
      have h := heq (1)
      change (CRow q (1)) ↔ (ARow q (1) ∨ DRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cOnly =>
      rfl
    | cb =>
      have h := heq (4*q)
      change (CRow q (4*q)) ↔ (CRow q (4*q) ∨ BRow q (4*q)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | eOnly =>
      have h := heq (1)
      change (CRow q (1)) ↔ (ERow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ae =>
      have h := heq (1)
      change (CRow q (1)) ↔ (ARow q (1) ∨ ERow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ce =>
      have h := heq (1)
      change (CRow q (1)) ↔ (CRow q (1) ∨ ERow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ac =>
      have h := heq (1)
      change (CRow q (1)) ↔ (ARow q (1) ∨ CRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | acb =>
      have h := heq (1)
      change (CRow q (1)) ↔ (ARow q (1) ∨ CRow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
  | cb =>
    cases w with
    | bOnly =>
      have h := heq (3)
      change (CRow q (3) ∨ BRow q (3)) ↔ (BRow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | aOnly =>
      have h := heq (1)
      change (CRow q (1) ∨ BRow q (1)) ↔ (ARow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ab =>
      have h := heq (1)
      change (CRow q (1) ∨ BRow q (1)) ↔ (ARow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | dOnly =>
      have h := heq (2)
      change (CRow q (2) ∨ BRow q (2)) ↔ (DRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ad =>
      have h := heq (1)
      change (CRow q (1) ∨ BRow q (1)) ↔ (ARow q (1) ∨ DRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cOnly =>
      have h := heq (4*q)
      change (CRow q (4*q) ∨ BRow q (4*q)) ↔ (CRow q (4*q)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cb =>
      rfl
    | eOnly =>
      have h := heq (1)
      change (CRow q (1) ∨ BRow q (1)) ↔ (ERow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ae =>
      have h := heq (1)
      change (CRow q (1) ∨ BRow q (1)) ↔ (ARow q (1) ∨ ERow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ce =>
      have h := heq (1)
      change (CRow q (1) ∨ BRow q (1)) ↔ (CRow q (1) ∨ ERow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ac =>
      have h := heq (1)
      change (CRow q (1) ∨ BRow q (1)) ↔ (ARow q (1) ∨ CRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | acb =>
      have h := heq (1)
      change (CRow q (1) ∨ BRow q (1)) ↔ (ARow q (1) ∨ CRow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
  | eOnly =>
    cases w with
    | bOnly =>
      have h := heq (1)
      change (ERow q (1)) ↔ (BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | aOnly =>
      have h := heq (3)
      change (ERow q (3)) ↔ (ARow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ab =>
      have h := heq (3)
      change (ERow q (3)) ↔ (ARow q (3) ∨ BRow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | dOnly =>
      have h := heq (1)
      change (ERow q (1)) ↔ (DRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ad =>
      have h := heq (2)
      change (ERow q (2)) ↔ (ARow q (2) ∨ DRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cOnly =>
      have h := heq (1)
      change (ERow q (1)) ↔ (CRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cb =>
      have h := heq (1)
      change (ERow q (1)) ↔ (CRow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | eOnly =>
      rfl
    | ae =>
      have h := heq (5)
      change (ERow q (5)) ↔ (ARow q (5) ∨ ERow q (5)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ce =>
      have h := heq (5)
      change (ERow q (5)) ↔ (CRow q (5) ∨ ERow q (5)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ac =>
      have h := heq (5)
      change (ERow q (5)) ↔ (ARow q (5) ∨ CRow q (5)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | acb =>
      have h := heq (5)
      change (ERow q (5)) ↔ (ARow q (5) ∨ CRow q (5) ∨ BRow q (5)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
  | ae =>
    cases w with
    | bOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ ERow q (1)) ↔ (BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | aOnly =>
      have h := heq (3)
      change (ARow q (3) ∨ ERow q (3)) ↔ (ARow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ab =>
      have h := heq (3)
      change (ARow q (3) ∨ ERow q (3)) ↔ (ARow q (3) ∨ BRow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | dOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ ERow q (1)) ↔ (DRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ad =>
      have h := heq (2)
      change (ARow q (2) ∨ ERow q (2)) ↔ (ARow q (2) ∨ DRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ ERow q (1)) ↔ (CRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cb =>
      have h := heq (1)
      change (ARow q (1) ∨ ERow q (1)) ↔ (CRow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | eOnly =>
      have h := heq (5)
      change (ARow q (5) ∨ ERow q (5)) ↔ (ERow q (5)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ae =>
      rfl
    | ce =>
      have h := heq (q+3)
      change (ARow q (q+3) ∨ ERow q (q+3)) ↔ (CRow q (q+3) ∨ ERow q (q+3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ac =>
      have h := heq (4*q)
      change (ARow q (4*q) ∨ ERow q (4*q)) ↔ (ARow q (4*q) ∨ CRow q (4*q)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | acb =>
      have h := heq (q+3)
      change (ARow q (q+3) ∨ ERow q (q+3)) ↔ (ARow q (q+3) ∨ CRow q (q+3) ∨ BRow q (q+3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
  | ce =>
    cases w with
    | bOnly =>
      have h := heq (1)
      change (CRow q (1) ∨ ERow q (1)) ↔ (BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | aOnly =>
      have h := heq (3)
      change (CRow q (3) ∨ ERow q (3)) ↔ (ARow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ab =>
      have h := heq (3)
      change (CRow q (3) ∨ ERow q (3)) ↔ (ARow q (3) ∨ BRow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | dOnly =>
      have h := heq (1)
      change (CRow q (1) ∨ ERow q (1)) ↔ (DRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ad =>
      have h := heq (2)
      change (CRow q (2) ∨ ERow q (2)) ↔ (ARow q (2) ∨ DRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cOnly =>
      have h := heq (1)
      change (CRow q (1) ∨ ERow q (1)) ↔ (CRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cb =>
      have h := heq (1)
      change (CRow q (1) ∨ ERow q (1)) ↔ (CRow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | eOnly =>
      have h := heq (5)
      change (CRow q (5) ∨ ERow q (5)) ↔ (ERow q (5)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ae =>
      have h := heq (q+3)
      change (CRow q (q+3) ∨ ERow q (q+3)) ↔ (ARow q (q+3) ∨ ERow q (q+3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ce =>
      rfl
    | ac =>
      have h := heq (4*q)
      change (CRow q (4*q) ∨ ERow q (4*q)) ↔ (ARow q (4*q) ∨ CRow q (4*q)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | acb =>
      have h := heq (2*q+3)
      change (CRow q (2*q+3) ∨ ERow q (2*q+3)) ↔ (ARow q (2*q+3) ∨ CRow q (2*q+3) ∨ BRow q (2*q+3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
  | ac =>
    cases w with
    | bOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ CRow q (1)) ↔ (BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | aOnly =>
      have h := heq (3)
      change (ARow q (3) ∨ CRow q (3)) ↔ (ARow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ab =>
      have h := heq (3)
      change (ARow q (3) ∨ CRow q (3)) ↔ (ARow q (3) ∨ BRow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | dOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ CRow q (1)) ↔ (DRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ad =>
      have h := heq (2)
      change (ARow q (2) ∨ CRow q (2)) ↔ (ARow q (2) ∨ DRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ CRow q (1)) ↔ (CRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cb =>
      have h := heq (1)
      change (ARow q (1) ∨ CRow q (1)) ↔ (CRow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | eOnly =>
      have h := heq (5)
      change (ARow q (5) ∨ CRow q (5)) ↔ (ERow q (5)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ae =>
      have h := heq (4*q)
      change (ARow q (4*q) ∨ CRow q (4*q)) ↔ (ARow q (4*q) ∨ ERow q (4*q)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ce =>
      have h := heq (4*q)
      change (ARow q (4*q) ∨ CRow q (4*q)) ↔ (CRow q (4*q) ∨ ERow q (4*q)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ac =>
      rfl
    | acb =>
      have h := heq (4*q)
      change (ARow q (4*q) ∨ CRow q (4*q)) ↔ (ARow q (4*q) ∨ CRow q (4*q) ∨ BRow q (4*q)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
  | acb =>
    cases w with
    | bOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ CRow q (1) ∨ BRow q (1)) ↔ (BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | aOnly =>
      have h := heq (3)
      change (ARow q (3) ∨ CRow q (3) ∨ BRow q (3)) ↔ (ARow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ab =>
      have h := heq (3)
      change (ARow q (3) ∨ CRow q (3) ∨ BRow q (3)) ↔ (ARow q (3) ∨ BRow q (3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | dOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ CRow q (1) ∨ BRow q (1)) ↔ (DRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ad =>
      have h := heq (2)
      change (ARow q (2) ∨ CRow q (2) ∨ BRow q (2)) ↔ (ARow q (2) ∨ DRow q (2)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cOnly =>
      have h := heq (1)
      change (ARow q (1) ∨ CRow q (1) ∨ BRow q (1)) ↔ (CRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | cb =>
      have h := heq (1)
      change (ARow q (1) ∨ CRow q (1) ∨ BRow q (1)) ↔ (CRow q (1) ∨ BRow q (1)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | eOnly =>
      have h := heq (5)
      change (ARow q (5) ∨ CRow q (5) ∨ BRow q (5)) ↔ (ERow q (5)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ae =>
      have h := heq (q+3)
      change (ARow q (q+3) ∨ CRow q (q+3) ∨ BRow q (q+3)) ↔ (ARow q (q+3) ∨ ERow q (q+3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ce =>
      have h := heq (2*q+3)
      change (ARow q (2*q+3) ∨ CRow q (2*q+3) ∨ BRow q (2*q+3)) ↔ (CRow q (2*q+3) ∨ ERow q (2*q+3)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | ac =>
      have h := heq (4*q)
      change (ARow q (4*q) ∨ CRow q (4*q) ∨ BRow q (4*q)) ↔ (ARow q (4*q) ∨ CRow q (4*q)) at h
      exfalso
      simp only [ARow,BRow,CRow,DRow,ERow,I] at h
      simp_all <;> omega
    | acb =>
      rfl

end LuRazClosure
