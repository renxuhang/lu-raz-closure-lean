import LuRazFullJL
namespace LuRazClosure
set_option linter.unusedSimpArgs false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

theorem NFFull.addA (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) :
    ∃ w : NFFull, w.Valid q ∧ ∀ e, (z.eval q e ∨ ARow q e) ↔ w.eval q e := by
  cases z with
  | noNInterval k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNInterval k,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJRight b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNMJRight b,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJLeft a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNMJLeft a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMK k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNMK k,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNCMJ b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNCMJ b,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Short p k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short (max p (q+2)) k,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1ZL a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1ZL a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Exception  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Exception ,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH2 a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH2 a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noFive a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    by_cases ha : a≤q+3
    · refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
    · refine ⟨.leftGap (q+2) a,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
  | leftGap p a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    by_cases ha : a≤q+3
    · refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
    · refine ⟨.leftGap (max p (q+2)) a,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
  | full  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full ,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | rightGap b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.rightGap b c,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | isolatedR b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.isolatedR b c,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega

theorem NFFull.addB (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) :
    ∃ w : NFFull, w.Valid q ∧ ∀ e, (z.eval q e ∨ BRow q e) ↔ w.eval q e := by
  cases z with
  | noNInterval k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJRight b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.rightGap b (3*q+2),by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJLeft a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.leftGap (q+3) a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMK k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short (q+3) k,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNCMJ b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.rightGap b (3*q+1),by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Short p k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short p k,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1ZL a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1ZL (min a (3*q+2)),by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Exception  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short (2*q) 0,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH2 a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH2 (min a (3*q+2)),by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noFive a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noFive a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | leftGap p a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.leftGap p a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | full  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full ,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | rightGap b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    by_cases hg : min c (3*q+2)≤b+1
    · refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
    · refine ⟨.rightGap b (min c (3*q+2)),by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
  | isolatedR b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.rightGap b (3*q+1),by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega

theorem NFFull.addC (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) :
    ∃ w : NFFull, w.Valid q ∧ ∀ e, (z.eval q e ∨ CRow q e) ↔ w.eval q e := by
  cases z with
  | noNInterval k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNInterval k,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJRight b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    by_cases hb : 3*q≤b
    · refine ⟨.noNInterval 1,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
    · refine ⟨.noNCMJ b,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
  | noNMJLeft a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNInterval 1,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMK k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNInterval 1,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNCMJ b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNCMJ b,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Short p k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1ZL a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    by_cases hr : a≤3*q+2
    · refine ⟨.rightGap (2*q+2) (min a (3*q+1)),by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
    · refine ⟨.isolatedR (2*q+2) a,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
  | noH1Exception  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.rightGap (4*q-2) (4*q),by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH2 a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    by_cases hl : a≤2*q+3
    · refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
    · by_cases hr : a≤3*q+2
      · refine ⟨.rightGap (2*q+2) (min a (3*q+1)),by simp only [NFFull.Valid] <;> omega,?_⟩
        intro e
        simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
        omega
      · refine ⟨.isolatedR (2*q+2) a,by simp only [NFFull.Valid] <;> omega,?_⟩
        intro e
        simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
        omega
  | noFive a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | leftGap p a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | full  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full ,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | rightGap b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    by_cases hr : 3*q+1≤b+1
    · by_cases hrb : 3*q+1≤b
      · refine ⟨.rightGap b c,by simp only [NFFull.Valid] <;> omega,?_⟩
        intro e
        simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
        omega
      · by_cases hc : c≤3*q+2
        · refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
          intro e
          simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
          omega
        · refine ⟨.rightGap (3*q+1) c,by simp only [NFFull.Valid] <;> omega,?_⟩
          intro e
          simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
          omega
    · by_cases hrc : c≤3*q+1
      · refine ⟨.rightGap b c,by simp only [NFFull.Valid] <;> omega,?_⟩
        intro e
        simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
        omega
      · by_cases hc : c=3*q+2
        · refine ⟨.rightGap b (3*q+1),by simp only [NFFull.Valid] <;> omega,?_⟩
          intro e
          simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
          omega
        · refine ⟨.isolatedR b c,by simp only [NFFull.Valid] <;> omega,?_⟩
          intro e
          simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
          omega
  | isolatedR b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.isolatedR b c,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega

theorem NFFull.addD (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) :
    ∃ w : NFFull, w.Valid q ∧ ∀ e, (z.eval q e ∨ DRow q e) ↔ w.eval q e := by
  cases z with
  | noNInterval k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJRight b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJLeft a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.leftGap (q+3) a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMK k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.leftGap (q+3) (2*q+1),by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNCMJ b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Short p k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    by_cases hp : 2*q≤p
    · refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
    · by_cases hp4 : p=4
      · refine ⟨.noFive (2*q+1),by simp only [NFFull.Valid] <;> omega,?_⟩
        intro e
        simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
        omega
      · refine ⟨.leftGap p (2*q+1),by simp only [NFFull.Valid] <;> omega,?_⟩
        intro e
        simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
        omega
  | noH1ZL a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Exception  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH2 a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noFive a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noFive a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | leftGap p a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.leftGap p a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | full  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full ,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | rightGap b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | isolatedR b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega

theorem NFFull.addE (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) :
    ∃ w : NFFull, w.Valid q ∧ ∀ e, (z.eval q e ∨ ERow q e) ↔ w.eval q e := by
  cases z with
  | noNInterval k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJRight b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJLeft a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.leftGap (q+3) a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMK k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short (q+3) k,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNCMJ b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Short p k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short p k,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1ZL a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short (2*q) 1,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Exception  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short (2*q) 0,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH2 a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH2 (2*q+3),by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noFive a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noFive a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | leftGap p a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.leftGap p a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | full  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full ,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | rightGap b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | isolatedR b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega

theorem NFFull.addZ (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) :
    ∃ w : NFFull, w.Valid q ∧ ∀ e, (z.eval q e ∨ ZRow q e) ↔ w.eval q e := by
  cases z with
  | noNInterval k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    by_cases hk : k=0
    · refine ⟨.rightGap (4*q-2) (4*q),by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
    · refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
  | noNMJRight b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.rightGap b (3*q+2),by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJLeft a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMK k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short (2*q) k,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNCMJ b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.rightGap b (3*q+1),by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Short p k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short (2*q) k,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1ZL a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1ZL a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Exception  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Exception ,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH2 a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH2 a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noFive a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | leftGap p a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | full  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full ,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | rightGap b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.rightGap b c,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | isolatedR b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.isolatedR b c,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega

theorem NFFull.addK1 (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) :
    ∃ w : NFFull, w.Valid q ∧ ∀ e, (z.eval q e ∨ K1Row q e) ↔ w.eval q e := by
  cases z with
  | noNInterval k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNInterval k,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJRight b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNInterval 1,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJLeft a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNMJLeft a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMK k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNMK 0,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNCMJ b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNInterval 1,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Short p k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short p 0,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1ZL a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short (2*q) 0,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Exception  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Exception ,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH2 a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    by_cases ha : a≤4*q-1
    · refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
    · refine ⟨.rightGap (4*q-2) (4*q),by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
  | noFive a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noFive a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | leftGap p a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.leftGap p a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | full  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full ,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | rightGap b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    by_cases hc : c≤4*q-1
    · refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
    · refine ⟨.rightGap (4*q-2) (4*q),by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
  | isolatedR b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    by_cases hc : c≤4*q-1
    · refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega
    · refine ⟨.rightGap (4*q-2) (4*q),by simp only [NFFull.Valid] <;> omega,?_⟩
      intro e
      simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
      omega

theorem NFFull.addK2 (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) :
    ∃ w : NFFull, w.Valid q ∧ ∀ e, (z.eval q e ∨ K2Row q e) ↔ w.eval q e := by
  cases z with
  | noNInterval k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNInterval 1,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJRight b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNInterval 1,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMJLeft a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNMJLeft a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNMK k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNMK k,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noNCMJ b =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noNInterval 1,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Short p k =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short p k,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1ZL a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short (2*q) 1,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH1Exception  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH1Short (2*q) 0,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noH2 a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noH2 (2*q+3),by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | noFive a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.noFive a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | leftGap p a =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.leftGap p a,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | full  =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full ,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | rightGap b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
  | isolatedR b c =>
    have hvalid := hz
    simp only [NFFull.Valid] at hvalid
    refine ⟨.full,by simp only [NFFull.Valid] <;> omega,?_⟩
    intro e
    simp only [NFFull.eval,FullHead,ARow,BRow,CRow,DRow,ERow,ZRow,K1Row,K2Row,I]
    omega
end LuRazClosure
