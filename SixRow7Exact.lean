import SixRow7Normal
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
theorem NF7.generated (q : Nat) (hq : 4≤q) (z : NF7) (hz : z.Valid q) : Generated q (z.eval q) := by
  have hp4 : P q 4 := by unfold P; omega
  have hpe : P q (q+3) := by unfold P; omega
  cases z with
  | old z =>
    have hzv := hz.1
    have hzk := hz.2
    cases z with
    | low t =>
      have ht : P q t := by have hh : 4≤t ∧ t≤q+1 := hzv; unfold P; omega
      have hh : 4≤t ∧ t≤q+1 := hzv
      have hv : NF6.Valid q (.lp t t) := ⟨ht,ht,by omega,by omega⟩
      apply generated_congr q (generated_join q (NF6.generated q hq (.lp t t) hv) (generated_a0 q hq))
      intro e
      simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    | high t p =>
      have ht := hzv.1
      have hp := hzv.2.1
      have htp : t≤p := hzv.2.2.2
      have hph : p≤2*q := hzk
      have ht0 := ht
      have hp0 := hp
      unfold P at ht0 hp0
      have hplo : q+3≤p := hzv.2.2.1
      have hv : NF6.Valid q (.lp t p) := ⟨ht,hp,htp,hph⟩
      apply generated_congr q (generated_join q (NF6.generated q hq (.lp t p) hv) (generated_a0 q hq))
      intro e
      simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    | filled =>
      have hv : NF6.Valid q (.filled) := True.intro
      apply generated_congr q (generated_join q (NF6.generated q hq (.filled) hv) (generated_a0 q hq))
      intro e
      simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    | full =>
      have hv : NF6.Valid q (.er 4) := hp4
      apply generated_congr q (generated_join q (NF6.generated q hq (.er 4) hv) (generated_h7 q hq))
      intro e
      simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    | creg t =>
      have ht : P q t := hzv.1
      have ht0 := ht
      unfold P at ht0
      have hth : t≤2*q := hzk
      have htn : t≠q+3 := hzv.2
      have hv : NF6.Valid q (.creg t) := ⟨ht,hth,htn⟩
      apply generated_congr q (generated_join q (NF6.generated q hq (.creg t) hv) (generated_h7 q hq))
      intro e
      simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    | cex =>
      have hv : NF6.Valid q (.cex) := True.intro
      apply generated_congr q (generated_join q (NF6.generated q hq (.cex) hv) (generated_h7 q hq))
      intro e
      simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    | er p =>
      have hpv : 4≤p ∧ p≤2*q+1 := hzv
      have hpk : q+2≤p ∧ p≤2*q := hzk
      by_cases he : p=q+2
      ·
        have hv : NF6.Valid q (.er 4) := hp4
        apply generated_congr q (generated_join q (NF6.generated q hq (.er 4) hv) (generated_a0 q hq))
        intro e
        simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
        repeat first | omega | (simp_all <;> omega) | split
      · have hp : P q p := by unfold P; omega
        have hv : NF6.Valid q (.er p) := hp
        apply generated_congr q (generated_join q (NF6.generated q hq (.er p) hv) (generated_a0 q hq))
        intro e
        simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
        repeat first | omega | (simp_all <;> omega) | split
    | dg p => exact False.elim hzk
    | ed p => exact False.elim hzk
  | creg t =>
    have ht := hz.1
    have ht0 := ht
    unfold P at ht0
    have hth : t≤2*q := hz.2.1
    have htn : t≠q+3 := hz.2.2
    have hv : NF6.Valid q (.creg t) := ⟨ht,hth,htn⟩
    apply generated_congr q (generated_join q (NF6.generated q hq (.creg t) hv) (generated_a0 q hq))
    intro e
    simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | cex =>
    have hv : NF6.Valid q (.cex) := True.intro
    apply generated_congr q (generated_join q (NF6.generated q hq (.cex) hv) (generated_a0 q hq))
    intro e
    simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | right c =>
    have hc : 3*q+2≤c ∧ c≤4*q-1 := hz
    obtain ⟨t,ht,he⟩ := beta_surjective q c hq (by omega)
    have ht0 := ht
    unfold P at ht0
    have hth : t≤2*q := by unfold beta at he; split at he <;> omega
    unfold beta at he
    by_cases hte : t=q+3
    ·
      have hv : NF6.Valid q (.filled) := True.intro
      apply generated_congr q (generated_join q (NF6.generated q hq (.filled) hv) (generated_h7 q hq))
      intro e
      simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
    ·
      have hv : NF6.Valid q (.lp t t) := ⟨ht,ht,by omega,hth⟩
      apply generated_congr q (generated_join q (NF6.generated q hq (.lp t t) hv) (generated_h7 q hq))
      intro e
      simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
      repeat first | omega | (simp_all <;> omega) | split
  | rex =>
    have hv : NF6.Valid q (.lp (q+3) (q+3)) := ⟨hpe,hpe,by omega,by omega⟩
    apply generated_congr q (generated_join q (NF6.generated q hq (.lp (q+3) (q+3)) hv) (generated_h7 q hq))
    intro e
    simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | point =>
    have hv : NF6.Valid q (.er (2*q+1)) := by unfold NF6.Valid P; omega
    apply generated_congr q (generated_join q (NF6.generated q hq (.er (2*q+1)) hv) (generated_a0 q hq))
    intro e
    simp only [NF7.eval,NF123.eval,NF123.body,NF6.eval,NF23.eval,ARow,H7,LRow,LNormal,TwoPiece,I,beta]
    repeat first | omega | (simp_all <;> omega) | split

theorem NF7.core (q : Nat) (hq : 4≤q) (z : NF7) (hz : z.Valid q) : Core123 (z.eval q) := by
  cases z with
  | old z => exact NF123.core q hq z hz.1
  | creg t =>
    have hh := NF6.core q hq (.creg t) hz
    simp only [Core123,NF7.eval,Core23] at *
    simp_all
  | cex =>
    have hh := NF6.core q hq .cex True.intro
    simp only [Core123,NF7.eval,Core23] at *
    simp_all
  | right c =>
    have hc : 3*q+2≤c ∧ c≤4*q-1 := hz
    simp only [Core123,NF7.eval,I]
    simp_all <;> omega
  | rex =>
    simp only [Core123,NF7.eval,I]
    simp_all <;> omega
  | point =>
    simp only [Core123,NF7.eval,I]
    simp_all <;> omega

theorem core7_exhaustive (q : Nat) (hq : 4≤q) (R : Nat→Prop) :
    Generated q R ∧ Core123 R ↔ ∃z : NF7,z.Valid q ∧ ∀e,R e ↔ z.eval q e := by
  constructor
  · exact fun h=>core7_normal q hq R h.1 h.2
  · rintro ⟨z,hz,he⟩
    refine ⟨generated_congr q (z.generated q hq hz) (fun e=>(he e).symm),?_⟩
    have hc := z.core q hq hz
    exact ⟨(he 1).mpr hc.1,(he 2).mpr hc.2.1,(he 3).mpr hc.2.2.1,
      fun h=>hc.2.2.2 ((he 4).mp h)⟩
end LuRazSixRowClosure
