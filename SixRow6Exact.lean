import SixRow6Normal
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
theorem NF6.generated (q : Nat) (hq : 4≤q) (z : NF6) (hz : z.Valid q) :
    Generated q (z.eval q) := by
  have hpe : P q (q+3) := by unfold P; omega
  cases z with
  | lp t p => exact generated_l6 q t p hq hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  | filled =>
    apply generated_congr q (generated_join q (generated_l6 q (q+3) (q+3) hq hpe hpe (by omega) (by omega)) (generated_b0 q hq))
    intro e
    simp only [NF6.eval,NF23.eval,LRow,LNormal,LuRazClosure.BRow,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | creg t =>
    have ht := hz.1
    have hth : t≤2*q := hz.2.1
    have ht' := ht
    unfold P at ht'
    apply generated_congr q (generated_join q (generated_l6 q t t hq ht ht (by omega) hz.2.1) (generated_c6 q hq))
    intro e
    simp only [NF6.eval,LRow,LNormal,C6,I,beta]
    have hn : t≠q+3 := hz.2.2
    repeat first | omega | (simp_all <;> omega) | split
  | cex =>
    apply generated_congr q (generated_join q (generated_l6 q (q+3) (q+3) hq hpe hpe (by omega) (by omega)) (generated_c6 q hq))
    intro e
    simp only [NF6.eval,LRow,LNormal,C6,I,beta]
    repeat first | omega | (simp_all <;> omega) | split
  | er p =>
    have hp : P q p := hz
    have hp' := hp
    unfold P at hp'
    by_cases he : p=2*q+1
    · apply generated_congr q (generated_join q (generated_e6 q hq) (generated_c6 q hq))
      intro e
      simp only [NF6.eval,E6,C6,I]
      omega
    · apply generated_congr q (generated_join q (generated_l6 q p p hq hp hp (by omega) (by omega)) (generated_e6 q hq))
      intro e
      simp only [NF6.eval,E6,LRow,LNormal,I,beta]
      repeat first | omega | (simp_all <;> omega) | split

theorem NF6.core (q : Nat) (hq : 4≤q) (z : NF6) (hz : z.Valid q) : Core23 (z.eval q) := by
  cases z <;> simp only [NF6.Valid,P] at hz <;>
    simp only [Core23,NF6.eval,NF23.eval,LRow,LNormal,I,beta] <;>
    repeat first | omega | (simp_all <;> omega) | split

theorem core6_exhaustive (q : Nat) (hq : 4≤q) (R : Nat→Prop) :
    Generated q R ∧ Core23 R ↔ ∃z : NF6,z.Valid q ∧ ∀e,R e ↔ z.eval q e := by
  constructor
  · exact fun h=>core6_normal q hq R h.1 h.2
  · rintro ⟨z,hz,he⟩
    refine ⟨generated_congr q (z.generated q hq hz) (fun e=>(he e).symm),?_⟩
    have hc := z.core q hq hz
    exact ⟨fun h=>hc.1 ((he 1).mp h),(he 2).mpr hc.2.1,(he 3).mpr hc.2.2.1,
      fun h=>hc.2.2.2 ((he 4).mp h)⟩
end LuRazSixRowClosure
