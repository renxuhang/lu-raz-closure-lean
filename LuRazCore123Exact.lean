import LuRazCore123Normal
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem NF123.generated (q : Nat) (hq : 4≤q) (z : NF123) (hz : z.Valid q) : Generated q (z.eval q) := by
  have hp4 : P q 4 := by unfold P; omega
  cases z with
  | low t =>
    have htBounds : 4≤t ∧ t≤q+1 := hz
    have ht : P q t := by have hb : 4≤t ∧ t≤q+1 := hz; unfold P; omega
    have hg := image123_generated q hq (.lp t t) (⟨ht,ht,by omega⟩) True False
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or,or_false]
    repeat first | omega | (simp_all <;> omega) | split
  | high t p =>
    have hb : P q t ∧ P q p ∧ q+3≤p ∧ t≤p := hz
    have hp := hb.2.1
    have hp' := hp
    unfold P at hp'
    have hg := image123_generated q hq (.lp t p) (⟨hb.1,hp,hb.2.2.2⟩) True False
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or,or_false]
    repeat first | omega | (simp_all <;> omega) | split
  | filled =>
    have hg := image123_generated q hq (.filledM) (True.intro) True False
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or,or_false]
    repeat first | omega | (simp_all <;> omega) | split
  | full =>
    have hg := image123_generated q hq (.full) (True.intro) True False
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or,or_false]
    repeat first | omega | (simp_all <;> omega) | split
  | creg t =>
    have hg := image123_generated q hq (.creg t) (hz) True False
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or,or_false]
    repeat first | omega | (simp_all <;> omega) | split
  | cex =>
    have hg := image123_generated q hq (.cexception) (True.intro) True False
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or,or_false]
    repeat first | omega | (simp_all <;> omega) | split
  | dg p =>
    have hb : q+2≤p ∧ p≤2*q-1 := hz
    by_cases he : p=q+2
    · have hg := image123_generated q hq (.dgap 4) ⟨hp4,by omega⟩ True False
      apply generated_congr q hg
      intro e
      simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,TwoPiece,I,true_and,false_and,or_false]
      omega
    · have hp : P q p := by unfold P; omega
      have hg := image123_generated q hq (.dgap p) ⟨hp,hb.2⟩ True False
      apply generated_congr q hg
      intro e
      simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,TwoPiece,I,true_and,false_and,or_false]
      omega
  | er p =>
    have hb : 4≤p ∧ p≤2*q+1 := hz
    by_cases he : p=q+2
    · have hg := image123_generated q hq (.lp 4 4) ⟨hp4,hp4,by omega⟩ True True
      apply generated_congr q hg
      intro e
      simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and]
      repeat first | omega | (simp_all <;> omega) | split
    · have hp : P q p := by unfold P; omega
      have hg := image123_generated q hq (.lp p p) ⟨hp,hp,by omega⟩ False True
      apply generated_congr q hg
      intro e
      simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,LRow,LNormal,I,beta,true_and,false_and,false_or]
      repeat first | omega | (simp_all <;> omega) | split
  | ed p =>
    have hb : 4≤p ∧ p≤q+1 := hz
    have hp : P q p := by unfold P; omega
    have hg := image123_generated q hq (.dgap p) ⟨hp,by omega⟩ False True
    apply generated_congr q hg
    intro e
    simp only [Image123,NF123.eval,NF123.body,NF23.eval,ARow,ERow,TwoPiece,I,true_and,false_and,false_or]
    omega

theorem NF123.body_no_one (q : Nat) (hq : 4≤q) (z : NF123) (hz : z.Valid q) : ¬z.body q 1 := by
  cases z <;> simp only [NF123.Valid,P] at hz <;>
    simp only [NF123.body,NF23.eval,LRow,LNormal,TwoPiece,I,beta] <;>
    repeat first | omega | (simp_all <;> omega) | split

theorem NF123.core (q : Nat) (hq : 4≤q) (z : NF123) (hz : z.Valid q) : Core123 (z.eval q) := by
  cases z <;> simp only [NF123.Valid,P] at hz <;>
    simp only [Core123,NF123.eval,NF123.body,NF23.eval,LRow,LNormal,TwoPiece,I,beta] <;>
    repeat first | omega | (simp_all <;> omega) | split

theorem core123_closure_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ Core123 R ↔ ∃ z : NF123, z.Valid q ∧ ∀ e, R e ↔ z.eval q e := by
  constructor
  · rintro ⟨hg,hc⟩
    obtain ⟨z,hz,a,f,hA,he⟩ := core123_image q hq R hg hc
    obtain ⟨w,hw,hn⟩ := image123_normal q hq z hz a f hA
    exact ⟨w,hw,fun e => (he e).trans (hn e)⟩
  · rintro ⟨z,hz,he⟩
    refine ⟨generated_congr q (NF123.generated q hq z hz) (fun e => (he e).symm),?_⟩
    have hc := NF123.core q hq z hz
    unfold Core123 at hc ⊢
    exact ⟨(he 1).mpr hc.1,(he 2).mpr hc.2.1,(he 3).mpr hc.2.2.1,fun h => hc.2.2.2 ((he 4).mp h)⟩
end LuRazClosure
