import LuRazSmallBase
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

inductive NFSmall where
  | bOnly
  | aOnly
  | ab
  | dOnly
  | ad
  | cOnly
  | cb
  | eOnly
  | ae
  | ce
  | ac
  | acb
  deriving DecidableEq, Repr

def NFSmall.tag : NFSmall → Nat
  | .bOnly => 0
  | .aOnly => 1
  | .ab => 1
  | .dOnly => 2
  | .ad => 3
  | .cOnly => 4
  | .cb => 4
  | .eOnly => 5
  | .ae => 5
  | .ce => 5
  | .ac => 5
  | .acb => 5

def NFSmall.eval (q : Nat) : NFSmall → Nat → Prop
  | .bOnly => BRow q
  | .aOnly => ARow q
  | .ab => fun e => ARow q e ∨ BRow q e
  | .dOnly => DRow q
  | .ad => fun e => ARow q e ∨ DRow q e
  | .cOnly => CRow q
  | .cb => fun e => CRow q e ∨ BRow q e
  | .eOnly => ERow q
  | .ae => fun e => ARow q e ∨ ERow q e
  | .ce => fun e => CRow q e ∨ ERow q e
  | .ac => fun e => ARow q e ∨ CRow q e
  | .acb => fun e => ARow q e ∨ CRow q e ∨ BRow q e

def CoreSmallAt (k : Nat) (R : Nat → Prop) : Prop := k≤5 ∧
  (R 1 ↔ k=1 ∨ k=3 ∨ k=5) ∧ (R 2 ↔ k=2 ∨ k=3) ∧ (R 3 ↔ k=4 ∨ k=5) ∧ ¬R 4

theorem coreSmallAt_congr (k : Nat) (R T : Nat → Prop) (he : ∀ e, R e ↔ T e) :
    CoreSmallAt k R ↔ CoreSmallAt k T := by
  unfold CoreSmallAt
  rw [he 1,he 2,he 3,he 4]

theorem coreSmallAt_unique (k j : Nat) (R : Nat → Prop)
    (hk : CoreSmallAt k R) (hj : CoreSmallAt j R) : k=j := by
  have h1 := hk.2.1.symm.trans hj.2.1
  have h2 := hk.2.2.1.symm.trans hj.2.2.1
  have h3 := hk.2.2.2.1.symm.trans hj.2.2.2.1
  have hk5 := hk.1
  have hj5 := hj.1
  omega

theorem coreSmallAt_small (k : Nat) (R : Nat → Prop) (h : CoreSmallAt k R) : SmallCore R := by
  refine ⟨h.2.2.2.2,?_⟩
  rintro ⟨h2,h3⟩
  have h2k := h.2.2.1.mp h2
  have h3k := h.2.2.2.1.mp h3
  omega

theorem small_guard (q : Nat) (a b c d f : Prop)
    (h : SmallCore (SmallMix q a b c d f)) : ¬((c ∨ f) ∧ d) := by
  rintro ⟨h3,hd⟩
  apply h.2
  constructor
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hd,Or.inl rfl⟩)))
  · rcases h3 with hc | hf
    · exact Or.inr (Or.inr (Or.inl ⟨hc,Or.inl rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hf,Or.inr (Or.inl rfl)⟩)))

theorem small_normal (q : Nat) (hq : 4≤q) (a b c d f : Prop)
    (hne : a ∨ b ∨ c ∨ d ∨ f) (hc : SmallCore (SmallMix q a b c d f)) :
    ∃ z : NFSmall, ∀ e, SmallMix q a b c d f e ↔ z.eval q e := by
  classical
  have hg := small_guard q a b c d f hc
  by_cases hd : d
  · have hnc : ¬c := fun h => hg ⟨Or.inl h,hd⟩
    have hnf : ¬f := fun h => hg ⟨Or.inr h,hd⟩
    by_cases ha : a
    · refine ⟨.ad,?_⟩
      intro e
      simp only [SmallMix,NFSmall.eval,hd,hnc,hnf,ha,true_and,false_and,false_or,or_false] <;>
        (simp only [ARow,BRow,CRow,DRow,ERow,I] <;> omega)
    · refine ⟨.dOnly,?_⟩
      intro e
      simp only [SmallMix,NFSmall.eval,hd,hnc,hnf,ha,true_and,false_and,false_or,or_false] <;>
        (simp only [ARow,BRow,CRow,DRow,ERow,I] <;> omega)
  · by_cases hf : f
    · by_cases hcc : c
      · refine ⟨.ce,?_⟩
        intro e
        simp only [SmallMix,NFSmall.eval,hd,hf,hcc,true_and,false_and,false_or,or_false] <;>
          (simp only [ARow,BRow,CRow,DRow,ERow,I] <;> omega)
      · by_cases ha : a
        · refine ⟨.ae,?_⟩
          intro e
          simp only [SmallMix,NFSmall.eval,hd,hf,hcc,ha,true_and,false_and,false_or,or_false] <;>
            (simp only [ARow,BRow,CRow,DRow,ERow,I] <;> omega)
        · refine ⟨.eOnly,?_⟩
          intro e
          simp only [SmallMix,NFSmall.eval,hd,hf,hcc,ha,true_and,false_and,false_or,or_false] <;>
            (simp only [ARow,BRow,CRow,DRow,ERow,I] <;> omega)
    · by_cases hcc : c
      · by_cases ha : a
        · by_cases hb : b
          · refine ⟨.acb,?_⟩
            intro e
            simp only [SmallMix,NFSmall.eval,hd,hf,hcc,ha,hb,true_and,false_and,false_or,or_false] <;>
              (simp only [ARow,BRow,CRow,DRow,ERow,I] <;> omega)
          · refine ⟨.ac,?_⟩
            intro e
            simp only [SmallMix,NFSmall.eval,hd,hf,hcc,ha,hb,true_and,false_and,false_or,or_false] <;>
              (simp only [ARow,BRow,CRow,DRow,ERow,I] <;> omega)
        · by_cases hb : b
          · refine ⟨.cb,?_⟩
            intro e
            simp only [SmallMix,NFSmall.eval,hd,hf,hcc,ha,hb,true_and,false_and,false_or,or_false] <;>
              (simp only [ARow,BRow,CRow,DRow,ERow,I] <;> omega)
          · refine ⟨.cOnly,?_⟩
            intro e
            simp only [SmallMix,NFSmall.eval,hd,hf,hcc,ha,hb,true_and,false_and,false_or,or_false] <;>
              (simp only [ARow,BRow,CRow,DRow,ERow,I] <;> omega)
      · by_cases ha : a
        · by_cases hb : b
          · refine ⟨.ab,?_⟩
            intro e
            simp only [SmallMix,NFSmall.eval,hd,hf,hcc,ha,hb,true_and,false_and,false_or,or_false] <;>
              (simp only [ARow,BRow,CRow,DRow,ERow,I] <;> omega)
          · refine ⟨.aOnly,?_⟩
            intro e
            simp only [SmallMix,NFSmall.eval,hd,hf,hcc,ha,hb,true_and,false_and,false_or,or_false] <;>
              (simp only [ARow,BRow,CRow,DRow,ERow,I] <;> omega)
        · have hb : b := by
            rcases hne with h | h | h | h | h
            · exact False.elim (ha h)
            · exact h
            · exact False.elim (hcc h)
            · exact False.elim (hd h)
            · exact False.elim (hf h)
          refine ⟨.bOnly,?_⟩
          intro e
          simp only [SmallMix,NFSmall.eval,hd,hf,hcc,ha,hb,true_and,false_and,false_or,or_false] <;>
            (simp only [ARow,BRow,CRow,DRow,ERow,I] <;> omega)

theorem NFSmall.generated (q : Nat) (hq : 4≤q) (z : NFSmall) : Generated q (z.eval q) := by
  cases z with
  | bOnly => exact generated_B q hq
  | aOnly => exact generated_A q hq
  | ab => exact generated_join q (generated_A q hq) (generated_B q hq)
  | dOnly => exact generated_D q hq
  | ad => exact generated_join q (generated_A q hq) (generated_D q hq)
  | cOnly => exact generated_C q hq
  | cb => exact generated_join q (generated_C q hq) (generated_B q hq)
  | eOnly => exact generated_E q hq
  | ae => exact generated_join q (generated_A q hq) (generated_E q hq)
  | ce => exact generated_join q (generated_C q hq) (generated_E q hq)
  | ac => exact generated_join q (generated_A q hq) (generated_C q hq)
  | acb => exact generated_join q (generated_A q hq) (generated_join q (generated_C q hq) (generated_B q hq))

theorem NFSmall.core (q : Nat) (hq : 4≤q) (z : NFSmall) : CoreSmallAt z.tag (z.eval q) := by
  cases z <;> simp only [CoreSmallAt,NFSmall.tag,NFSmall.eval,ARow,BRow,CRow,DRow,ERow,I] <;>
    (simp_all <;> omega)

theorem small_closure_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    (Generated q R ∧ SmallCore R) ↔ ∃ z : NFSmall, ∀ e, R e ↔ z.eval q e := by
  constructor
  · rintro ⟨hg,hc⟩
    obtain ⟨a,b,c,d,f,hne,heq⟩ := small_mix_of_generated q hq R hg hc
    have hm : SmallCore (SmallMix q a b c d f) := by
      unfold SmallCore at *
      rw [←heq 4,←heq 2,←heq 3]
      exact hc
    obtain ⟨z,hz⟩ := small_normal q hq a b c d f hne hm
    exact ⟨z,fun e => (heq e).trans (hz e)⟩
  · rintro ⟨z,heq⟩
    have hc := (coreSmallAt_congr z.tag R (z.eval q) heq).mpr (NFSmall.core q hq z)
    exact ⟨generated_congr q (NFSmall.generated q hq z) (fun e => (heq e).symm),coreSmallAt_small z.tag R hc⟩

end LuRazClosure
