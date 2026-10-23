import LuRazFullSeeds
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

theorem ARow_low (q : Nat) (hq : 4≤q) (e : Nat) (he : e≤4) : ARow q e ↔ (e=1) := by
  unfold ARow I
  omega

theorem FixedAug.memA {q : Nat} {R : Nat → Prop} {u v c d f z k1 k2 : Prop} {e : Nat}
    (hf : u) (he : ARow q e) : FixedAug q R u v c d f z k1 k2 e := by
  simp only [FixedAug,hf,true_and,he,true_or,or_true]

theorem BRow_low (q : Nat) (hq : 4≤q) (e : Nat) (he : e≤4) : BRow q e ↔ (False) := by
  unfold BRow I
  simp only [iff_false]
  omega

theorem FixedAug.memB {q : Nat} {R : Nat → Prop} {u v c d f z k1 k2 : Prop} {e : Nat}
    (hf : v) (he : BRow q e) : FixedAug q R u v c d f z k1 k2 e := by
  simp only [FixedAug,hf,true_and,he,true_or,or_true]

theorem CRow_low (q : Nat) (hq : 4≤q) (e : Nat) (he : e≤4) : CRow q e ↔ (e=3) := by
  unfold CRow I
  omega

theorem FixedAug.memC {q : Nat} {R : Nat → Prop} {u v c d f z k1 k2 : Prop} {e : Nat}
    (hf : c) (he : CRow q e) : FixedAug q R u v c d f z k1 k2 e := by
  simp only [FixedAug,hf,true_and,he,true_or,or_true]

theorem DRow_low (q : Nat) (hq : 4≤q) (e : Nat) (he : e≤4) : DRow q e ↔ (e=2) := by
  unfold DRow I
  omega

theorem FixedAug.memD {q : Nat} {R : Nat → Prop} {u v c d f z k1 k2 : Prop} {e : Nat}
    (hf : d) (he : DRow q e) : FixedAug q R u v c d f z k1 k2 e := by
  simp only [FixedAug,hf,true_and,he,true_or,or_true]

theorem ERow_low (q : Nat) (hq : 4≤q) (e : Nat) (he : e≤4) : ERow q e ↔ (e=1 ∨ e=3) := by
  unfold ERow I
  omega

theorem FixedAug.memE {q : Nat} {R : Nat → Prop} {u v c d f z k1 k2 : Prop} {e : Nat}
    (hf : f) (he : ERow q e) : FixedAug q R u v c d f z k1 k2 e := by
  simp only [FixedAug,hf,true_and,he,true_or,or_true]

theorem ZRow_low (q : Nat) (hq : 4≤q) (e : Nat) (he : e≤4) : ZRow q e ↔ (e=1 ∨ e=3 ∨ e=4) := by
  unfold ZRow I
  omega

theorem FixedAug.memZ {q : Nat} {R : Nat → Prop} {u v c d f z k1 k2 : Prop} {e : Nat}
    (hf : z) (he : ZRow q e) : FixedAug q R u v c d f z k1 k2 e := by
  simp only [FixedAug,hf,true_and,he,true_or,or_true]

theorem K1Row_low (q : Nat) (hq : 4≤q) (e : Nat) (he : e≤4) : K1Row q e ↔ (e=2 ∨ e=4) := by
  unfold K1Row I
  omega

theorem FixedAug.memK1 {q : Nat} {R : Nat → Prop} {u v c d f z k1 k2 : Prop} {e : Nat}
    (hf : k1) (he : K1Row q e) : FixedAug q R u v c d f z k1 k2 e := by
  simp only [FixedAug,hf,true_and,he,true_or,or_true]

theorem K2Row_low (q : Nat) (hq : 4≤q) (e : Nat) (he : e≤4) : K2Row q e ↔ (e=2 ∨ e=4) := by
  unfold K2Row I
  omega

theorem FixedAug.memK2 {q : Nat} {R : Nat → Prop} {u v c d f z k1 k2 : Prop} {e : Nat}
    (hf : k2) (he : K2Row q e) : FixedAug q R u v c d f z k1 k2 e := by
  simp only [FixedAug,hf,true_and,he,true_or,or_true]

theorem FixedAug.memPickedK {q : Nat} {R : Nat → Prop} {u v c d f z k1 k2 : Prop} {k e : Nat}
    (hsel : ∀ e, KRow q k e → (k1∧K1Row q e) ∨ (k2∧K2Row q e)) (he : KRow q k e) :
    FixedAug q R u v c d f z k1 k2 e := by
  rcases hsel e he with h | h
  · exact FixedAug.memK1 h.1 h.2
  · exact FixedAug.memK2 h.1 h.2

theorem fixedAug_core (q : Nat) (hq : 4≤q) (R : Nat → Prop) (u v c d f z k1 k2 : Prop) :
    CoreFull (FixedAug q R u v c d f z k1 k2) ↔
      (R 1∨u∨f∨z) ∧ (R 2∨d∨k1∨k2) ∧ (R 3∨c∨f∨z) ∧ (R 4∨z∨k1∨k2) := by
  simp (disch := decide) [CoreFull,FixedAug,ARow_low q hq,BRow_low q hq,CRow_low q hq,
    DRow_low q hq,ERow_low q hq,ZRow_low q hq,K1Row_low q hq,K2Row_low q hq,or_assoc]

theorem full_normalizes_from_seed (q : Nat) (hq : 4≤q) (B S : Nat → Prop)
    (u v c d f z k1 k2 : Prop) (hS : FullNormalizes q S)
    (hBS : ∀ e, B e → S e)
    (hSA : ∀ e, S e → FixedAug q B u v c d f z k1 k2 e) :
    FullNormalizes q (FixedAug q B u v c d f z k1 k2) := by
  have h := full_normalizes_fixedAug q hq S hS u v c d f z k1 k2
  apply full_normalizes_congr q _ _ h
  intro e
  constructor
  · rintro (hs | hf)
    · exact hSA e hs
    · exact Or.inr hf
  · rintro (hb | hf)
    · exact Or.inl (hBS e hb)
    · exact Or.inr hf

theorem full_normalizes_fixed_only (q : Nat) (hq : 4≤q) (u v c d f z k1 k2 : Prop)
    (hc : CoreFull (FixedAug q (fun _ => False) u v c d f z k1 k2)) :
    FullNormalizes q (FixedAug q (fun _ => False) u v c d f z k1 k2) := by
  classical
  have hg : (u∨f∨z) ∧ (d∨k1∨k2) ∧ (c∨f∨z) ∧ (z∨k1∨k2) := by
    simpa only [false_or] using (fixedAug_core q hq _ u v c d f z k1 k2).mp hc
  by_cases hz : z
  · by_cases hd : d
    · apply full_normalizes_from_seed q hq _ _ u v c d f z k1 k2 (d_z_full_seed q hq)
      · intro e h; exact False.elim h
      · intro e h; rcases h with h | h
        · exact FixedAug.memD hd h
        · exact FixedAug.memZ hz h
    · have hK : k1∨k2 := by simpa only [hd,false_or] using hg.2.1
      obtain ⟨k,hk,hsel⟩ := pick_K q hq k1 k2 hK
      apply full_normalizes_from_seed q hq _ _ u v c d f z k1 k2 (k_z_full_seed q k hq hk)
      · intro e h; exact False.elim h
      · intro e h; rcases h with h | h
        · exact FixedAug.memPickedK hsel h
        · exact FixedAug.memZ hz h
  · have hK : k1∨k2 := by simpa only [hz,false_or] using hg.2.2.2
    obtain ⟨k,hk,hsel⟩ := pick_K q hq k1 k2 hK
    by_cases hf : f
    · apply full_normalizes_from_seed q hq _ _ u v c d f z k1 k2 (k_e_full_seed q k hq hk)
      · intro e h; exact False.elim h
      · intro e h; rcases h with h | h
        · exact FixedAug.memPickedK hsel h
        · exact FixedAug.memE hf h
    · have hu : u := by simpa only [hf,hz,or_false] using hg.1
      have hC : c := by simpa only [hf,hz,or_false] using hg.2.2.1
      apply full_normalizes_from_seed q hq _ _ u v c d f z k1 k2 (k_c_a_full_seed q k hq hk)
      · intro e h; exact False.elim h
      · intro e h; rcases h with h | h | h
        · exact FixedAug.memPickedK hsel h
        · exact FixedAug.memC hC h
        · exact FixedAug.memA hu h

theorem full_normalizes_lfixed (q t p : Nat) (hq : 4≤q) (ht : P q t) (hp : P q p) (htp : t≤p)
    (u v c d f z k1 k2 : Prop) (hc : CoreFull (FixedAug q (LRow q t p) u v c d f z k1 k2)) :
    FullNormalizes q (FixedAug q (LRow q t p) u v c d f z k1 k2) := by
  classical
  have hb := beta_bounds q t hq ht
  have hl1 : ¬LRow q t p 1 := by unfold LRow LNormal I; omega
  have hl4 : ¬LRow q t p 4 := by unfold LRow LNormal I; omega
  have hcore := (fixedAug_core q hq _ u v c d f z k1 k2).mp hc
  have hg1 : u∨f∨z := by simpa only [hl1,false_or] using hcore.1
  have hg4 : z∨k1∨k2 := by simpa only [hl4,false_or] using hcore.2.2.2
  by_cases hz : z
  · apply full_normalizes_from_seed q hq _ _ u v c d f z k1 k2 (l_z_full_seed q t p hq ht hp htp)
    · intro e h; exact Or.inl h
    · intro e h; rcases h with h | h
      · exact Or.inl h
      · exact FixedAug.memZ hz h
  · have hK : k1∨k2 := by simpa only [hz,false_or] using hg4
    obtain ⟨k,hk,hsel⟩ := pick_K q hq k1 k2 hK
    by_cases hu : u
    · apply full_normalizes_from_seed q hq _ _ u v c d f z k1 k2 (l_k_a_full_seed q t p k hq ht hp htp hk)
      · intro e h; exact Or.inl h
      · intro e h; rcases h with h | h | h
        · exact Or.inl h
        · exact FixedAug.memPickedK hsel h
        · exact FixedAug.memA hu h
    · have hf : f := by simpa only [hu,hz,false_or,or_false] using hg1
      apply full_normalizes_from_seed q hq _ _ u v c d f z k1 k2 (l_k_e_full_seed q t p k hq ht hp htp hk)
      · intro e h; exact Or.inl h
      · intro e h; rcases h with h | h | h
        · exact Or.inl h
        · exact FixedAug.memPickedK hsel h
        · exact FixedAug.memE hf h

theorem full_normalizes_jfixed (q a b : Nat) (hq : 4≤q) (hab : JReachable q a b)
    (u v c d f z k1 k2 : Prop) (hc : CoreFull (FixedAug q (JRow a b) u v c d f z k1 k2)) :
    FullNormalizes q (FixedAug q (JRow a b) u v c d f z k1 k2) := by
  classical
  have hab' := hab
  unfold JReachable at hab'
  have hj2 : ¬JRow a b 2 := by unfold JRow I; omega
  have hj3 : ¬JRow a b 3 := by unfold JRow I; omega
  have hcore := (fixedAug_core q hq _ u v c d f z k1 k2).mp hc
  have hg2 : d∨k1∨k2 := by simpa only [hj2,false_or] using hcore.2.1
  have hg3 : c∨f∨z := by simpa only [hj3,false_or] using hcore.2.2.1
  have hpick : ∃ k, k<2 ∧ ∀ e, KRow q k e → FixedAug q (JRow a b) u v c d f z k1 k2 e := by
    by_cases hd : d
    · refine ⟨0,by decide,?_⟩
      intro e he
      have hkd : JRow a b e ∨ DRow q e := by unfold KRow JRow DRow I at *; omega
      rcases hkd with h | h
      · exact Or.inl h
      · exact FixedAug.memD hd h
    · have hK : k1∨k2 := by simpa only [hd,false_or] using hg2
      obtain ⟨k,hk,hsel⟩ := pick_K q hq k1 k2 hK
      exact ⟨k,hk,fun _ he => FixedAug.memPickedK hsel he⟩
  obtain ⟨k,hk,hsel⟩ := hpick
  rcases hg3 with hC | hE | hZ
  · apply full_normalizes_from_seed q hq _ _ u v c d f z k1 k2 (j_k_c_full_seed q a b k hq hab hk)
    · intro e h; exact Or.inl h
    · intro e h; rcases h with h | h | h
      · exact Or.inl h
      · exact hsel e h
      · exact FixedAug.memC hC h
  · apply full_normalizes_from_seed q hq _ _ u v c d f z k1 k2 (j_k_e_full_seed q a b k hq hab hk)
    · intro e h; exact Or.inl h
    · intro e h; rcases h with h | h | h
      · exact Or.inl h
      · exact hsel e h
      · exact FixedAug.memE hE h
  · apply full_normalizes_from_seed q hq _ _ u v c d f z k1 k2 (j_k_z_full_seed q a b k hq hab hk)
    · intro e h; exact Or.inl h
    · intro e h; rcases h with h | h | h
      · exact Or.inl h
      · exact hsel e h
      · exact FixedAug.memZ hZ h
end LuRazClosure
