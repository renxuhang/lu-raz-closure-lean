import LuRazFullAugment
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def KRow (q k e : Nat) : Prop := e=2 ∨ e=4 ∨ I (2*q+2+k) (4*q-2+k) e

theorem KRow_zero (q e : Nat) : KRow q 0 e ↔ K1Row q e := by simp [KRow,K1Row]
theorem KRow_one (q e : Nat) (hq : 4≤q) : KRow q 1 e ↔ K2Row q e := by unfold KRow K2Row I; omega

theorem pick_K (q : Nat) (hq : 4≤q) (k1 k2 : Prop) (hK : k1∨k2) :
    ∃ k, k<2 ∧ ∀ e, KRow q k e → (k1∧K1Row q e) ∨ (k2∧K2Row q e) := by
  rcases hK with h | h
  · exact ⟨0,by decide,fun e he => Or.inl ⟨h,(KRow_zero q e).mp he⟩⟩
  · exact ⟨1,by decide,fun e he => Or.inr ⟨h,(KRow_one q e hq).mp he⟩⟩

theorem l_z_full_seed (q t p : Nat) (hq : 4≤q) (ht : P q t) (hp : P q p) (htp : t≤p) :
    FullNormalizes q (fun e => LRow q t p e ∨ ZRow q e) := by
  have ht' := ht
  have hp' := hp
  unfold P at ht' hp'
  have hb := beta_bounds q t hq ht
  by_cases hl : p≤2*q
  · have ha : beta q t≤4*q-1 := by
      unfold beta
      split <;> omega
    refine ⟨.noH1ZL (beta q t),by change 2*q+4≤beta q t ∧ beta q t≤4*q-1; omega,?_⟩
    intro e
    simp only [LRow,LNormal,ZRow,NFFull.eval,FullHead,I]
    split <;> omega
  · refine ⟨.noH2 (beta q t),by change 2*q+3≤beta q t ∧ beta q t≤4*q; omega,?_⟩
    intro e
    simp only [LRow,LNormal,ZRow,NFFull.eval,FullHead,I]
    split <;> omega

theorem l_k_e_full_seed (q t p k : Nat) (hq : 4≤q) (ht : P q t) (hp : P q p)
    (htp : t≤p) (hk : k<2) :
    FullNormalizes q (fun e => LRow q t p e ∨ KRow q k e ∨ ERow q e) := by
  have ht' := ht
  have hp' := hp
  unfold P at ht' hp'
  have hb := beta_bounds q t hq ht
  by_cases hl : p≤2*q
  · refine ⟨.noH1Short p k,by change (4≤p ∧ p≤2*q) ∧ k<2; omega,?_⟩
    intro e
    simp only [LRow,LNormal,KRow,ERow,NFFull.eval,FullHead,I]
    split <;> omega
  · by_cases hk0 : k=0
    · refine ⟨.full,True.intro,?_⟩
      intro e
      simp only [LRow,LNormal,KRow,ERow,NFFull.eval,FullHead,I]
      split <;> omega
    · refine ⟨.noH2 (2*q+3),by change 2*q+3≤2*q+3 ∧ 2*q+3≤4*q; omega,?_⟩
      intro e
      simp only [LRow,LNormal,KRow,ERow,NFFull.eval,FullHead,I]
      split <;> omega

theorem l_k_a_full_seed (q t p k : Nat) (hq : 4≤q) (ht : P q t) (hp : P q p)
    (htp : t≤p) (hk : k<2) :
    FullNormalizes q (fun e => LRow q t p e ∨ KRow q k e ∨ ARow q e) := by
  have hg : k=0 ∨ k=1 := by omega
  obtain ⟨z,hz,he⟩ := mixed234_normal q t p hq ht hp htp False False False (k=0) (k=1) hg
  obtain ⟨w,hw,hn⟩ := a234_full_normal q hq z hz False
  refine ⟨w,hw,?_⟩
  intro e
  have hm : (LRow q t p e ∨ KRow q k e) ↔ z.eval q e := by
    rw [←he e]
    have hke : KRow q k e ↔ (k=0∧K1Row q e) ∨ (k=1∧K2Row q e) := by
      rcases hg with h | h <;> subst k <;>
        simp only [KRow,K1Row,K2Row,true_and,false_and,false_or,or_false,I] <;> omega
    simp only [Mixed234,Fixed234,false_and,false_or,or_false]
    exact or_congr Iff.rfl hke
  simp only [false_and,or_false] at hn
  simpa only [or_assoc] using (or_congr hm Iff.rfl).trans (hn e)

theorem j_k_c_full_seed (q a b k : Nat) (hq : 4≤q) (hab : JReachable q a b) (hk : k<2) :
    FullNormalizes q (fun e => JRow a b e ∨ KRow q k e ∨ CRow q e) := by
  have hab' := hab
  unfold JReachable at hab'
  refine ⟨.noNInterval k,hk,?_⟩
  intro e
  simp only [JRow,KRow,CRow,ZRow,ERow,NFFull.eval,FullHead,I]
  omega

theorem j_k_z_full_seed (q a b k : Nat) (hq : 4≤q) (hab : JReachable q a b) (hk : k<2) :
    FullNormalizes q (fun e => JRow a b e ∨ KRow q k e ∨ ZRow q e) := by
  have hab' := hab
  unfold JReachable at hab'
  by_cases hk0 : k=0
  · refine ⟨.rightGap (4*q-2) (4*q),by simp only [NFFull.Valid]; omega,?_⟩
    intro e
    simp only [JRow,KRow,CRow,ZRow,ERow,NFFull.eval,FullHead,I]
    omega
  · refine ⟨.full,True.intro,?_⟩
    intro e
    simp only [JRow,KRow,CRow,ZRow,ERow,NFFull.eval,FullHead,I]
    omega

theorem j_k_e_full_seed (q a b k : Nat) (hq : 4≤q) (hab : JReachable q a b) (hk : k<2) :
    FullNormalizes q (fun e => JRow a b e ∨ KRow q k e ∨ ERow q e) := by
  have hab' := hab
  unfold JReachable at hab'
  by_cases ha : a=5
  · refine ⟨.full,True.intro,?_⟩
    intro e
    simp only [JRow,KRow,CRow,ZRow,ERow,NFFull.eval,FullHead,I]
    omega
  · refine ⟨.noFive a,by simp only [NFFull.Valid]; omega,?_⟩
    intro e
    simp only [JRow,KRow,CRow,ZRow,ERow,NFFull.eval,FullHead,I]
    omega

theorem k_z_full_seed (q k : Nat) (hq : 4≤q) (hk : k<2) :
    FullNormalizes q (fun e => KRow q k e ∨ ZRow q e) := by
  by_cases hk0 : k=0
  · refine ⟨.noH1Exception,True.intro,?_⟩
    intro e
    simp only [KRow,ZRow,NFFull.eval,FullHead,I]
    omega
  · refine ⟨.noH1Short (2*q) 1,by simp only [NFFull.Valid]; omega,?_⟩
    intro e
    simp only [KRow,ZRow,NFFull.eval,FullHead,I]
    omega

theorem k_e_full_seed (q k : Nat) (hq : 4≤q) (hk : k<2) :
    FullNormalizes q (fun e => KRow q k e ∨ ERow q e) := by
  refine ⟨.noH1Short 4 k,by simp only [NFFull.Valid]; omega,?_⟩
  intro e
  simp only [KRow,ERow,NFFull.eval,FullHead,I]
  omega

theorem k_c_a_full_seed (q k : Nat) (hq : 4≤q) (hk : k<2) :
    FullNormalizes q (fun e => KRow q k e ∨ CRow q e ∨ ARow q e) := by
  refine ⟨.noNInterval k,hk,?_⟩
  intro e
  simp only [KRow,CRow,ARow,NFFull.eval,FullHead,I]
  omega

theorem d_z_full_seed (q : Nat) (hq : 4≤q) :
    FullNormalizes q (fun e => DRow q e ∨ ZRow q e) := by
  refine ⟨.full,True.intro,?_⟩
  intro e
  simp only [DRow,ZRow,NFFull.eval,FullHead,I]
  omega
end LuRazClosure
