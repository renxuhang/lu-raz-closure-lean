import LuRazFullNormal
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The four-endpoint J/L interaction, preserving the exceptional missing last point. -/
theorem lp_j_full_normal (q t p a b : Nat) (hq : 4≤q)
    (ht : P q t) (hp : P q p) (htp : t≤p) (hab : JReachable q a b) :
    ∃ w : NFFull, w.Valid q ∧
      ∀ e, (LRow q t p e ∨ JRow a b e) ↔ w.eval q e := by
  have ht' := ht
  have hp' := hp
  have hab' := hab
  unfold P at ht' hp'
  unfold JReachable at hab'
  have hbt := beta_bounds q t hq ht
  have hbp := beta_bounds q p hq hp
  have hmon : beta q t≤beta q p := by
    by_cases he : t=p
    · rw [he]
      exact Nat.le_refl _
    · have hs := beta_strict q t p hq ht hp (by omega)
      omega
  have hgapjoin : p+2≤a → beta q t≤b+1 := by
    intro hgap
    have hs := no_two_gaps q p a hq hp ⟨hab.1,hab.2.1⟩ hgap
    omega
  by_cases hm : t=q+3 ∧ p=q+3
  · have hend : (if t=q+3 ∧ p=q+3 then 4*q-1 else 4*q)=4*q-1 := if_pos hm
    have hbeta : beta q t=3*q+2 := by rw [hm.1,beta_exception q hq]
    by_cases hl : a≤p+1
    · by_cases hr : beta q t≤b+1
      · refine ⟨.noNInterval 1,by simp [NFFull.Valid],?_⟩
        intro e
        simp only [LRow,LNormal,JRow,hend,hbeta,NFFull.eval,FullHead,I]
        omega
      · refine ⟨.noNMJRight b,by change 2*q+2≤b ∧ b≤3*q; omega,?_⟩
        intro e
        simp only [LRow,LNormal,JRow,hend,hbeta,NFFull.eval,FullHead,I]
        omega
    · have hjoin := hgapjoin (by omega)
      refine ⟨.noNMJLeft a,by change q+5≤a ∧ a≤2*q+1; omega,?_⟩
      intro e
      simp only [LRow,LNormal,JRow,hend,hbeta,NFFull.eval,FullHead,I]
      omega
  · have hend : (if t=q+3 ∧ p=q+3 then 4*q-1 else 4*q)=4*q := if_neg hm
    by_cases hl : a≤p+1
    · by_cases hr : beta q t≤b+1
      · refine ⟨.full,True.intro,?_⟩
        intro e
        simp only [LRow,LNormal,JRow,hend,NFFull.eval,FullHead,I]
        omega
      · refine ⟨.rightGap b (beta q t),by change (2*q+2≤b ∧ b≤4*q-2) ∧ b+2≤beta q t ∧ beta q t≤4*q; omega,?_⟩
        intro e
        simp only [LRow,LNormal,JRow,hend,NFFull.eval,FullHead,I]
        omega
    · have hjoin := hgapjoin (by omega)
      by_cases hp4 : p=4
      · refine ⟨.noFive a,by change 6≤a ∧ a≤2*q+1; omega,?_⟩
        intro e
        simp only [LRow,LNormal,JRow,hend,NFFull.eval,FullHead,I]
        omega
      · refine ⟨.leftGap p a,by change (5≤p ∧ p≤2*q-1) ∧ p+2≤a ∧ a≤2*q+1; omega,?_⟩
        intro e
        simp only [LRow,LNormal,JRow,hend,NFFull.eval,FullHead,I]
        omega
end LuRazClosure
