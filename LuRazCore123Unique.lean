import LuRazCore123Exact
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem NF123.unique (q : Nat) (hq : 4≤q) (z w : NF123)
    (hz : z.Valid q) (hw : w.Valid q) (heq : ∀ e, z.eval q e ↔ w.eval q e) : z=w := by
  have hnz := NF123.body_no_one q hq z hz
  have hnw := NF123.body_no_one q hq w hw
  have he : ∀ e, z.body q e ↔ w.body q e := by
    intro e
    by_cases h : e=1
    · subst e; simp only [hnz,hnw]
    · simpa only [NF123.eval,h,false_or] using heq e
  cases z with
  | low t =>
    cases w with
    | low s =>
      simp only [NF123.Valid] at hz hw
      have hpt : P q t := by unfold P; omega
      have hbt := beta_bounds q t hq hpt
      have hps : P q s := by unfold P; omega
      have hbs := beta_bounds q s hq hps
      have h := twoPiece_unique q (q+2) (beta q t) (4*q) (q+2) (beta q s) (4*q)
        (by omega) (by omega) hbt hbs he
      have hts := beta_injective q t s hq hpt hps h.2.1
      subst s; rfl
    | high s r =>
      simp only [NF123.Valid] at hz hw
      have hpt : P q t := by unfold P; omega
      have hbt := beta_bounds q t hq hpt
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | filled  =>
      simp only [NF123.Valid] at hz hw
      have hpt : P q t := by unfold P; omega
      have hbt := beta_bounds q t hq hpt
      try simp only [P] at hz hw
      have h0 := he (q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | dg r =>
      simp only [NF123.Valid] at hz hw
      have hpt : P q t := by unfold P; omega
      have hbt := beta_bounds q t hq hpt
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NF123.Valid] at hz hw
      have hpt : P q t := by unfold P; omega
      have hbt := beta_bounds q t hq hpt
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | creg s =>
      simp only [NF123.Valid] at hz hw
      have hpt : P q t := by unfold P; omega
      have hbt := beta_bounds q t hq hpt
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cex  =>
      simp only [NF123.Valid] at hz hw
      have hpt : P q t := by unfold P; omega
      have hbt := beta_bounds q t hq hpt
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | er r =>
      simp only [NF123.Valid] at hz hw
      have hpt : P q t := by unfold P; omega
      have hbt := beta_bounds q t hq hpt
      try simp only [P] at hz hw
      have h0 := he (2*q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | ed r =>
      simp only [NF123.Valid] at hz hw
      have hpt : P q t := by unfold P; omega
      have hbt := beta_bounds q t hq hpt
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | high t p =>
    cases w with
    | low s =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      have hps : P q s := by unfold P; omega
      have hbs := beta_bounds q s hq hps
      try simp only [P] at hz hw
      have h0 := he (q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | high s r =>
      simp only [NF123.Valid] at hz hw
      have h := lp_unique q t p s r hq ⟨hz.1,hz.2.1,hz.2.2.2⟩ ⟨hw.1,hw.2.1,hw.2.2.2⟩ he
      rcases h with ⟨h1,h2⟩
      subst s; subst r; rfl
    | filled  =>
      simp only [NF123.Valid] at hz hw
      exact False.elim (lp_ne_filled q t p hq ⟨hz.1,hz.2.1,hz.2.2.2⟩ he)
    | dg r =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | creg s =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cex  =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | er r =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      try simp only [P] at hz hw
      have h0 := he (2*q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | ed r =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | filled  =>
    cases w with
    | low s =>
      simp only [NF123.Valid] at hz hw
      have hps : P q s := by unfold P; omega
      have hbs := beta_bounds q s hq hps
      try simp only [P] at hz hw
      have h0 := he (q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | high s r =>
      simp only [NF123.Valid] at hz hw
      exact False.elim (lp_ne_filled q s r hq ⟨hw.1,hw.2.1,hw.2.2.2⟩ (fun e => (he e).symm))
    | filled  =>
      rfl
    | dg r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | creg s =>
      simp only [NF123.Valid] at hz hw
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cex  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | er r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | ed r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | dg p =>
    cases w with
    | low s =>
      simp only [NF123.Valid] at hz hw
      have hps : P q s := by unfold P; omega
      have hbs := beta_bounds q s hq hps
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | high s r =>
      simp only [NF123.Valid] at hz hw
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | filled  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | dg r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (p+1)
      have h1 := he (r+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have hpr : p=r := by omega
      subst r; rfl
    | full  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | creg s =>
      simp only [NF123.Valid] at hz hw
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (2*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cex  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | er r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      have h1 := he (2*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      exfalso
      omega
    | ed r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | full  =>
    cases w with
    | low s =>
      simp only [NF123.Valid] at hz hw
      have hps : P q s := by unfold P; omega
      have hbs := beta_bounds q s hq hps
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | high s r =>
      simp only [NF123.Valid] at hz hw
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | filled  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | dg r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      rfl
    | creg s =>
      simp only [NF123.Valid] at hz hw
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (2*q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cex  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | er r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | ed r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | creg t =>
    cases w with
    | low s =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      have hps : P q s := by unfold P; omega
      have hbs := beta_bounds q s hq hps
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | high s r =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | filled  =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | dg r =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      try simp only [P] at hz hw
      have h0 := he (2*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      try simp only [P] at hz hw
      have h0 := he (2*q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | creg s =>
      simp only [NF123.Valid] at hz hw
      have h := creg_unique q t s hq hz hw he
      subst s; rfl
    | cex  =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      try simp only [P] at hz hw
      have h0 := he (4*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | er r =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | ed r =>
      simp only [NF123.Valid] at hz hw
      have hbt := beta_bounds q t hq hz.1
      try simp only [P] at hz hw
      have h0 := he (2*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | cex  =>
    cases w with
    | low s =>
      simp only [NF123.Valid] at hz hw
      have hps : P q s := by unfold P; omega
      have hbs := beta_bounds q s hq hps
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | high s r =>
      simp only [NF123.Valid] at hz hw
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | filled  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | dg r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | creg s =>
      simp only [NF123.Valid] at hz hw
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (4*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cex  =>
      rfl
    | er r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (4*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | ed r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (4*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | er p =>
    cases w with
    | low s =>
      simp only [NF123.Valid] at hz hw
      have hps : P q s := by unfold P; omega
      have hbs := beta_bounds q s hq hps
      try simp only [P] at hz hw
      have h0 := he (2*q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | high s r =>
      simp only [NF123.Valid] at hz hw
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (2*q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | filled  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+3)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | dg r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      have h1 := he (2*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      exfalso
      omega
    | full  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | creg s =>
      simp only [NF123.Valid] at hz hw
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cex  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (4*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | er r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (p+1)
      have h1 := he (r+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have hpr : p=r := by omega
      subst r; rfl
    | ed r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
  | ed p =>
    cases w with
    | low s =>
      simp only [NF123.Valid] at hz hw
      have hps : P q s := by unfold P; omega
      have hbs := beta_bounds q s hq hps
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | high s r =>
      simp only [NF123.Valid] at hz hw
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | filled  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | dg r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | full  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | creg s =>
      simp only [NF123.Valid] at hz hw
      have hbs := beta_bounds q s hq hw.1
      try simp only [P] at hz hw
      have h0 := he (2*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | cex  =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (4*q)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | er r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (2*q+2)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0
      exfalso
      omega
    | ed r =>
      simp only [NF123.Valid] at hz hw
      try simp only [P] at hz hw
      have h0 := he (p+1)
      have h1 := he (r+1)
      simp only [NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I,true_or,or_true,false_or,or_false,iff_true,true_iff,iff_false,false_iff] at h0 h1
      have hpr : p=r := by omega
      subst r; rfl
end LuRazClosure
