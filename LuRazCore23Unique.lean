import LuRazCore23Recovery
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem NF23.unique (q : Nat) (hq : 4≤q) (z w : NF23)
    (hz : z.Valid q) (hw : w.Valid q) (heq : ∀ e, z.eval q e ↔ w.eval q e) : z=w := by
  cases z with
  | lp t p =>
    have hzb : (4≤t ∧ t≤2*q+1 ∧ t≠q+2) ∧ (4≤p ∧ p≤2*q+1 ∧ p≠q+2) ∧ t≤p := hz
    have hzbeta := beta_bounds q t hq hz.1
    cases w with
    | lp s r =>
      have hwb : (4≤s ∧ s≤2*q+1 ∧ s≠q+2) ∧ (4≤r ∧ r≤2*q+1 ∧ r≠q+2) ∧ s≤r := hw
      have hwbeta := beta_bounds q s hq hw.1
      obtain ⟨hts,hpr⟩ := lp_unique q t p s r hq hz hw heq
      subst s; subst r; rfl
    | filledM  =>
      exact False.elim (lp_ne_filled q t p hq hz heq)
    | dgap r =>
      have hwb : (4≤r ∧ r≤2*q+1 ∧ r≠q+2) ∧ r≤2*q-1 := hw
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤p) ∨ ((beta q t)≤(2*q+2) ∧ (2*q+2)≤(if t=q+3 ∧ p=q+3 then 4*q-1 else 4*q))) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤r) ∨ (2*q+1≤(2*q+2) ∧ (2*q+2)≤4*q)) at h0
      exfalso
      omega
    | full  =>
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤p) ∨ ((beta q t)≤(2*q+2) ∧ (2*q+2)≤(if t=q+3 ∧ p=q+3 then 4*q-1 else 4*q))) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤4*q)) at h0
      exfalso
      omega
    | creg s =>
      have hwb : (4≤s ∧ s≤2*q+1 ∧ s≠q+2) ∧ s≠q+3 := hw
      have hwbeta := beta_bounds q s hq hw.1
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤p) ∨ ((beta q t)≤(2*q+2) ∧ (2*q+2)≤(if t=q+3 ∧ p=q+3 then 4*q-1 else 4*q))) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤2*q+2) ∨ (2*q+2)=3*q+1 ∨ ((beta q s)≤(2*q+2) ∧ (2*q+2)≤4*q)) at h0
      exfalso
      omega
    | cexception  =>
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤p) ∨ ((beta q t)≤(2*q+2) ∧ (2*q+2)≤(if t=q+3 ∧ p=q+3 then 4*q-1 else 4*q))) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤2*q+2) ∨ (3*q+1≤(2*q+2) ∧ (2*q+2)≤4*q-1)) at h0
      exfalso
      omega
  | filledM  =>
    cases w with
    | lp s r =>
      have hwb : (4≤s ∧ s≤2*q+1 ∧ s≠q+2) ∧ (4≤r ∧ r≤2*q+1 ∧ r≠q+2) ∧ s≤r := hw
      have hwbeta := beta_bounds q s hq hw.1
      exact False.elim (lp_ne_filled q s r hq hw (fun e => (heq e).symm))
    | filledM  =>
      rfl
    | dgap r =>
      have hwb : (4≤r ∧ r≤2*q+1 ∧ r≠q+2) ∧ r≤2*q-1 := hw
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤q+3) ∨ (3*q+2≤(2*q+2) ∧ (2*q+2)≤4*q)) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤r) ∨ (2*q+1≤(2*q+2) ∧ (2*q+2)≤4*q)) at h0
      exfalso
      omega
    | full  =>
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤q+3) ∨ (3*q+2≤(2*q+2) ∧ (2*q+2)≤4*q)) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤4*q)) at h0
      exfalso
      omega
    | creg s =>
      have hwb : (4≤s ∧ s≤2*q+1 ∧ s≠q+2) ∧ s≠q+3 := hw
      have hwbeta := beta_bounds q s hq hw.1
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤q+3) ∨ (3*q+2≤(2*q+2) ∧ (2*q+2)≤4*q)) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤2*q+2) ∨ (2*q+2)=3*q+1 ∨ ((beta q s)≤(2*q+2) ∧ (2*q+2)≤4*q)) at h0
      exfalso
      omega
    | cexception  =>
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤q+3) ∨ (3*q+2≤(2*q+2) ∧ (2*q+2)≤4*q)) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤2*q+2) ∨ (3*q+1≤(2*q+2) ∧ (2*q+2)≤4*q-1)) at h0
      exfalso
      omega
  | dgap p =>
    have hzb : (4≤p ∧ p≤2*q+1 ∧ p≠q+2) ∧ p≤2*q-1 := hz
    cases w with
    | lp s r =>
      have hwb : (4≤s ∧ s≤2*q+1 ∧ s≠q+2) ∧ (4≤r ∧ r≤2*q+1 ∧ r≠q+2) ∧ s≤r := hw
      have hwbeta := beta_bounds q s hq hw.1
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤p) ∨ (2*q+1≤(2*q+2) ∧ (2*q+2)≤4*q)) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤r) ∨ ((beta q s)≤(2*q+2) ∧ (2*q+2)≤(if s=q+3 ∧ r=q+3 then 4*q-1 else 4*q))) at h0
      exfalso
      omega
    | filledM  =>
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤p) ∨ (2*q+1≤(2*q+2) ∧ (2*q+2)≤4*q)) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤q+3) ∨ (3*q+2≤(2*q+2) ∧ (2*q+2)≤4*q)) at h0
      exfalso
      omega
    | dgap r =>
      have hwb : (4≤r ∧ r≤2*q+1 ∧ r≠q+2) ∧ r≤2*q-1 := hw
      have h0 := heq (p)
      change ((p)=2 ∨ (p)=3 ∨ (5≤(p) ∧ (p)≤p) ∨ (2*q+1≤(p) ∧ (p)≤4*q)) ↔ ((p)=2 ∨ (p)=3 ∨ (5≤(p) ∧ (p)≤r) ∨ (2*q+1≤(p) ∧ (p)≤4*q)) at h0
      have h1 := heq (r)
      change ((r)=2 ∨ (r)=3 ∨ (5≤(r) ∧ (r)≤p) ∨ (2*q+1≤(r) ∧ (r)≤4*q)) ↔ ((r)=2 ∨ (r)=3 ∨ (5≤(r) ∧ (r)≤r) ∨ (2*q+1≤(r) ∧ (r)≤4*q)) at h1
      have hpr : p=r := by omega
      subst r; rfl
    | full  =>
      have h0 := heq (2*q)
      change ((2*q)=2 ∨ (2*q)=3 ∨ (5≤(2*q) ∧ (2*q)≤p) ∨ (2*q+1≤(2*q) ∧ (2*q)≤4*q)) ↔ ((2*q)=2 ∨ (2*q)=3 ∨ (5≤(2*q) ∧ (2*q)≤4*q)) at h0
      exfalso
      omega
    | creg s =>
      have hwb : (4≤s ∧ s≤2*q+1 ∧ s≠q+2) ∧ s≠q+3 := hw
      have hwbeta := beta_bounds q s hq hw.1
      have h0 := heq (2*q)
      change ((2*q)=2 ∨ (2*q)=3 ∨ (5≤(2*q) ∧ (2*q)≤p) ∨ (2*q+1≤(2*q) ∧ (2*q)≤4*q)) ↔ ((2*q)=2 ∨ (2*q)=3 ∨ (5≤(2*q) ∧ (2*q)≤2*q+2) ∨ (2*q)=3*q+1 ∨ ((beta q s)≤(2*q) ∧ (2*q)≤4*q)) at h0
      exfalso
      omega
    | cexception  =>
      have h0 := heq (2*q)
      change ((2*q)=2 ∨ (2*q)=3 ∨ (5≤(2*q) ∧ (2*q)≤p) ∨ (2*q+1≤(2*q) ∧ (2*q)≤4*q)) ↔ ((2*q)=2 ∨ (2*q)=3 ∨ (5≤(2*q) ∧ (2*q)≤2*q+2) ∨ (3*q+1≤(2*q) ∧ (2*q)≤4*q-1)) at h0
      exfalso
      omega
  | full  =>
    cases w with
    | lp s r =>
      have hwb : (4≤s ∧ s≤2*q+1 ∧ s≠q+2) ∧ (4≤r ∧ r≤2*q+1 ∧ r≠q+2) ∧ s≤r := hw
      have hwbeta := beta_bounds q s hq hw.1
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤4*q)) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤r) ∨ ((beta q s)≤(2*q+2) ∧ (2*q+2)≤(if s=q+3 ∧ r=q+3 then 4*q-1 else 4*q))) at h0
      exfalso
      omega
    | filledM  =>
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤4*q)) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤q+3) ∨ (3*q+2≤(2*q+2) ∧ (2*q+2)≤4*q)) at h0
      exfalso
      omega
    | dgap r =>
      have hwb : (4≤r ∧ r≤2*q+1 ∧ r≠q+2) ∧ r≤2*q-1 := hw
      have h0 := heq (2*q)
      change ((2*q)=2 ∨ (2*q)=3 ∨ (5≤(2*q) ∧ (2*q)≤4*q)) ↔ ((2*q)=2 ∨ (2*q)=3 ∨ (5≤(2*q) ∧ (2*q)≤r) ∨ (2*q+1≤(2*q) ∧ (2*q)≤4*q)) at h0
      exfalso
      omega
    | full  =>
      rfl
    | creg s =>
      have hwb : (4≤s ∧ s≤2*q+1 ∧ s≠q+2) ∧ s≠q+3 := hw
      have hwbeta := beta_bounds q s hq hw.1
      have h0 := heq (2*q+3)
      change ((2*q+3)=2 ∨ (2*q+3)=3 ∨ (5≤(2*q+3) ∧ (2*q+3)≤4*q)) ↔ ((2*q+3)=2 ∨ (2*q+3)=3 ∨ (5≤(2*q+3) ∧ (2*q+3)≤2*q+2) ∨ (2*q+3)=3*q+1 ∨ ((beta q s)≤(2*q+3) ∧ (2*q+3)≤4*q)) at h0
      exfalso
      omega
    | cexception  =>
      have h0 := heq (2*q+3)
      change ((2*q+3)=2 ∨ (2*q+3)=3 ∨ (5≤(2*q+3) ∧ (2*q+3)≤4*q)) ↔ ((2*q+3)=2 ∨ (2*q+3)=3 ∨ (5≤(2*q+3) ∧ (2*q+3)≤2*q+2) ∨ (3*q+1≤(2*q+3) ∧ (2*q+3)≤4*q-1)) at h0
      exfalso
      omega
  | creg t =>
    have hzb : (4≤t ∧ t≤2*q+1 ∧ t≠q+2) ∧ t≠q+3 := hz
    have hzbeta := beta_bounds q t hq hz.1
    cases w with
    | lp s r =>
      have hwb : (4≤s ∧ s≤2*q+1 ∧ s≠q+2) ∧ (4≤r ∧ r≤2*q+1 ∧ r≠q+2) ∧ s≤r := hw
      have hwbeta := beta_bounds q s hq hw.1
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤2*q+2) ∨ (2*q+2)=3*q+1 ∨ ((beta q t)≤(2*q+2) ∧ (2*q+2)≤4*q)) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤r) ∨ ((beta q s)≤(2*q+2) ∧ (2*q+2)≤(if s=q+3 ∧ r=q+3 then 4*q-1 else 4*q))) at h0
      exfalso
      omega
    | filledM  =>
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤2*q+2) ∨ (2*q+2)=3*q+1 ∨ ((beta q t)≤(2*q+2) ∧ (2*q+2)≤4*q)) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤q+3) ∨ (3*q+2≤(2*q+2) ∧ (2*q+2)≤4*q)) at h0
      exfalso
      omega
    | dgap r =>
      have hwb : (4≤r ∧ r≤2*q+1 ∧ r≠q+2) ∧ r≤2*q-1 := hw
      have h0 := heq (2*q)
      change ((2*q)=2 ∨ (2*q)=3 ∨ (5≤(2*q) ∧ (2*q)≤2*q+2) ∨ (2*q)=3*q+1 ∨ ((beta q t)≤(2*q) ∧ (2*q)≤4*q)) ↔ ((2*q)=2 ∨ (2*q)=3 ∨ (5≤(2*q) ∧ (2*q)≤r) ∨ (2*q+1≤(2*q) ∧ (2*q)≤4*q)) at h0
      exfalso
      omega
    | full  =>
      have h0 := heq (2*q+3)
      change ((2*q+3)=2 ∨ (2*q+3)=3 ∨ (5≤(2*q+3) ∧ (2*q+3)≤2*q+2) ∨ (2*q+3)=3*q+1 ∨ ((beta q t)≤(2*q+3) ∧ (2*q+3)≤4*q)) ↔ ((2*q+3)=2 ∨ (2*q+3)=3 ∨ (5≤(2*q+3) ∧ (2*q+3)≤4*q)) at h0
      exfalso
      omega
    | creg s =>
      have hwb : (4≤s ∧ s≤2*q+1 ∧ s≠q+2) ∧ s≠q+3 := hw
      have hwbeta := beta_bounds q s hq hw.1
      have hts := creg_unique q t s hq hz hw heq
      subst s; rfl
    | cexception  =>
      have h0 := heq (4*q)
      change ((4*q)=2 ∨ (4*q)=3 ∨ (5≤(4*q) ∧ (4*q)≤2*q+2) ∨ (4*q)=3*q+1 ∨ ((beta q t)≤(4*q) ∧ (4*q)≤4*q)) ↔ ((4*q)=2 ∨ (4*q)=3 ∨ (5≤(4*q) ∧ (4*q)≤2*q+2) ∨ (3*q+1≤(4*q) ∧ (4*q)≤4*q-1)) at h0
      exfalso
      omega
  | cexception  =>
    cases w with
    | lp s r =>
      have hwb : (4≤s ∧ s≤2*q+1 ∧ s≠q+2) ∧ (4≤r ∧ r≤2*q+1 ∧ r≠q+2) ∧ s≤r := hw
      have hwbeta := beta_bounds q s hq hw.1
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤2*q+2) ∨ (3*q+1≤(2*q+2) ∧ (2*q+2)≤4*q-1)) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤r) ∨ ((beta q s)≤(2*q+2) ∧ (2*q+2)≤(if s=q+3 ∧ r=q+3 then 4*q-1 else 4*q))) at h0
      exfalso
      omega
    | filledM  =>
      have h0 := heq (2*q+2)
      change ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤2*q+2) ∨ (3*q+1≤(2*q+2) ∧ (2*q+2)≤4*q-1)) ↔ ((2*q+2)=2 ∨ (2*q+2)=3 ∨ (5≤(2*q+2) ∧ (2*q+2)≤q+3) ∨ (3*q+2≤(2*q+2) ∧ (2*q+2)≤4*q)) at h0
      exfalso
      omega
    | dgap r =>
      have hwb : (4≤r ∧ r≤2*q+1 ∧ r≠q+2) ∧ r≤2*q-1 := hw
      have h0 := heq (2*q)
      change ((2*q)=2 ∨ (2*q)=3 ∨ (5≤(2*q) ∧ (2*q)≤2*q+2) ∨ (3*q+1≤(2*q) ∧ (2*q)≤4*q-1)) ↔ ((2*q)=2 ∨ (2*q)=3 ∨ (5≤(2*q) ∧ (2*q)≤r) ∨ (2*q+1≤(2*q) ∧ (2*q)≤4*q)) at h0
      exfalso
      omega
    | full  =>
      have h0 := heq (2*q+3)
      change ((2*q+3)=2 ∨ (2*q+3)=3 ∨ (5≤(2*q+3) ∧ (2*q+3)≤2*q+2) ∨ (3*q+1≤(2*q+3) ∧ (2*q+3)≤4*q-1)) ↔ ((2*q+3)=2 ∨ (2*q+3)=3 ∨ (5≤(2*q+3) ∧ (2*q+3)≤4*q)) at h0
      exfalso
      omega
    | creg s =>
      have hwb : (4≤s ∧ s≤2*q+1 ∧ s≠q+2) ∧ s≠q+3 := hw
      have hwbeta := beta_bounds q s hq hw.1
      have h0 := heq (4*q)
      change ((4*q)=2 ∨ (4*q)=3 ∨ (5≤(4*q) ∧ (4*q)≤2*q+2) ∨ (3*q+1≤(4*q) ∧ (4*q)≤4*q-1)) ↔ ((4*q)=2 ∨ (4*q)=3 ∨ (5≤(4*q) ∧ (4*q)≤2*q+2) ∨ (4*q)=3*q+1 ∨ ((beta q s)≤(4*q) ∧ (4*q)≤4*q)) at h0
      exfalso
      omega
    | cexception  =>
      rfl

end LuRazClosure
