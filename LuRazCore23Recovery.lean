import LuRazCore23Normal

namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def end23 (q t p : Nat) : Nat := if t=q+3 ∧ p=q+3 then 4*q-1 else 4*q
def TwoPiece (p s z e : Nat) : Prop := e=2 ∨ e=3 ∨ I 5 p e ∨ I s z e

theorem twoPiece_low (q p s z e : Nat) (hp : p≤2*q+1) (hs : 2*q+4≤s)
    (he : 4≤e ∧ e≤2*q+1) : TwoPiece p s z e ↔ 5≤e ∧ e≤p := by
  unfold TwoPiece I
  omega

theorem twoPiece_high (q p s z e : Nat) (hp : p≤2*q+1)
    (he : 2*q+4≤e) : TwoPiece p s z e ↔ s≤e ∧ e≤z := by
  unfold TwoPiece I
  omega

theorem twoPiece_unique (q p s z r a b : Nat)
    (hp : 4≤p ∧ p≤2*q+1) (hr : 4≤r ∧ r≤2*q+1)
    (hs : 2*q+4≤s ∧ s≤z) (ha : 2*q+4≤a ∧ a≤b)
    (heq : ∀ e, TwoPiece p s z e ↔ TwoPiece r a b e) : p=r ∧ s=a ∧ z=b := by
  have h0 := heq p
  have h1 := heq r
  rw [twoPiece_low q p s z p hp.2 hs.1 hp,twoPiece_low q r a b p hr.2 ha.1 hp] at h0
  rw [twoPiece_low q p s z r hp.2 hs.1 hr,twoPiece_low q r a b r hr.2 ha.1 hr] at h1
  have h2 := heq s
  have h3 := heq a
  have h4 := heq z
  have h5 := heq b
  rw [twoPiece_high q p s z s hp.2 hs.1,twoPiece_high q r a b s hr.2 hs.1] at h2
  rw [twoPiece_high q p s z a hp.2 ha.1,twoPiece_high q r a b a hr.2 ha.1] at h3
  rw [twoPiece_high q p s z z hp.2 (by omega),twoPiece_high q r a b z hr.2 (by omega)] at h4
  rw [twoPiece_high q p s z b hp.2 (by omega),twoPiece_high q r a b b hr.2 (by omega)] at h5
  omega

theorem beta_injective (q t s : Nat) (hq : 4≤q) (ht : P q t) (hs : P q s)
    (heq : beta q t=beta q s) : t=s := by
  by_cases h : t<s
  · have hc := beta_strict q t s hq ht hs h
    omega
  by_cases h' : s<t
  · have hc := beta_strict q s t hq hs ht h'
    omega
  omega

theorem beta_exception (q : Nat) (hq : 4≤q) : beta q (q+3)=3*q+2 := by
  unfold beta
  split <;> omega

theorem end23_bounds (q t p : Nat) (hq : 4≤q) (ht : P q t) :
    beta q t≤end23 q t p ∧ end23 q t p≤4*q := by
  unfold end23
  split
  · rename_i he
    rw [he.1,beta_exception q hq]
    omega
  · have hb := beta_bounds q t hq ht
    omega

theorem lp_unique (q t p s r : Nat) (hq : 4≤q)
    (hz : P q t ∧ P q p ∧ t≤p) (hw : P q s ∧ P q r ∧ s≤r)
    (heq : ∀ e, LRow q t p e ↔ LRow q s r e) : t=s ∧ p=r := by
  have hb := beta_bounds q t hq hz.1
  have hc := beta_bounds q s hq hw.1
  have he := end23_bounds q t p hq hz.1
  have hf := end23_bounds q s r hq hw.1
  have hz' := hz.2.1
  have hw' := hw.2.1
  unfold P at hz' hw'
  have hm := twoPiece_unique q p (beta q t) (end23 q t p) r (beta q s) (end23 q s r)
    (by omega) (by omega) ⟨hb.1,he.1⟩ ⟨hc.1,hf.1⟩ heq
  exact ⟨beta_injective q t s hq hz.1 hw.1 hm.2.1,hm.1⟩

theorem lp_ne_filled (q t p : Nat) (hq : 4≤q) (hz : P q t ∧ P q p ∧ t≤p)
    (heq : ∀ e, LRow q t p e ↔ NF23.eval q .filledM e) : False := by
  have hb := beta_bounds q t hq hz.1
  have he := end23_bounds q t p hq hz.1
  have hz' := hz.2.1
  unfold P at hz'
  have hm := twoPiece_unique q p (beta q t) (end23 q t p) (q+3) (3*q+2) (4*q)
    (by omega) (by omega) ⟨hb.1,he.1⟩ (by omega) heq
  have hpe : P q (q+3) := by unfold P; omega
  have hte : t=q+3 := beta_injective q t (q+3) hq hz.1 hpe (by rw [beta_exception q hq]; exact hm.2.1)
  have hlast := hm.2.2
  have hf : end23 q t p=4*q-1 := by
    unfold end23
    exact if_pos ⟨hte,hm.1⟩
  omega

def CShape (q s e : Nat) : Prop := e=2 ∨ e=3 ∨ I 5 (2*q+2) e ∨ e=3*q+1 ∨ I s (4*q) e

theorem cShape_high (q s e : Nat) (he : 2*q+4≤e) :
    CShape q s e ↔ e=3*q+1 ∨ (s≤e ∧ e≤4*q) := by
  unfold CShape I
  omega

theorem cShape_unique (q a b : Nat) (hq : 4≤q)
    (ha : 2*q+4≤a ∧ a≤4*q ∧ a≠3*q+2) (hb : 2*q+4≤b ∧ b≤4*q ∧ b≠3*q+2)
    (heq : ∀ e, CShape q a e ↔ CShape q b e) : a=b := by
  have h0 := heq a
  have h1 := heq b
  have h2 := heq (3*q+2)
  rw [cShape_high q a a ha.1,cShape_high q b a ha.1] at h0
  rw [cShape_high q a b hb.1,cShape_high q b b hb.1] at h1
  rw [cShape_high q a (3*q+2) (by omega),cShape_high q b (3*q+2) (by omega)] at h2
  omega

theorem creg_unique (q t s : Nat) (hq : 4≤q)
    (ht : P q t ∧ t≠q+3) (hs : P q s ∧ s≠q+3)
    (heq : ∀ e, NF23.eval q (.creg t) e ↔ NF23.eval q (.creg s) e) : t=s := by
  have ha := beta_bounds q t hq ht.1
  have hb := beta_bounds q s hq hs.1
  have hpe : P q (q+3) := by unfold P; omega
  have hta : beta q t≠3*q+2 := by
    intro h
    exact ht.2 (beta_injective q t (q+3) hq ht.1 hpe (by rw [beta_exception q hq]; exact h))
  have hsb : beta q s≠3*q+2 := by
    intro h
    exact hs.2 (beta_injective q s (q+3) hq hs.1 hpe (by rw [beta_exception q hq]; exact h))
  have hm := cShape_unique q (beta q t) (beta q s) hq ⟨ha.1,ha.2,hta⟩ ⟨hb.1,hb.2,hsb⟩ heq
  exact beta_injective q t s hq ht.1 hs.1 hm

end LuRazClosure
