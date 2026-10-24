import SixRowSpectrumExtremaCells
namespace LuRazSixRowSpectrum
open Extrema
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
theorem spectrum_min_strict (q e : Int) (hq : 4≤q)
    (he : 1≤e) (hen : e≤4*q) (hne : e≠3*q) :
    15*q*q+7*q-14<spectrumPolynomial2 q e := by
  by_cases h0 : e=1
  ·
    simp only [spectrumPolynomial2,ite_eq_left h0]
    have ht := one_min_strict q e hq (by omega) (by omega)
    grind
  by_cases h1 : e=2
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_left h1]
    have ht := two_min_strict q e hq (by omega) (by omega)
    grind
  by_cases h2 : e=3
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_left h2]
    have ht := three_min_strict q e hq (by omega) (by omega)
    grind
  by_cases h3 : e=4
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_left h3]
    have ht := four_min_strict q e hq (by omega) (by omega)
    grind
  by_cases h4 : e≤q+2
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_left h4]
    have ht := left1_min_strict q e hq (by omega) (by omega)
    grind
  by_cases h5 : e=q+3
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_left h5]
    have ht := q3_min_strict q e hq (by omega) (by omega)
    grind
  by_cases h6 : e≤2*q
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_left h6]
    have ht := left2_min_strict q e hq (by omega) (by omega)
    grind
  by_cases h7 : e=2*q+1
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_left h7]
    have ht := h1_min_strict q e hq (by omega) (by omega)
    grind
  by_cases h8 : e=2*q+2
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_left h8]
    have ht := h2_min_strict q e hq (by omega) (by omega)
    grind
  by_cases h9 : e≤3*q
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_left h9]
    have ht := right1_min_strict q e hq (by omega) (by omega)
    grind
  by_cases h10 : e=3*q+1
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_left h10]
    have ht := r1_min_strict q e hq (by omega) (by omega)
    grind
  by_cases h11 : e≤4*q-2
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_left h11]
    have ht := right2_min_strict q e hq (by omega) (by omega)
    grind
  by_cases h12 : e=4*q-1
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_right h11,ite_eq_left h12]
    have ht := n1_min_strict q e hq (by omega) (by omega)
    grind
  simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_right h11,ite_eq_right h12]
  have ht := n_min_strict q e hq (by omega) (by omega)
  grind
#print axioms spectrum_min_strict
theorem spectrum_max_strict (q e : Int) (hq : 5≤q)
    (he : 1≤e) (hen : e≤4*q) (hne : e≠q+2) :
    spectrumPolynomial2 q e<19*q*q+q+2 := by
  by_cases h0 : e=1
  ·
    simp only [spectrumPolynomial2,ite_eq_left h0]
    have ht := one_max_strict q e hq (by omega) (by omega)
    grind
  by_cases h1 : e=2
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_left h1]
    have ht := two_max_strict q e hq (by omega) (by omega)
    grind
  by_cases h2 : e=3
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_left h2]
    have ht := three_max_strict q e hq (by omega) (by omega)
    grind
  by_cases h3 : e=4
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_left h3]
    have ht := four_max_strict q e hq (by omega) (by omega)
    grind
  by_cases h4 : e≤q+2
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_left h4]
    have ht := left1_max_strict q e hq (by omega) (by omega)
    grind
  by_cases h5 : e=q+3
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_left h5]
    have ht := q3_max_strict q e hq (by omega) (by omega)
    grind
  by_cases h6 : e≤2*q
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_left h6]
    have ht := left2_max_strict q e hq (by omega) (by omega)
    grind
  by_cases h7 : e=2*q+1
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_left h7]
    have ht := h1_max_strict q e hq (by omega) (by omega)
    grind
  by_cases h8 : e=2*q+2
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_left h8]
    have ht := h2_max_strict q e hq (by omega) (by omega)
    grind
  by_cases h9 : e≤3*q
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_left h9]
    have ht := right1_max_strict q e hq (by omega) (by omega)
    grind
  by_cases h10 : e=3*q+1
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_left h10]
    have ht := r1_max_strict q e hq (by omega) (by omega)
    grind
  by_cases h11 : e≤4*q-2
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_left h11]
    have ht := right2_max_strict q e hq (by omega) (by omega)
    grind
  by_cases h12 : e=4*q-1
  ·
    simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_right h11,ite_eq_left h12]
    have ht := n1_max_strict q e hq (by omega) (by omega)
    grind
  simp only [spectrumPolynomial2,ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_right h11,ite_eq_right h12]
  have ht := n_max_strict q e hq (by omega) (by omega)
  grind
#print axioms spectrum_max_strict
theorem spectrum_at_threeq (q : Int) (hq : 4≤q) :
    spectrumPolynomial2 q (3*q)=15*q*q+7*q-14 := by
  unfold spectrumPolynomial2
  have h0 : ¬((3*q)=1) := by omega
  have h1 : ¬((3*q)=2) := by omega
  have h2 : ¬((3*q)=3) := by omega
  have h3 : ¬((3*q)=4) := by omega
  have h4 : ¬((3*q)≤q+2) := by omega
  have h5 : ¬((3*q)=q+3) := by omega
  have h6 : ¬((3*q)≤2*q) := by omega
  have h7 : ¬((3*q)=2*q+1) := by omega
  have h8 : ¬((3*q)=2*q+2) := by omega
  have h9 : (3*q)≤3*q := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_left h9]
  grind
#print axioms spectrum_at_threeq
theorem spectrum_at_qplus2 (q : Int) (hq : 4≤q) :
    spectrumPolynomial2 q (q+2)=19*q*q+q+2 := by
  unfold spectrumPolynomial2
  have h0 : ¬((q+2)=1) := by omega
  have h1 : ¬((q+2)=2) := by omega
  have h2 : ¬((q+2)=3) := by omega
  have h3 : ¬((q+2)=4) := by omega
  have h4 : (q+2)≤q+2 := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_left h4]
  grind
#print axioms spectrum_at_qplus2
theorem spectrum_q4_min (e : Int) (he : 1≤e) (hen : e≤16) :
    254≤spectrumPolynomial2 4 e ∧ (spectrumPolynomial2 4 e=254 ↔ e=12) := by
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 ∨ e=8 ∨ e=9 ∨ e=10 ∨ e=11 ∨ e=12 ∨ e=13 ∨ e=14 ∨ e=15 ∨ e=16 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  all_goals subst e; decide
#print axioms spectrum_q4_min
theorem spectrum_q4_max (e : Int) (he : 1≤e) (hen : e≤16) :
    spectrumPolynomial2 4 e≤310 ∧ (spectrumPolynomial2 4 e=310 ↔ e=6 ∨ e=15) := by
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 ∨ e=8 ∨ e=9 ∨ e=10 ∨ e=11 ∨ e=12 ∨ e=13 ∨ e=14 ∨ e=15 ∨ e=16 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  all_goals subst e; decide
#print axioms spectrum_q4_max
theorem spectrum_min_exact (q e : Int) (hq : 4≤q)
    (he : 1≤e) (hen : e≤4*q) :
    15*q*q+7*q-14≤spectrumPolynomial2 q e ∧
    (spectrumPolynomial2 q e=15*q*q+7*q-14 ↔ e=3*q) := by
  by_cases h : e=3*q
  · subst e; rw [spectrum_at_threeq q hq]; simp
  · have hs := spectrum_min_strict q e hq he hen h
    omega
theorem spectrum_max_exact (q e : Int) (hq : 5≤q)
    (he : 1≤e) (hen : e≤4*q) :
    spectrumPolynomial2 q e≤19*q*q+q+2 ∧
    (spectrumPolynomial2 q e=19*q*q+q+2 ↔ e=q+2) := by
  by_cases h : e=q+2
  · subst e; rw [spectrum_at_qplus2 q (by omega)]; simp
  · have hs := spectrum_max_strict q e hq he hen h
    omega
theorem spectrum_max_bound (q e : Int) (hq : 4≤q)
    (he : 1≤e) (hen : e≤4*q) :
    spectrumPolynomial2 q e≤19*q*q+q+2 := by
  by_cases h : q=4
  · subst q; exact (spectrum_q4_max e he (by omega)).1
  · exact (spectrum_max_exact q e (by omega) he hen).1
theorem spectrum_maximum_threshold (q : Int) (hq : 4≤q) :
    (∀ e : Int, 1≤e → e≤4*q → e≠q+2 →
      spectrumPolynomial2 q e<spectrumPolynomial2 q (q+2)) ↔ 5≤q := by
  constructor
  · intro h
    by_cases hn : 5≤q
    · exact hn
    have h4 : q=4 := by omega
    subst q
    have ht := h 15 (by decide) (by decide) (by decide)
    have hf : ¬(spectrumPolynomial2 4 15<spectrumPolynomial2 4 (4+2)) := by decide
    exact False.elim (hf ht)
  · intro h5 e he hen hne
    rw [spectrum_at_qplus2 q hq]
    exact spectrum_max_strict q e h5 he hen hne
#print axioms spectrum_min_exact
#print axioms spectrum_max_exact
#print axioms spectrum_max_bound
#print axioms spectrum_maximum_threshold
end LuRazSixRowSpectrum
