import ThreeRowSpectrumExtremaCells
namespace LuRazThreeRow
open SpectrumExtrema
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
theorem spectrum_max_strict (q e : Int) (hq : 9≤q)
    (he : 1≤e) (hen : e≤4*q) (hne : e≠1) :
    spectrumPolynomial2 q e<19*q*q+17*q-26 := by
  by_cases h0 : e=1
  ·
    exact False.elim (hne h0)
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
theorem spectrum_min_strict (q e : Int) (hq : 6≤q)
    (he : 1≤e) (hen : e≤4*q) (hne : e≠3*q) :
    15*q*q+27*q-40<spectrumPolynomial2 q e := by
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
theorem spectrum_at_one (q : Int) (hq : 4≤q) :
    spectrumPolynomial2 q 1=19*q*q+17*q-26 := by
  simp [spectrumPolynomial2]
theorem spectrum_at_threeq (q : Int) (hq : 4≤q) :
    spectrumPolynomial2 q (3*q)=15*q*q+27*q-40 := by
  unfold spectrumPolynomial2
  have h0 : 3*q≠1 := by omega
  have h1 : 3*q≠2 := by omega
  have h2 : 3*q≠3 := by omega
  have h3 : 3*q≠4 := by omega
  have h4 : ¬3*q≤q+2 := by omega
  have h5 : 3*q≠q+3 := by omega
  have h6 : ¬3*q≤2*q := by omega
  have h7 : 3*q≠2*q+1 := by omega
  have h8 : 3*q≠2*q+2 := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,
    ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,
    ite_eq_left (show 3*q≤3*q from Int.le_refl _)]
  grind
theorem spectrum_q4_min (e : Int) (he : 1≤e) (hen : e≤16) :
    298≤spectrumPolynomial2 4 e ∧ (spectrumPolynomial2 4 e=298 ↔ e=8) := by
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 ∨ e=8 ∨ e=9 ∨ e=10 ∨ e=11 ∨ e=12 ∨ e=13 ∨ e=14 ∨ e=15 ∨ e=16 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  all_goals subst e; decide
#print axioms spectrum_q4_min
theorem spectrum_q4_max (e : Int) (he : 1≤e) (hen : e≤16) :
    spectrumPolynomial2 4 e≤358 ∧ (spectrumPolynomial2 4 e=358 ↔ e=14) := by
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 ∨ e=8 ∨ e=9 ∨ e=10 ∨ e=11 ∨ e=12 ∨ e=13 ∨ e=14 ∨ e=15 ∨ e=16 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  all_goals subst e; decide
#print axioms spectrum_q4_max
theorem spectrum_q5_min (e : Int) (he : 1≤e) (hen : e≤20) :
    466≤spectrumPolynomial2 5 e ∧ (spectrumPolynomial2 5 e=466 ↔ e=9) := by
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 ∨ e=8 ∨ e=9 ∨ e=10 ∨ e=11 ∨ e=12 ∨ e=13 ∨ e=14 ∨ e=15 ∨ e=16 ∨ e=17 ∨ e=18 ∨ e=19 ∨ e=20 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19
  all_goals subst e; decide
#print axioms spectrum_q5_min
theorem spectrum_q5_max (e : Int) (he : 1≤e) (hen : e≤20) :
    spectrumPolynomial2 5 e≤544 ∧ (spectrumPolynomial2 5 e=544 ↔ e=18) := by
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 ∨ e=8 ∨ e=9 ∨ e=10 ∨ e=11 ∨ e=12 ∨ e=13 ∨ e=14 ∨ e=15 ∨ e=16 ∨ e=17 ∨ e=18 ∨ e=19 ∨ e=20 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19
  all_goals subst e; decide
#print axioms spectrum_q5_max
theorem spectrum_q6_min (e : Int) (he : 1≤e) (hen : e≤24) :
    662≤spectrumPolynomial2 6 e ∧ (spectrumPolynomial2 6 e=662 ↔ e=18) := by
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 ∨ e=8 ∨ e=9 ∨ e=10 ∨ e=11 ∨ e=12 ∨ e=13 ∨ e=14 ∨ e=15 ∨ e=16 ∨ e=17 ∨ e=18 ∨ e=19 ∨ e=20 ∨ e=21 ∨ e=22 ∨ e=23 ∨ e=24 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23
  all_goals subst e; decide
#print axioms spectrum_q6_min
theorem spectrum_q6_max (e : Int) (he : 1≤e) (hen : e≤24) :
    spectrumPolynomial2 6 e≤766 ∧ (spectrumPolynomial2 6 e=766 ↔ e=22) := by
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 ∨ e=8 ∨ e=9 ∨ e=10 ∨ e=11 ∨ e=12 ∨ e=13 ∨ e=14 ∨ e=15 ∨ e=16 ∨ e=17 ∨ e=18 ∨ e=19 ∨ e=20 ∨ e=21 ∨ e=22 ∨ e=23 ∨ e=24 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23
  all_goals subst e; decide
#print axioms spectrum_q6_max
theorem spectrum_q7_min (e : Int) (he : 1≤e) (hen : e≤28) :
    884≤spectrumPolynomial2 7 e ∧ (spectrumPolynomial2 7 e=884 ↔ e=21) := by
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 ∨ e=8 ∨ e=9 ∨ e=10 ∨ e=11 ∨ e=12 ∨ e=13 ∨ e=14 ∨ e=15 ∨ e=16 ∨ e=17 ∨ e=18 ∨ e=19 ∨ e=20 ∨ e=21 ∨ e=22 ∨ e=23 ∨ e=24 ∨ e=25 ∨ e=26 ∨ e=27 ∨ e=28 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27
  all_goals subst e; decide
#print axioms spectrum_q7_min
theorem spectrum_q7_max (e : Int) (he : 1≤e) (hen : e≤28) :
    spectrumPolynomial2 7 e≤1026 ∧ (spectrumPolynomial2 7 e=1026 ↔ e=6 ∨ e=7) := by
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 ∨ e=8 ∨ e=9 ∨ e=10 ∨ e=11 ∨ e=12 ∨ e=13 ∨ e=14 ∨ e=15 ∨ e=16 ∨ e=17 ∨ e=18 ∨ e=19 ∨ e=20 ∨ e=21 ∨ e=22 ∨ e=23 ∨ e=24 ∨ e=25 ∨ e=26 ∨ e=27 ∨ e=28 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27
  all_goals subst e; decide
#print axioms spectrum_q7_max
theorem spectrum_q8_min (e : Int) (he : 1≤e) (hen : e≤32) :
    1136≤spectrumPolynomial2 8 e ∧ (spectrumPolynomial2 8 e=1136 ↔ e=24) := by
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 ∨ e=8 ∨ e=9 ∨ e=10 ∨ e=11 ∨ e=12 ∨ e=13 ∨ e=14 ∨ e=15 ∨ e=16 ∨ e=17 ∨ e=18 ∨ e=19 ∨ e=20 ∨ e=21 ∨ e=22 ∨ e=23 ∨ e=24 ∨ e=25 ∨ e=26 ∨ e=27 ∨ e=28 ∨ e=29 ∨ e=30 ∨ e=31 ∨ e=32 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  all_goals subst e; decide
#print axioms spectrum_q8_min
theorem spectrum_q8_max (e : Int) (he : 1≤e) (hen : e≤32) :
    spectrumPolynomial2 8 e≤1326 ∧ (spectrumPolynomial2 8 e=1326 ↔ e=1 ∨ e=7 ∨ e=8) := by
  have hc : e=1 ∨ e=2 ∨ e=3 ∨ e=4 ∨ e=5 ∨ e=6 ∨ e=7 ∨ e=8 ∨ e=9 ∨ e=10 ∨ e=11 ∨ e=12 ∨ e=13 ∨ e=14 ∨ e=15 ∨ e=16 ∨ e=17 ∨ e=18 ∨ e=19 ∨ e=20 ∨ e=21 ∨ e=22 ∨ e=23 ∨ e=24 ∨ e=25 ∨ e=26 ∨ e=27 ∨ e=28 ∨ e=29 ∨ e=30 ∨ e=31 ∨ e=32 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  all_goals subst e; decide
#print axioms spectrum_q8_max
theorem spectrum_maximum_threshold (q : Int) (hq : 4≤q) :
    (∀ e : Int, 1≤e → e≤4*q → e≠1 →
      spectrumPolynomial2 q e<spectrumPolynomial2 q 1) ↔ 9≤q := by
  constructor
  · intro h
    by_cases h9 : 9≤q
    · exact h9
    have hc : q=4 ∨ q=5 ∨ q=6 ∨ q=7 ∨ q=8 := by omega
    rcases hc with h4 | h5 | h6 | h7 | h8
    · subst q
      have hb := h 14 (by decide) (by decide) (by decide)
      have hv : ¬(spectrumPolynomial2 4 14<spectrumPolynomial2 4 1) := by decide
      exact False.elim (hv hb)
    · subst q
      have hb := h 18 (by decide) (by decide) (by decide)
      have hv : ¬(spectrumPolynomial2 5 18<spectrumPolynomial2 5 1) := by decide
      exact False.elim (hv hb)
    · subst q
      have hb := h 22 (by decide) (by decide) (by decide)
      have hv : ¬(spectrumPolynomial2 6 22<spectrumPolynomial2 6 1) := by decide
      exact False.elim (hv hb)
    · subst q
      have hb := h 6 (by decide) (by decide) (by decide)
      have hv : ¬(spectrumPolynomial2 7 6<spectrumPolynomial2 7 1) := by decide
      exact False.elim (hv hb)
    · subst q
      have hb := h 7 (by decide) (by decide) (by decide)
      have hv : ¬(spectrumPolynomial2 8 7<spectrumPolynomial2 8 1) := by decide
      exact False.elim (hv hb)
  · intro h9 e he hen hne
    rw [spectrum_at_one q hq]
    exact spectrum_max_strict q e h9 he hen hne
theorem spectrum_minimum_threshold (q : Int) (hq : 4≤q) :
    (∀ e : Int, 1≤e → e≤4*q → e≠3*q →
      spectrumPolynomial2 q (3*q)<spectrumPolynomial2 q e) ↔ 6≤q := by
  constructor
  · intro h
    by_cases h6 : 6≤q
    · exact h6
    have hc : q=4 ∨ q=5 := by omega
    rcases hc with h4 | h5
    · subst q
      have hb := h 8 (by decide) (by decide) (by decide)
      have hv : ¬(spectrumPolynomial2 4 (3*4)<spectrumPolynomial2 4 8) := by decide
      exact False.elim (hv hb)
    · subst q
      have hb := h 9 (by decide) (by decide) (by decide)
      have hv : ¬(spectrumPolynomial2 5 (3*5)<spectrumPolynomial2 5 9) := by decide
      exact False.elim (hv hb)
  · intro h6 e he hen hne
    rw [spectrum_at_threeq q hq]
    exact spectrum_min_strict q e h6 he hen hne
#print axioms spectrum_maximum_threshold
#print axioms spectrum_minimum_threshold
end LuRazThreeRow
