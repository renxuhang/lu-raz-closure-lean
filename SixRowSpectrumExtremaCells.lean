import SixRowSpectrumPolynomial
namespace LuRazSixRowSpectrum.Extrema
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000
theorem one_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((0)*q+(0)*e+(1)*1)≤e)
    (hu : e≤((0)*q+(0)*e+(1)*1)) :
    ((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(0)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms one_max_strict
theorem one_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((0)*q+(0)*e+(1)*1)≤e)
    (hu : e≤((0)*q+(0)*e+(1)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(0)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-4)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms one_min_strict
theorem two_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((0)*q+(0)*e+(2)*1)≤e)
    (hu : e≤((0)*q+(0)*e+(2)*1)) :
    ((17)*q*q+(0)*q*e+(0)*e*e+(-1)*q+(0)*e+(0)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-5)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms two_max_strict
theorem two_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((0)*q+(0)*e+(2)*1)≤e)
    (hu : e≤((0)*q+(0)*e+(2)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((17)*q*q+(0)*q*e+(0)*e*e+(-1)*q+(0)*e+(0)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-4)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms two_min_strict
theorem three_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((0)*q+(0)*e+(3)*1)≤e)
    (hu : e≤((0)*q+(0)*e+(3)*1)) :
    ((17)*q*q+(0)*q*e+(0)*e*e+(-1)*q+(0)*e+(-2)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-5)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms three_max_strict
theorem three_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((0)*q+(0)*e+(3)*1)≤e)
    (hu : e≤((0)*q+(0)*e+(3)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((17)*q*q+(0)*q*e+(0)*e*e+(-1)*q+(0)*e+(-2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-4)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms three_min_strict
theorem four_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((0)*q+(0)*e+(4)*1)≤e)
    (hu : e≤((0)*q+(0)*e+(4)*1)) :
    ((16)*q*q+(0)*q*e+(0)*e*e+(10)*q+(0)*e+(-22)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-5)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms four_max_strict
theorem four_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((0)*q+(0)*e+(4)*1)≤e)
    (hu : e≤((0)*q+(0)*e+(4)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((16)*q*q+(0)*q*e+(0)*e*e+(10)*q+(0)*e+(-22)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-4)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms four_min_strict
theorem left1_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((0)*q+(0)*e+(5)*1)≤e)
    (hu : e≤((1)*q+(0)*e+(1)*1)) :
    ((18)*q*q+(2)*q*e+(-1)*e*e+(-4)*q+(5)*e+(-4)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(-1)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((-1)*q+(1)*e+(0)*1)*((-1)*q+(1)*e+(0)*1) := by
    by_cases ha : 0≤((-1)*q+(1)*e+(0)*1)
    · exact Int.mul_nonneg ha ha
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  grind
#print axioms left1_max_strict
theorem left1_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((0)*q+(0)*e+(5)*1)≤e)
    (hu : e≤((1)*q+(0)*e+(2)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((18)*q*q+(2)*q*e+(-1)*e*e+(-4)*q+(5)*e+(-4)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(1)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h3 : 0≤((1)*q+(0)*e+(-4)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h4 : 0≤((1)*q+(0)*e+(-4)*1)*((0)*q+(1)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h5 : 0≤((0)*q+(1)*e+(-5)*1)*((1)*q+(-1)*e+(2)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms left1_min_strict
theorem q3_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((1)*q+(0)*e+(3)*1)≤e)
    (hu : e≤((1)*q+(0)*e+(3)*1)) :
    ((18)*q*q+(0)*q*e+(0)*e*e+(-4)*q+(0)*e+(4)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-5)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms q3_max_strict
theorem q3_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((1)*q+(0)*e+(3)*1)≤e)
    (hu : e≤((1)*q+(0)*e+(3)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((18)*q*q+(0)*q*e+(0)*e*e+(-4)*q+(0)*e+(4)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-4)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms q3_min_strict
theorem left2_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((1)*q+(0)*e+(4)*1)≤e)
    (hu : e≤((2)*q+(0)*e+(0)*1)) :
    ((16)*q*q+(4)*q*e+(-2)*e*e+(-24)*q+(18)*e+(-32)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((0)*q+(0)*e+(1)*1)*((-1)*q+(1)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h3 : 0≤((1)*q+(0)*e+(-5)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h4 : 0≤((-1)*q+(1)*e+(-5)*1)*((-1)*q+(1)*e+(-5)*1) := by
    by_cases ha : 0≤((-1)*q+(1)*e+(-5)*1)
    · exact Int.mul_nonneg ha ha
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  grind
#print axioms left2_max_strict
theorem left2_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((1)*q+(0)*e+(4)*1)≤e)
    (hu : e≤((2)*q+(0)*e+(0)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((16)*q*q+(4)*q*e+(-2)*e*e+(-24)*q+(18)*e+(-32)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((0)*q+(0)*e+(1)*1)*((-1)*q+(1)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h3 : 0≤((1)*q+(0)*e+(-4)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h4 : 0≤((1)*q+(0)*e+(-4)*1)*((2)*q+(-1)*e+(0)*1) := Int.mul_nonneg (by omega) (by omega)
  have h5 : 0≤((-1)*q+(1)*e+(-4)*1)*((2)*q+(-1)*e+(0)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms left2_min_strict
theorem h1_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((2)*q+(0)*e+(1)*1)≤e)
    (hu : e≤((2)*q+(0)*e+(1)*1)) :
    ((16)*q*q+(0)*q*e+(0)*e*e+(12)*q+(0)*e+(-24)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-5)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms h1_max_strict
theorem h1_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((2)*q+(0)*e+(1)*1)≤e)
    (hu : e≤((2)*q+(0)*e+(1)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((16)*q*q+(0)*q*e+(0)*e*e+(12)*q+(0)*e+(-24)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-4)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms h1_min_strict
theorem h2_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((2)*q+(0)*e+(2)*1)≤e)
    (hu : e≤((2)*q+(0)*e+(2)*1)) :
    ((16)*q*q+(0)*q*e+(0)*e*e+(10)*q+(0)*e+(-20)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-5)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms h2_max_strict
theorem h2_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((2)*q+(0)*e+(2)*1)≤e)
    (hu : e≤((2)*q+(0)*e+(2)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((16)*q*q+(0)*q*e+(0)*e*e+(10)*q+(0)*e+(-20)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-4)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms h2_min_strict
theorem right1_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((2)*q+(0)*e+(3)*1)≤e)
    (hu : e≤((3)*q+(0)*e+(0)*1)) :
    ((12)*q*q+(4)*q*e+(-1)*e*e+(16)*q+(-3)*e+(-14)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((0)*q+(0)*e+(1)*1)*((-2)*q+(1)*e+(-3)*1) := Int.mul_nonneg (by omega) (by omega)
  have h3 : 0≤((1)*q+(0)*e+(-5)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h4 : 0≤((-2)*q+(1)*e+(-3)*1)*((-2)*q+(1)*e+(-3)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms right1_max_strict
theorem right1_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((2)*q+(0)*e+(3)*1)≤e)
    (hu : e≤((3)*q+(0)*e+(-1)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((12)*q*q+(4)*q*e+(-1)*e*e+(16)*q+(-3)*e+(-14)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((0)*q+(0)*e+(1)*1)*((3)*q+(-1)*e+(-1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h3 : 0≤((1)*q+(0)*e+(-4)*1)*((3)*q+(-1)*e+(-1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h4 : 0≤((-2)*q+(1)*e+(-3)*1)*((3)*q+(-1)*e+(-1)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms right1_min_strict
theorem r1_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((3)*q+(0)*e+(1)*1)≤e)
    (hu : e≤((3)*q+(0)*e+(1)*1)) :
    ((17)*q*q+(0)*q*e+(0)*e*e+(11)*q+(0)*e+(-24)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((1)*q+(0)*e+(-5)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((1)*q+(0)*e+(0)*1)*((1)*q+(0)*e+(0)*1) := by
    by_cases ha : 0≤((1)*q+(0)*e+(0)*1)
    · exact Int.mul_nonneg ha ha
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  grind
#print axioms r1_max_strict
theorem r1_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((3)*q+(0)*e+(1)*1)≤e)
    (hu : e≤((3)*q+(0)*e+(1)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((17)*q*q+(0)*q*e+(0)*e*e+(11)*q+(0)*e+(-24)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-4)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms r1_min_strict
theorem right2_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((3)*q+(0)*e+(2)*1)≤e)
    (hu : e≤((4)*q+(0)*e+(-2)*1)) :
    ((-14)*q*q+(16)*q*e+(-2)*e*e+(26)*q+(-6)*e+(0)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((0)*q+(0)*e+(1)*1)*((4)*q+(-1)*e+(-2)*1) := Int.mul_nonneg (by omega) (by omega)
  have h3 : 0≤((1)*q+(0)*e+(-5)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h4 : 0≤((4)*q+(-1)*e+(-2)*1)*((4)*q+(-1)*e+(-2)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms right2_max_strict
theorem right2_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((3)*q+(0)*e+(2)*1)≤e)
    (hu : e≤((4)*q+(0)*e+(-2)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((-14)*q*q+(16)*q*e+(-2)*e*e+(26)*q+(-6)*e+(0)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((0)*q+(0)*e+(1)*1)*((-3)*q+(1)*e+(-2)*1) := Int.mul_nonneg (by omega) (by omega)
  have h3 : 0≤((1)*q+(0)*e+(-4)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h4 : 0≤((1)*q+(0)*e+(-4)*1)*((-3)*q+(1)*e+(-2)*1) := Int.mul_nonneg (by omega) (by omega)
  have h5 : 0≤((-3)*q+(1)*e+(-2)*1)*((4)*q+(-1)*e+(-2)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms right2_min_strict
theorem n1_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((4)*q+(0)*e+(-1)*1)≤e)
    (hu : e≤((4)*q+(0)*e+(-1)*1)) :
    ((18)*q*q+(0)*q*e+(0)*e*e+(6)*q+(0)*e+(-2)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-5)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms n1_max_strict
theorem n1_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((4)*q+(0)*e+(-1)*1)≤e)
    (hu : e≤((4)*q+(0)*e+(-1)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((18)*q*q+(0)*q*e+(0)*e*e+(6)*q+(0)*e+(-2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-4)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms n1_min_strict
theorem n_max_strict (q e : Int) (hq : 5≤q)
    (hl : ((4)*q+(0)*e+(0)*1)≤e)
    (hu : e≤((4)*q+(0)*e+(0)*1)) :
    ((18)*q*q+(0)*q*e+(0)*e*e+(2)*q+(0)*e+(-4)*1)<((19)*q*q+(0)*q*e+(0)*e*e+(1)*q+(0)*e+(2)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-5)*1)*((1)*q+(0)*e+(-5)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms n_max_strict
theorem n_min_strict (q e : Int) (hq : 4≤q)
    (hl : ((4)*q+(0)*e+(0)*1)≤e)
    (hu : e≤((4)*q+(0)*e+(0)*1)) :
    ((15)*q*q+(0)*q*e+(0)*e*e+(7)*q+(0)*e+(-14)*1)<((18)*q*q+(0)*q*e+(0)*e*e+(2)*q+(0)*e+(-4)*1) := by
  have h0 : 0≤((0)*q+(0)*e+(1)*1)*((0)*q+(0)*e+(1)*1) := Int.mul_nonneg (by omega) (by omega)
  have h1 : 0≤((0)*q+(0)*e+(1)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0≤((1)*q+(0)*e+(-4)*1)*((1)*q+(0)*e+(-4)*1) := Int.mul_nonneg (by omega) (by omega)
  grind
#print axioms n_min_strict
end LuRazSixRowSpectrum.Extrema
