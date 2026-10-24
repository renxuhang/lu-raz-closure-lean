import LatticePiecePointDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
noncomputable section
theorem p52_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 52) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p52_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 52 ↔ p52Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p52Domain]
  simp <;> omega
#print axioms p52_points_nonneg
#print axioms p52_points_domain
theorem p53_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 53) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (5) ((2)*(q:Int)+1) ((4)*(q:Int)+(-2)) ((4)*(q:Int)) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p53_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 53 ↔ p53Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p53Domain]
  simp <;> omega
#print axioms p53_points_nonneg
#print axioms p53_points_domain
theorem p54_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 54) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((q:Int)+4) ((2)*(q:Int)+1) ((4)*(q:Int)+(-2)) ((4)*(q:Int)) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p54_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 54 ↔ p54Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p54Domain]
  simp <;> omega
#print axioms p54_points_nonneg
#print axioms p54_points_domain
theorem p55_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 55) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p55_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 55 ↔ p55Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p55Domain]
  simp <;> omega
#print axioms p55_points_nonneg
#print axioms p55_points_domain
theorem p56_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 56) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p56_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 56 ↔ p56Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p56Domain]
  simp <;> omega
#print axioms p56_points_nonneg
#print axioms p56_points_domain
theorem p57_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 57) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p57_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 57 ↔ p57Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p57Domain]
  simp <;> omega
#print axioms p57_points_nonneg
#print axioms p57_points_domain
theorem p58_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 58) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p58_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 58 ↔ p58Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p58Domain]
  simp <;> omega
#print axioms p58_points_nonneg
#print axioms p58_points_domain
theorem p59_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 59) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p59_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 59 ↔ p59Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p59Domain]
  simp <;> omega
#print axioms p59_points_nonneg
#print axioms p59_points_domain
theorem p60_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 60) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (5) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p60_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 60 ↔ p60Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p60Domain]
  simp <;> omega
#print axioms p60_points_nonneg
#print axioms p60_points_domain
theorem p61_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 61) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((q:Int)+4) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p61_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 61 ↔ p61Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p61Domain]
  simp <;> omega
#print axioms p61_points_nonneg
#print axioms p61_points_domain
end
end LuRazClosure.SourcePieces
