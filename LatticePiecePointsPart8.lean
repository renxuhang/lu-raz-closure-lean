import LatticePiecePointDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
noncomputable section
theorem p82_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 82) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p82_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 82 ↔ p82Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p82Domain]
  simp <;> omega
#print axioms p82_points_nonneg
#print axioms p82_points_domain
theorem p83_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 83) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (4) ((2)*(q:Int)) ((2)*(q:Int)+2) ((2)*(q:Int)+3) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p83_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 83 ↔ p83Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p83Domain]
  simp <;> omega
#print axioms p83_points_nonneg
#print axioms p83_points_domain
theorem p84_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 84) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((2)*(q:Int)+4) ((4)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p84_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 84 ↔ p84Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p84Domain]
  simp <;> omega
#print axioms p84_points_nonneg
#print axioms p84_points_domain
theorem p85_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 85) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p85_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 85 ↔ p85Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p85Domain]
  simp <;> omega
#print axioms p85_points_nonneg
#print axioms p85_points_domain
theorem p86_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 86) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((2)*(q:Int)+3) ((4)*(q:Int)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p86_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 86 ↔ p86Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p86Domain]
  simp <;> omega
#print axioms p86_points_nonneg
#print axioms p86_points_domain
theorem p87_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 87) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (6) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p87_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 87 ↔ p87Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p87Domain]
  simp <;> omega
#print axioms p87_points_nonneg
#print axioms p87_points_domain
theorem p88_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 88) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .lower (5) ((2)*(q:Int)+(-1)) (0:Int) ((2)*(q:Int)+1) (2) p.1 p.2).mp hp
  simp at h
  omega
theorem p88_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 88 ↔ p88Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p88Domain]
  simp <;> omega
#print axioms p88_points_nonneg
#print axioms p88_points_domain
theorem p89_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 89) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p89_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 89 ↔ p89Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p89Domain]
  simp <;> omega
#print axioms p89_points_nonneg
#print axioms p89_points_domain
theorem p90_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 90) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .lower ((2)*(q:Int)+2) ((4)*(q:Int)+(-2)) (0:Int) ((4)*(q:Int)) (2) p.1 p.2).mp hp
  simp at h
  omega
theorem p90_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 90 ↔ p90Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p90Domain]
  simp <;> omega
#print axioms p90_points_nonneg
#print axioms p90_points_domain
theorem p91_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 91) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)+(-1)) ((3)*(q:Int)+3) ((4)*(q:Int)) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p91_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 91 ↔ p91Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p91Domain]
  simp <;> omega
#print axioms p91_points_nonneg
#print axioms p91_points_domain
end
end LuRazClosure.SourcePieces
