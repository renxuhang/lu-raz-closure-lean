import LatticePiecePointDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
noncomputable section
theorem p0_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 0) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p0_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 0 ↔ p0Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p0Domain]
  simp <;> omega
#print axioms p0_points_nonneg
#print axioms p0_points_domain
theorem p1_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 1) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p1_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 1 ↔ p1Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p1Domain]
  simp <;> omega
#print axioms p1_points_nonneg
#print axioms p1_points_domain
theorem p2_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 2) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p2_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 2 ↔ p2Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p2Domain]
  simp <;> omega
#print axioms p2_points_nonneg
#print axioms p2_points_domain
theorem p3_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 3) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p3_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 3 ↔ p3Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p3Domain]
  simp <;> omega
#print axioms p3_points_nonneg
#print axioms p3_points_domain
theorem p4_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 4) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p4_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 4 ↔ p4Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p4Domain]
  simp <;> omega
#print axioms p4_points_nonneg
#print axioms p4_points_domain
theorem p5_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 5) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p5_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 5 ↔ p5Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p5Domain]
  simp <;> omega
#print axioms p5_points_nonneg
#print axioms p5_points_domain
theorem p6_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 6) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p6_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 6 ↔ p6Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p6Domain]
  simp <;> omega
#print axioms p6_points_nonneg
#print axioms p6_points_domain
theorem p7_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 7) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p7_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 7 ↔ p7Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p7Domain]
  simp <;> omega
#print axioms p7_points_nonneg
#print axioms p7_points_domain
theorem p8_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 8) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p8_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 8 ↔ p8Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p8Domain]
  simp <;> omega
#print axioms p8_points_nonneg
#print axioms p8_points_domain
theorem p9_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 9) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p9_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 9 ↔ p9Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p9Domain]
  simp <;> omega
#print axioms p9_points_nonneg
#print axioms p9_points_domain
end
end LuRazClosure.SourcePieces
