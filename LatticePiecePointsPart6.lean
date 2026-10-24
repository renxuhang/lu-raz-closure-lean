import LatticePiecePointDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
noncomputable section
theorem p62_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 62) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p62_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 62 ↔ p62Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p62Domain]
  simp <;> omega
#print axioms p62_points_nonneg
#print axioms p62_points_domain
theorem p63_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 63) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((3)*(q:Int)+1) ((4)*(q:Int)+(-3)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p63_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 63 ↔ p63Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p63Domain]
  simp <;> omega
#print axioms p63_points_nonneg
#print axioms p63_points_domain
theorem p64_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 64) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((4)*(q:Int)+(-3)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p64_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 64 ↔ p64Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p64Domain]
  simp <;> omega
#print axioms p64_points_nonneg
#print axioms p64_points_domain
theorem p65_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 65) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p65_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 65 ↔ p65Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p65Domain]
  simp <;> omega
#print axioms p65_points_nonneg
#print axioms p65_points_domain
theorem p66_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 66) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p66_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 66 ↔ p66Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p66Domain]
  simp <;> omega
#print axioms p66_points_nonneg
#print axioms p66_points_domain
theorem p67_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 67) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p67_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 67 ↔ p67Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p67Domain]
  simp <;> omega
#print axioms p67_points_nonneg
#print axioms p67_points_domain
theorem p68_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 68) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p68_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 68 ↔ p68Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p68Domain]
  simp <;> omega
#print axioms p68_points_nonneg
#print axioms p68_points_domain
theorem p69_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 69) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p69_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 69 ↔ p69Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p69Domain]
  simp <;> omega
#print axioms p69_points_nonneg
#print axioms p69_points_domain
theorem p70_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 70) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p70_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 70 ↔ p70Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p70Domain]
  simp <;> omega
#print axioms p70_points_nonneg
#print axioms p70_points_domain
theorem p71_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 71) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (4) ((q:Int)+1) ((2)*(q:Int)+2) ((2)*(q:Int)+3) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p71_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 71 ↔ p71Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p71Domain]
  simp <;> omega
#print axioms p71_points_nonneg
#print axioms p71_points_domain
end
end LuRazClosure.SourcePieces
