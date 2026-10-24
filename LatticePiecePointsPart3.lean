import LatticePiecePointDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
noncomputable section
theorem p32_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 32) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p32_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 32 ↔ p32Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p32Domain]
  simp <;> omega
#print axioms p32_points_nonneg
#print axioms p32_points_domain
theorem p33_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 33) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((q:Int)+4) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p33_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 33 ↔ p33Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p33Domain]
  simp <;> omega
#print axioms p33_points_nonneg
#print axioms p33_points_domain
theorem p34_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 34) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p34_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 34 ↔ p34Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p34Domain]
  simp <;> omega
#print axioms p34_points_nonneg
#print axioms p34_points_domain
theorem p35_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 35) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p35_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 35 ↔ p35Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p35Domain]
  simp <;> omega
#print axioms p35_points_nonneg
#print axioms p35_points_domain
theorem p36_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 36) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((q:Int)+3) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p36_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 36 ↔ p36Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p36Domain]
  simp <;> omega
#print axioms p36_points_nonneg
#print axioms p36_points_domain
theorem p37_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 37) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p37_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 37 ↔ p37Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p37Domain]
  simp <;> omega
#print axioms p37_points_nonneg
#print axioms p37_points_domain
theorem p38_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 38) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p38_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 38 ↔ p38Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p38Domain]
  simp <;> omega
#print axioms p38_points_nonneg
#print axioms p38_points_domain
theorem p39_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 39) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .lower (5) ((q:Int)+3) (0:Int) ((4)*(q:Int)+(-3)) ((2)*(q:Int)+(-3)) p.1 p.2).mp hp
  simp at h
  omega
theorem p39_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 39 ↔ p39Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p39Domain]
  simp <;> omega
#print axioms p39_points_nonneg
#print axioms p39_points_domain
theorem p40_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 40) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .lower ((q:Int)+4) ((2)*(q:Int)+1) (0:Int) ((4)*(q:Int)+(-3)) ((2)*(q:Int)+(-4)) p.1 p.2).mp hp
  simp at h
  omega
theorem p40_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 40 ↔ p40Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p40Domain]
  simp <;> omega
#print axioms p40_points_nonneg
#print axioms p40_points_domain
theorem p41_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 41) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .lower ((q:Int)+4) ((2)*(q:Int)+1) (0:Int) ((4)*(q:Int)+(-3)) ((2)*(q:Int)+(-4)) p.1 p.2).mp hp
  simp at h
  omega
theorem p41_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 41 ↔ p41Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p41Domain]
  simp <;> omega
#print axioms p41_points_nonneg
#print axioms p41_points_domain
end
end LuRazClosure.SourcePieces
