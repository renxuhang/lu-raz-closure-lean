import LatticePiecePointDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
noncomputable section
theorem p21_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 21) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p21_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 21 ↔ p21Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p21Domain]
  simp <;> omega
#print axioms p21_points_nonneg
#print axioms p21_points_domain
theorem p22_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 22) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((q:Int)+4) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p22_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 22 ↔ p22Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p22Domain]
  simp <;> omega
#print axioms p22_points_nonneg
#print axioms p22_points_domain
theorem p23_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 23) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p23_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 23 ↔ p23Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p23Domain]
  simp <;> omega
#print axioms p23_points_nonneg
#print axioms p23_points_domain
theorem p24_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 24) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p24_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 24 ↔ p24Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p24Domain]
  simp <;> omega
#print axioms p24_points_nonneg
#print axioms p24_points_domain
theorem p25_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 25) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .upper ((q:Int)+3) ((2)*(q:Int)+1) (4) ((q:Int)+1) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p25_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 25 ↔ p25Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p25Domain]
  simp <;> omega
#print axioms p25_points_nonneg
#print axioms p25_points_domain
theorem p26_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 26) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .upper ((q:Int)+3) ((2)*(q:Int)+1) ((q:Int)+3) ((2)*(q:Int)+1) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p26_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 26 ↔ p26Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p26Domain]
  simp <;> omega
#print axioms p26_points_nonneg
#print axioms p26_points_domain
theorem p28_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 28) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p28_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 28 ↔ p28Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p28Domain]
  simp <;> omega
#print axioms p28_points_nonneg
#print axioms p28_points_domain
theorem p29_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 29) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p29_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 29 ↔ p29Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p29Domain]
  simp <;> omega
#print axioms p29_points_nonneg
#print axioms p29_points_domain
theorem p30_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 30) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((q:Int)+3) ((2)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p30_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 30 ↔ p30Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p30Domain]
  simp <;> omega
#print axioms p30_points_nonneg
#print axioms p30_points_domain
theorem p31_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 31) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p31_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 31 ↔ p31Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p31Domain]
  simp <;> omega
#print axioms p31_points_nonneg
#print axioms p31_points_domain
end
end LuRazClosure.SourcePieces
