import LatticePiecePointDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
noncomputable section
theorem p42_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 42) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .lower (5) ((q:Int)+3) (0:Int) ((3)*(q:Int)) ((2)*(q:Int)+(-3)) p.1 p.2).mp hp
  simp at h
  omega
theorem p42_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 42 ↔ p42Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p42Domain]
  simp <;> omega
#print axioms p42_points_nonneg
#print axioms p42_points_domain
theorem p43_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 43) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .lower ((q:Int)+4) ((q:Int)+4) (0:Int) ((3)*(q:Int)) ((2)*(q:Int)+(-4)) p.1 p.2).mp hp
  simp at h
  omega
theorem p43_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 43 ↔ p43Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p43Domain]
  simp <;> omega
#print axioms p43_points_nonneg
#print axioms p43_points_domain
theorem p44_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 44) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (5) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p44_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 44 ↔ p44Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p44Domain]
  simp <;> omega
#print axioms p44_points_nonneg
#print axioms p44_points_domain
theorem p45_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 45) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p45_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 45 ↔ p45Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p45Domain]
  simp <;> omega
#print axioms p45_points_nonneg
#print axioms p45_points_domain
theorem p46_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 46) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((q:Int)+4) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p46_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 46 ↔ p46Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p46Domain]
  simp <;> omega
#print axioms p46_points_nonneg
#print axioms p46_points_domain
theorem p47_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 47) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p47_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 47 ↔ p47Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p47Domain]
  simp <;> omega
#print axioms p47_points_nonneg
#print axioms p47_points_domain
theorem p48_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 48) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p48_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 48 ↔ p48Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p48Domain]
  simp <;> omega
#print axioms p48_points_nonneg
#print axioms p48_points_domain
theorem p49_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 49) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p49_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 49 ↔ p49Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p49Domain]
  simp <;> omega
#print axioms p49_points_nonneg
#print axioms p49_points_domain
theorem p50_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 50) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p50_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 50 ↔ p50Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p50Domain]
  simp <;> omega
#print axioms p50_points_nonneg
#print axioms p50_points_domain
theorem p51_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 51) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p51_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 51 ↔ p51Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p51Domain]
  simp <;> omega
#print axioms p51_points_nonneg
#print axioms p51_points_domain
end
end LuRazClosure.SourcePieces
