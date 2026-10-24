import LatticePiecePointDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
noncomputable section
theorem p10_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 10) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p10_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 10 ↔ p10Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p10Domain]
  simp <;> omega
#print axioms p10_points_nonneg
#print axioms p10_points_domain
theorem p11_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 11) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p11_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 11 ↔ p11Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p11Domain]
  simp <;> omega
#print axioms p11_points_nonneg
#print axioms p11_points_domain
theorem p12_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 12) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .upper (4) ((q:Int)+1) (4) ((q:Int)+1) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p12_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 12 ↔ p12Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p12Domain]
  simp <;> omega
#print axioms p12_points_nonneg
#print axioms p12_points_domain
theorem p13_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 13) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .upper (4) ((q:Int)+1) ((q:Int)+3) ((2)*(q:Int)+1) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p13_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 13 ↔ p13Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p13Domain]
  simp <;> omega
#print axioms p13_points_nonneg
#print axioms p13_points_domain
theorem p14_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 14) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .upper ((q:Int)+3) ((2)*(q:Int)+1) (4) ((q:Int)+1) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p14_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 14 ↔ p14Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p14Domain]
  simp <;> omega
#print axioms p14_points_nonneg
#print axioms p14_points_domain
theorem p15_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 15) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .upper ((q:Int)+3) ((2)*(q:Int)+1) ((q:Int)+3) ((2)*(q:Int)+1) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p15_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 15 ↔ p15Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p15Domain]
  simp <;> omega
#print axioms p15_points_nonneg
#print axioms p15_points_domain
theorem p17_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 17) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p17_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 17 ↔ p17Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p17Domain]
  simp <;> omega
#print axioms p17_points_nonneg
#print axioms p17_points_domain
theorem p18_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 18) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p18_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 18 ↔ p18Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p18Domain]
  simp <;> omega
#print axioms p18_points_nonneg
#print axioms p18_points_domain
theorem p19_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 19) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((q:Int)+3) ((2)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p19_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 19 ↔ p19Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p19Domain]
  simp <;> omega
#print axioms p19_points_nonneg
#print axioms p19_points_domain
theorem p20_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 20) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p20_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 20 ↔ p20Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p20Domain]
  simp <;> omega
#print axioms p20_points_nonneg
#print axioms p20_points_domain
end
end LuRazClosure.SourcePieces
