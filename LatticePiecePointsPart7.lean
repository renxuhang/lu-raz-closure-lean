import LatticePiecePointDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
noncomputable section
theorem p72_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 72) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((q:Int)+3) ((2)*(q:Int)+1) ((2)*(q:Int)+2) ((2)*(q:Int)+3) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p72_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 72 ↔ p72Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p72Domain]
  simp <;> omega
#print axioms p72_points_nonneg
#print axioms p72_points_domain
theorem p73_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 73) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p73_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 73 ↔ p73Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p73Domain]
  simp <;> omega
#print axioms p73_points_nonneg
#print axioms p73_points_domain
theorem p74_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 74) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((q:Int)+3) ((2)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p74_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 74 ↔ p74Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p74Domain]
  simp <;> omega
#print axioms p74_points_nonneg
#print axioms p74_points_domain
theorem p75_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 75) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((2)*(q:Int)+3) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p75_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 75 ↔ p75Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p75Domain]
  simp <;> omega
#print axioms p75_points_nonneg
#print axioms p75_points_domain
theorem p76_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 76) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((4)*(q:Int)+(-2)) ((4)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p76_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 76 ↔ p76Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p76Domain]
  simp <;> omega
#print axioms p76_points_nonneg
#print axioms p76_points_domain
theorem p77_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 77) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p77_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 77 ↔ p77Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p77Domain]
  simp <;> omega
#print axioms p77_points_nonneg
#print axioms p77_points_domain
theorem p78_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 78) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((4)*(q:Int)+(-2)) ((4)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p78_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 78 ↔ p78Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p78Domain]
  simp <;> omega
#print axioms p78_points_nonneg
#print axioms p78_points_domain
theorem p79_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 79) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p79_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 79 ↔ p79Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p79Domain]
  simp <;> omega
#print axioms p79_points_nonneg
#print axioms p79_points_domain
theorem p80_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 80) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((q:Int)+5) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p80_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 80 ↔ p80Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p80Domain]
  simp <;> omega
#print axioms p80_points_nonneg
#print axioms p80_points_domain
theorem p81_points_nonneg (q : Nat) (hq : 4≤q) (p : Int×Int)
    (hp : p∈piecePoints q 81) : 0≤p.1 ∧ 0≤p.2 := by
  have h := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((2)*(q:Int)+3) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at h
  omega
theorem p81_points_domain (q a b : Nat) (hq : 4≤q) :
    ((a:Int),(b:Int))∈piecePoints q 81 ↔ p81Domain q a b := by
  simp only [piecePoints,orientedPoints_mem,p81Domain]
  simp <;> omega
#print axioms p81_points_nonneg
#print axioms p81_points_domain
end
end LuRazClosure.SourcePieces
