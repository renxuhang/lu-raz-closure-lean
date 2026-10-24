import LatticePiecePointsPart8
import LatticePayloadDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
theorem p82_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 82) : rawPieceEvent q 82 e p↔payload (q:Int) (e:Int) 82 p := by
  have hn := p82_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p82Set,payload,h1,h2,false_or] <;> omega
#print axioms p82_event
theorem p83_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 83) : rawPieceEvent q 83 e p↔payload (q:Int) (e:Int) 83 p := by
  have hn := p83_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (4) ((2)*(q:Int)) ((2)*(q:Int)+2) ((2)*(q:Int)+3) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p83Set,payload,h1,h2,false_or] <;> omega
#print axioms p83_event
theorem p84_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 84) : rawPieceEvent q 84 e p↔payload (q:Int) (e:Int) 84 p := by
  have hn := p84_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((2)*(q:Int)+4) ((4)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p84Set,payload,h1,h2,false_or] <;> omega
#print axioms p84_event
theorem p85_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 85) : rawPieceEvent q 85 e p↔payload (q:Int) (e:Int) 85 p := by
  have hn := p85_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p85Set,payload,h1,h2,false_or] <;> omega
#print axioms p85_event
theorem p86_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 86) : rawPieceEvent q 86 e p↔payload (q:Int) (e:Int) 86 p := by
  have hn := p86_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((2)*(q:Int)+3) ((4)*(q:Int)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p86Set,payload,h1,h2,false_or] <;> omega
#print axioms p86_event
theorem p87_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 87) : rawPieceEvent q 87 e p↔payload (q:Int) (e:Int) 87 p := by
  have hn := p87_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (6) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p87Set,payload,h1,h2,false_or] <;> omega
#print axioms p87_event
theorem p88_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 88) : rawPieceEvent q 88 e p↔payload (q:Int) (e:Int) 88 p := by
  have hn := p88_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .lower (5) ((2)*(q:Int)+(-1)) (0:Int) ((2)*(q:Int)+1) (2) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p88Set,payload,h1,h2,false_or] <;> omega
#print axioms p88_event
theorem p89_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 89) : rawPieceEvent q 89 e p↔payload (q:Int) (e:Int) 89 p := by
  have hn := p89_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p89Set,payload,h1,h2,false_or] <;> omega
#print axioms p89_event
theorem p90_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 90) : rawPieceEvent q 90 e p↔payload (q:Int) (e:Int) 90 p := by
  have hn := p90_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .lower ((2)*(q:Int)+2) ((4)*(q:Int)+(-2)) (0:Int) ((4)*(q:Int)) (2) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p90Set,payload,h1,h2,false_or] <;> omega
#print axioms p90_event
theorem p91_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 91) : rawPieceEvent q 91 e p↔payload (q:Int) (e:Int) 91 p := by
  have hn := p91_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)+(-1)) ((3)*(q:Int)+3) ((4)*(q:Int)) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p91Set,payload,h1,h2,false_or] <;> omega
#print axioms p91_event
end
end LuRazClosure.SourcePieces
