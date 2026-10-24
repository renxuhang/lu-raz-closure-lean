import LatticePiecePointsPart5
import LatticePayloadDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
theorem p52_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 52) : rawPieceEvent q 52 e p↔payload (q:Int) (e:Int) 52 p := by
  have hn := p52_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p52Set,payload,h1,h2,false_or] <;> omega
#print axioms p52_event
theorem p53_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 53) : rawPieceEvent q 53 e p↔payload (q:Int) (e:Int) 53 p := by
  have hn := p53_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (5) ((2)*(q:Int)+1) ((4)*(q:Int)+(-2)) ((4)*(q:Int)) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p53Set,payload,h1,h2,false_or] <;> omega
#print axioms p53_event
theorem p54_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 54) : rawPieceEvent q 54 e p↔payload (q:Int) (e:Int) 54 p := by
  have hn := p54_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((q:Int)+4) ((2)*(q:Int)+1) ((4)*(q:Int)+(-2)) ((4)*(q:Int)) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p54Set,payload,h1,h2,false_or] <;> omega
#print axioms p54_event
theorem p55_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 55) : rawPieceEvent q 55 e p↔payload (q:Int) (e:Int) 55 p := by
  have hn := p55_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p55Set,payload,h1,h2,false_or] <;> omega
#print axioms p55_event
theorem p56_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 56) : rawPieceEvent q 56 e p↔payload (q:Int) (e:Int) 56 p := by
  have hn := p56_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p56Set,payload,h1,h2,false_or] <;> omega
#print axioms p56_event
theorem p57_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 57) : rawPieceEvent q 57 e p↔payload (q:Int) (e:Int) 57 p := by
  have hn := p57_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p57Set,payload,h1,h2,false_or] <;> omega
#print axioms p57_event
theorem p58_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 58) : rawPieceEvent q 58 e p↔payload (q:Int) (e:Int) 58 p := by
  have hn := p58_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p58Set,payload,h1,h2,false_or] <;> omega
#print axioms p58_event
theorem p59_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 59) : rawPieceEvent q 59 e p↔payload (q:Int) (e:Int) 59 p := by
  have hn := p59_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p59Set,payload,h1,h2,false_or] <;> omega
#print axioms p59_event
theorem p60_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 60) : rawPieceEvent q 60 e p↔payload (q:Int) (e:Int) 60 p := by
  have hn := p60_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (5) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p60Set,payload,h1,h2,false_or] <;> omega
#print axioms p60_event
theorem p61_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 61) : rawPieceEvent q 61 e p↔payload (q:Int) (e:Int) 61 p := by
  have hn := p61_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((q:Int)+4) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p61Set,payload,h1,h2,false_or] <;> omega
#print axioms p61_event
end
end LuRazClosure.SourcePieces
