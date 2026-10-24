import LatticePiecePointsPart3
import LatticePayloadDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
theorem p32_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 32) : rawPieceEvent q 32 e p↔payload (q:Int) (e:Int) 32 p := by
  have hn := p32_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p32Set,payload,h1,h2,false_or] <;> omega
#print axioms p32_event
theorem p33_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 33) : rawPieceEvent q 33 e p↔payload (q:Int) (e:Int) 33 p := by
  have hn := p33_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((q:Int)+4) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p33Set,payload,h1,h2,false_or] <;> omega
#print axioms p33_event
theorem p34_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 34) : rawPieceEvent q 34 e p↔payload (q:Int) (e:Int) 34 p := by
  have hn := p34_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p34Set,payload,h1,h2,false_or] <;> omega
#print axioms p34_event
theorem p35_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 35) : rawPieceEvent q 35 e p↔payload (q:Int) (e:Int) 35 p := by
  have hn := p35_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p35Set,payload,h1,h2,false_or] <;> omega
#print axioms p35_event
theorem p36_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 36) : rawPieceEvent q 36 e p↔payload (q:Int) (e:Int) 36 p := by
  have hn := p36_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((q:Int)+3) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p36Set,payload,h1,h2,false_or] <;> omega
#print axioms p36_event
theorem p37_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 37) : rawPieceEvent q 37 e p↔payload (q:Int) (e:Int) 37 p := by
  have hn := p37_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p37Set,payload,h1,h2,false_or] <;> omega
#print axioms p37_event
theorem p38_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 38) : rawPieceEvent q 38 e p↔payload (q:Int) (e:Int) 38 p := by
  have hn := p38_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p38Set,payload,h1,h2,false_or] <;> omega
#print axioms p38_event
theorem p39_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 39) : rawPieceEvent q 39 e p↔payload (q:Int) (e:Int) 39 p := by
  have hn := p39_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .lower (5) ((q:Int)+3) (0:Int) ((4)*(q:Int)+(-3)) ((2)*(q:Int)+(-3)) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p39Set,payload,h1,h2,false_or] <;> omega
#print axioms p39_event
theorem p40_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 40) : rawPieceEvent q 40 e p↔payload (q:Int) (e:Int) 40 p := by
  have hn := p40_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .lower ((q:Int)+4) ((2)*(q:Int)+1) (0:Int) ((4)*(q:Int)+(-3)) ((2)*(q:Int)+(-4)) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p40Set,payload,h1,h2,false_or] <;> omega
#print axioms p40_event
theorem p41_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 41) : rawPieceEvent q 41 e p↔payload (q:Int) (e:Int) 41 p := by
  have hn := p41_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .lower ((q:Int)+4) ((2)*(q:Int)+1) (0:Int) ((4)*(q:Int)+(-3)) ((2)*(q:Int)+(-4)) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p41Set,payload,h1,h2,false_or] <;> omega
#print axioms p41_event
end
end LuRazClosure.SourcePieces
