import LatticePiecePointsPart4
import LatticePayloadDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
theorem p42_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 42) : rawPieceEvent q 42 e p↔payload (q:Int) (e:Int) 42 p := by
  have hn := p42_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .lower (5) ((q:Int)+3) (0:Int) ((3)*(q:Int)) ((2)*(q:Int)+(-3)) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p42Set,payload,h1,h2,false_or] <;> omega
#print axioms p42_event
theorem p43_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 43) : rawPieceEvent q 43 e p↔payload (q:Int) (e:Int) 43 p := by
  have hn := p43_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .lower ((q:Int)+4) ((q:Int)+4) (0:Int) ((3)*(q:Int)) ((2)*(q:Int)+(-4)) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p43Set,payload,h1,h2,false_or] <;> omega
#print axioms p43_event
theorem p44_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 44) : rawPieceEvent q 44 e p↔payload (q:Int) (e:Int) 44 p := by
  have hn := p44_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (5) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p44Set,payload,h1,h2,false_or] <;> omega
#print axioms p44_event
theorem p45_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 45) : rawPieceEvent q 45 e p↔payload (q:Int) (e:Int) 45 p := by
  have hn := p45_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p45Set,payload,h1,h2,false_or] <;> omega
#print axioms p45_event
theorem p46_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 46) : rawPieceEvent q 46 e p↔payload (q:Int) (e:Int) 46 p := by
  have hn := p46_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((q:Int)+4) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p46Set,payload,h1,h2,false_or] <;> omega
#print axioms p46_event
theorem p47_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 47) : rawPieceEvent q 47 e p↔payload (q:Int) (e:Int) 47 p := by
  have hn := p47_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p47Set,payload,h1,h2,false_or] <;> omega
#print axioms p47_event
theorem p48_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 48) : rawPieceEvent q 48 e p↔payload (q:Int) (e:Int) 48 p := by
  have hn := p48_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p48Set,payload,h1,h2,false_or] <;> omega
#print axioms p48_event
theorem p49_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 49) : rawPieceEvent q 49 e p↔payload (q:Int) (e:Int) 49 p := by
  have hn := p49_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p49Set,payload,h1,h2,false_or] <;> omega
#print axioms p49_event
theorem p50_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 50) : rawPieceEvent q 50 e p↔payload (q:Int) (e:Int) 50 p := by
  have hn := p50_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p50Set,payload,h1,h2,false_or] <;> omega
#print axioms p50_event
theorem p51_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 51) : rawPieceEvent q 51 e p↔payload (q:Int) (e:Int) 51 p := by
  have hn := p51_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p51Set,payload,h1,h2,false_or] <;> omega
#print axioms p51_event
end
end LuRazClosure.SourcePieces
