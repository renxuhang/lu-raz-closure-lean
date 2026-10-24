import LatticePiecePointsPart7
import LatticePayloadDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
theorem p72_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 72) : rawPieceEvent q 72 e p↔payload (q:Int) (e:Int) 72 p := by
  have hn := p72_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((q:Int)+3) ((2)*(q:Int)+1) ((2)*(q:Int)+2) ((2)*(q:Int)+3) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p72Set,payload,h1,h2,false_or] <;> omega
#print axioms p72_event
theorem p73_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 73) : rawPieceEvent q 73 e p↔payload (q:Int) (e:Int) 73 p := by
  have hn := p73_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p73Set,payload,h1,h2,false_or] <;> omega
#print axioms p73_event
theorem p74_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 74) : rawPieceEvent q 74 e p↔payload (q:Int) (e:Int) 74 p := by
  have hn := p74_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((q:Int)+3) ((2)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p74Set,payload,h1,h2,false_or] <;> omega
#print axioms p74_event
theorem p75_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 75) : rawPieceEvent q 75 e p↔payload (q:Int) (e:Int) 75 p := by
  have hn := p75_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((2)*(q:Int)+3) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p75Set,payload,h1,h2,false_or] <;> omega
#print axioms p75_event
theorem p76_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 76) : rawPieceEvent q 76 e p↔payload (q:Int) (e:Int) 76 p := by
  have hn := p76_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((4)*(q:Int)+(-2)) ((4)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p76Set,payload,h1,h2,false_or] <;> omega
#print axioms p76_event
theorem p77_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 77) : rawPieceEvent q 77 e p↔payload (q:Int) (e:Int) 77 p := by
  have hn := p77_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p77Set,payload,h1,h2,false_or] <;> omega
#print axioms p77_event
theorem p78_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 78) : rawPieceEvent q 78 e p↔payload (q:Int) (e:Int) 78 p := by
  have hn := p78_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((4)*(q:Int)+(-2)) ((4)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p78Set,payload,h1,h2,false_or] <;> omega
#print axioms p78_event
theorem p79_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 79) : rawPieceEvent q 79 e p↔payload (q:Int) (e:Int) 79 p := by
  have hn := p79_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p79Set,payload,h1,h2,false_or] <;> omega
#print axioms p79_event
theorem p80_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 80) : rawPieceEvent q 80 e p↔payload (q:Int) (e:Int) 80 p := by
  have hn := p80_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((q:Int)+5) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p80Set,payload,h1,h2,false_or] <;> omega
#print axioms p80_event
theorem p81_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 81) : rawPieceEvent q 81 e p↔payload (q:Int) (e:Int) 81 p := by
  have hn := p81_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((2)*(q:Int)+3) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p81Set,payload,h1,h2,false_or] <;> omega
#print axioms p81_event
end
end LuRazClosure.SourcePieces
