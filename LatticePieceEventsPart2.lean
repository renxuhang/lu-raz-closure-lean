import LatticePiecePointsPart2
import LatticePayloadDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
theorem p21_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 21) : rawPieceEvent q 21 e p↔payload (q:Int) (e:Int) 21 p := by
  have hn := p21_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p21Set,payload,h1,h2,false_or] <;> omega
#print axioms p21_event
theorem p22_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 22) : rawPieceEvent q 22 e p↔payload (q:Int) (e:Int) 22 p := by
  have hn := p22_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((q:Int)+4) ((2)*(q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p22Set,payload,h1,h2,false_or] <;> omega
#print axioms p22_event
theorem p23_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 23) : rawPieceEvent q 23 e p↔payload (q:Int) (e:Int) 23 p := by
  have hn := p23_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p23Set,payload,h1,h2,false_or] <;> omega
#print axioms p23_event
theorem p24_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 24) : rawPieceEvent q 24 e p↔payload (q:Int) (e:Int) 24 p := by
  have hn := p24_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p24Set,payload,h1,h2,false_or] <;> omega
#print axioms p24_event
theorem p25_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 25) : rawPieceEvent q 25 e p↔payload (q:Int) (e:Int) 25 p := by
  have hn := p25_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .upper ((q:Int)+3) ((2)*(q:Int)+1) (4) ((q:Int)+1) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p25Set,payload,h1,h2,false_or] <;> omega
#print axioms p25_event
theorem p26_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 26) : rawPieceEvent q 26 e p↔payload (q:Int) (e:Int) 26 p ∧ ¬(p.1=(q:Int)+3 ∧ p.2=(q:Int)+3 ∧ e=4*q) := by
  have hn := p26_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .upper ((q:Int)+3) ((2)*(q:Int)+1) ((q:Int)+3) ((2)*(q:Int)+1) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p26Set,payload,h1,h2,false_or] <;> omega
#print axioms p26_event
theorem p28_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 28) : rawPieceEvent q 28 e p↔payload (q:Int) (e:Int) 28 p := by
  have hn := p28_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p28Set,payload,h1,h2,false_or] <;> omega
#print axioms p28_event
theorem p29_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 29) : rawPieceEvent q 29 e p↔payload (q:Int) (e:Int) 29 p := by
  have hn := p29_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p29Set,payload,h1,h2,false_or] <;> omega
#print axioms p29_event
theorem p30_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 30) : rawPieceEvent q 30 e p↔payload (q:Int) (e:Int) 30 p := by
  have hn := p30_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((q:Int)+3) ((2)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p30Set,payload,h1,h2,false_or] <;> omega
#print axioms p30_event
theorem p31_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 31) : rawPieceEvent q 31 e p↔payload (q:Int) (e:Int) 31 p := by
  have hn := p31_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p31Set,payload,h1,h2,false_or] <;> omega
#print axioms p31_event
end
end LuRazClosure.SourcePieces
