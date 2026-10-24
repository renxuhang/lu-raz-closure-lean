import LatticePiecePointsPart1
import LatticePayloadDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
theorem p10_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 10) : rawPieceEvent q 10 e p↔payload (q:Int) (e:Int) 10 p := by
  have hn := p10_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p10Set,payload,h1,h2,false_or] <;> omega
#print axioms p10_event
theorem p11_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 11) : rawPieceEvent q 11 e p↔payload (q:Int) (e:Int) 11 p := by
  have hn := p11_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p11Set,payload,h1,h2,false_or] <;> omega
#print axioms p11_event
theorem p12_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 12) : rawPieceEvent q 12 e p↔payload (q:Int) (e:Int) 12 p := by
  have hn := p12_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .upper (4) ((q:Int)+1) (4) ((q:Int)+1) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p12Set,payload,h1,h2,false_or] <;> omega
#print axioms p12_event
theorem p13_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 13) : rawPieceEvent q 13 e p↔payload (q:Int) (e:Int) 13 p := by
  have hn := p13_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .upper (4) ((q:Int)+1) ((q:Int)+3) ((2)*(q:Int)+1) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p13Set,payload,h1,h2,false_or] <;> omega
#print axioms p13_event
theorem p14_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 14) : rawPieceEvent q 14 e p↔payload (q:Int) (e:Int) 14 p := by
  have hn := p14_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .upper ((q:Int)+3) ((2)*(q:Int)+1) (4) ((q:Int)+1) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p14Set,payload,h1,h2,false_or] <;> omega
#print axioms p14_event
theorem p15_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 15) : rawPieceEvent q 15 e p↔payload (q:Int) (e:Int) 15 p ∧ ¬(p.1=(q:Int)+3 ∧ p.2=(q:Int)+3 ∧ e=4*q) := by
  have hn := p15_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .upper ((q:Int)+3) ((2)*(q:Int)+1) ((q:Int)+3) ((2)*(q:Int)+1) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p15Set,payload,h1,h2,false_or] <;> omega
#print axioms p15_event
theorem p17_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 17) : rawPieceEvent q 17 e p↔payload (q:Int) (e:Int) 17 p := by
  have hn := p17_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p17Set,payload,h1,h2,false_or] <;> omega
#print axioms p17_event
theorem p18_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 18) : rawPieceEvent q 18 e p↔payload (q:Int) (e:Int) 18 p := by
  have hn := p18_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (4) ((q:Int)+1) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p18Set,payload,h1,h2,false_or] <;> omega
#print axioms p18_event
theorem p19_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 19) : rawPieceEvent q 19 e p↔payload (q:Int) (e:Int) 19 p := by
  have hn := p19_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((q:Int)+3) ((2)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p19Set,payload,h1,h2,false_or] <;> omega
#print axioms p19_event
theorem p20_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 20) : rawPieceEvent q 20 e p↔payload (q:Int) (e:Int) 20 p := by
  have hn := p20_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p20Set,payload,h1,h2,false_or] <;> omega
#print axioms p20_event
end
end LuRazClosure.SourcePieces
