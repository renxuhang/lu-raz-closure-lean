import LatticePiecePointsPart6
import LatticePayloadDefs
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
theorem p62_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 62) : rawPieceEvent q 62 e p↔payload (q:Int) (e:Int) 62 p := by
  have hn := p62_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p62Set,payload,h1,h2,false_or] <;> omega
#print axioms p62_event
theorem p63_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 63) : rawPieceEvent q 63 e p↔payload (q:Int) (e:Int) 63 p := by
  have hn := p63_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((3)*(q:Int)+1) ((4)*(q:Int)+(-3)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p63Set,payload,h1,h2,false_or] <;> omega
#print axioms p63_event
theorem p64_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 64) : rawPieceEvent q 64 e p↔payload (q:Int) (e:Int) 64 p := by
  have hn := p64_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((4)*(q:Int)+(-3)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p64Set,payload,h1,h2,false_or] <;> omega
#print axioms p64_event
theorem p65_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 65) : rawPieceEvent q 65 e p↔payload (q:Int) (e:Int) 65 p := by
  have hn := p65_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p65Set,payload,h1,h2,false_or] <;> omega
#print axioms p65_event
theorem p66_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 66) : rawPieceEvent q 66 e p↔payload (q:Int) (e:Int) 66 p := by
  have hn := p66_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p66Set,payload,h1,h2,false_or] <;> omega
#print axioms p66_event
theorem p67_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 67) : rawPieceEvent q 67 e p↔payload (q:Int) (e:Int) 67 p := by
  have hn := p67_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect ((2)*(q:Int)+2) ((3)*(q:Int)+(-1)) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p67Set,payload,h1,h2,false_or] <;> omega
#print axioms p67_event
theorem p68_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 68) : rawPieceEvent q 68 e p↔payload (q:Int) (e:Int) 68 p := by
  have hn := p68_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p68Set,payload,h1,h2,false_or] <;> omega
#print axioms p68_event
theorem p69_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 69) : rawPieceEvent q 69 e p↔payload (q:Int) (e:Int) 69 p := by
  have hn := p69_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p69Set,payload,h1,h2,false_or] <;> omega
#print axioms p69_event
theorem p70_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 70) : rawPieceEvent q 70 e p↔payload (q:Int) (e:Int) 70 p := by
  have hn := p70_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (0:Int) (0:Int) (0:Int) (0:Int) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p70Set,payload,h1,h2,false_or] <;> omega
#print axioms p70_event
theorem p71_event (q e : Nat) (hq : 4≤q) (he : 5≤e) (p : Int×Int)
    (hp : p∈piecePoints q 71) : rawPieceEvent q 71 e p↔payload (q:Int) (e:Int) 71 p := by
  have hn := p71_points_nonneg q hq p hp
  have h1 := Int.toNat_of_nonneg hn.1
  have h2 := Int.toNat_of_nonneg hn.2
  have hb := (orientedPoints_mem .rect (4) ((q:Int)+1) ((2)*(q:Int)+2) ((2)*(q:Int)+3) (0:Int) p.1 p.2).mp hp
  simp at hb
  simp only [rawPieceEvent,pieceSet,p71Set,payload,h1,h2,false_or] <;> omega
#print axioms p71_event
end
end LuRazClosure.SourcePieces
