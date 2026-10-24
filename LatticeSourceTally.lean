import LatticeRawEnumeration
import LatticeTallyTools
import LatticePayloadDefs

namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section

def elementFrequency (q e : Nat) : Int := tally (closureMembers q) (fun R => R e)

theorem elementFrequency_sum (q e : Nat) (hq : 4≤q) :
    elementFrequency q e=
      (positiveIds.map (fun i => tally (piecePoints q i) (rawPieceEvent q i e))).sum := by
  rw [elementFrequency,←tally_perm (latticeMembers_perm q hq) (fun R => R e)]
  rw [latticeMembers,tally_map,rawMembers,tally_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [tally_map,natPoints,tally_map]
  apply tally_congr
  intro p hp
  have hm : natPoint p∈natPoints q i := List.mem_map.mpr ⟨p,hp,rfl⟩
  have hd := (natPoints_mem q i (natPoint p).1 (natPoint p).2 hq hi).mp hm
  exact decode_eval q i (natPoint p).1 (natPoint p).2 hq hd e

#print axioms elementFrequency_sum
end
end LuRazClosure.SourcePieces
