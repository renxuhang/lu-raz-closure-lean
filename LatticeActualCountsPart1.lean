import LatticePieceEventsPart0
import LatticePieceEventsPart1
import LatticePieceEventsPart2
import LatticePieceEventsPart3
import LatticePieceEventsPart4
import LatticePieceEventsPart5
import LatticePieceEventsPart6
import LatticePieceEventsPart7
import LatticePieceEventsPart8
import LatticePayloadCountsPart0
import LatticePayloadCountsPart1
import LatticePayloadCountsPart2
import LatticePayloadCountsPart3
import LatticeTallyTools
import LatticePointProperties
namespace LuRazClosure.SourcePieces
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
noncomputable section
theorem actual24_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 24) (rawPieceEvent q 24 e)=Identity_left1_0.term_74 (q:Int) (e:Int) + Identity_left1_0.term_75 (q:Int) (e:Int) + Identity_left1_0.term_76 (q:Int) (e:Int) := by
  classical
  have hs := payload24_count q (e:Int)
  have ht := tally_congr (piecePoints q 24) (rawPieceEvent q 24 e)
    (payload (q:Int) (e:Int) 24) (p24_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual24_count
theorem actual25_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 25) (rawPieceEvent q 25 e)=Identity_left1_0.term_77 (q:Int) (e:Int) + Identity_left1_0.term_78 (q:Int) (e:Int) + Identity_left1_0.term_79 (q:Int) (e:Int) := by
  classical
  have hs := payload25_count q (e:Int)
  have ht := tally_congr (piecePoints q 25) (rawPieceEvent q 25 e)
    (payload (q:Int) (e:Int) 25) (p25_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual25_count
theorem actual26_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 26) (rawPieceEvent q 26 e)=Identity_left1_0.term_80 (q:Int) (e:Int) + Identity_left1_0.term_81 (q:Int) (e:Int) + Identity_left1_0.term_82 (q:Int) (e:Int) + Identity_left1_0.term_83 (q:Int) (e:Int) := by
  classical
  have hs := payload26_count q (e:Int)
  have ht := tally_congr (piecePoints q 26) (rawPieceEvent q 26 e)
    (fun p => payload (q:Int) (e:Int) 26 p ∧ ¬(p.1=(q:Int)+3 ∧ p.2=(q:Int)+3 ∧ e=4*q)) (p26_event q e hq he)
  rw [ht,tally_and_not]
  have hp : ((piecePoints q 26).filter (fun p => decide (payload (q:Int) (e:Int) 26 p ∧ (p.1=(q:Int)+3 ∧ p.2=(q:Int)+3 ∧ e=4*q)))).Perm
      ((piecePoints q 27).filter (fun p => decide (payload (q:Int) (e:Int) 27 p))) := by
    apply (List.perm_ext_iff_of_nodup
      (List.Nodup.sublist List.filter_sublist (piece_points_nodup q 26))
      (List.Nodup.sublist List.filter_sublist (piece_points_nodup q 27))).mpr
    intro p
    obtain ⟨a,b⟩ := p
    simp only [List.mem_filter,decide_eq_true_eq,piecePoints,orientedPoints_mem,payload]
    simp <;> omega
  have hc : tally (piecePoints q 26) (fun p => payload (q:Int) (e:Int) 26 p ∧ (p.1=(q:Int)+3 ∧ p.2=(q:Int)+3 ∧ e=4*q))=
      tally (piecePoints q 27) (payload (q:Int) (e:Int) 27) := by
    simp only [tally_eq_filter]
    exact congrArg (fun n : Nat => (n:Int)) hp.length_eq
  rw [hc]
  have hn := payload27_count q (e:Int)
  simp only [Int.one_mul] at hs
  omega
#print axioms actual26_count
theorem actual28_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 28) (rawPieceEvent q 28 e)=Identity_left1_0.term_84 (q:Int) (e:Int) + Identity_left1_0.term_85 (q:Int) (e:Int) + Identity_left1_0.term_86 (q:Int) (e:Int) := by
  classical
  have hs := payload28_count q (e:Int)
  have ht := tally_congr (piecePoints q 28) (rawPieceEvent q 28 e)
    (payload (q:Int) (e:Int) 28) (p28_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual28_count
theorem actual29_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 29) (rawPieceEvent q 29 e)=Identity_left1_0.term_87 (q:Int) (e:Int) + Identity_left1_0.term_88 (q:Int) (e:Int) + Identity_left1_0.term_89 (q:Int) (e:Int) := by
  classical
  have hs := payload29_count q (e:Int)
  have ht := tally_congr (piecePoints q 29) (rawPieceEvent q 29 e)
    (payload (q:Int) (e:Int) 29) (p29_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual29_count
theorem actual30_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 30) (rawPieceEvent q 30 e)=Identity_left1_0.term_90 (q:Int) (e:Int) + Identity_left1_0.term_91 (q:Int) (e:Int) + Identity_left1_0.term_92 (q:Int) (e:Int) := by
  classical
  have hs := payload30_count q (e:Int)
  have ht := tally_congr (piecePoints q 30) (rawPieceEvent q 30 e)
    (payload (q:Int) (e:Int) 30) (p30_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual30_count
theorem actual31_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 31) (rawPieceEvent q 31 e)=Identity_left1_0.term_93 (q:Int) (e:Int) := by
  classical
  have hs := payload31_count q (e:Int)
  have ht := tally_congr (piecePoints q 31) (rawPieceEvent q 31 e)
    (payload (q:Int) (e:Int) 31) (p31_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual31_count
theorem actual32_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 32) (rawPieceEvent q 32 e)=Identity_left1_0.term_94 (q:Int) (e:Int) + Identity_left1_0.term_95 (q:Int) (e:Int) + Identity_left1_0.term_96 (q:Int) (e:Int) + Identity_left1_0.term_97 (q:Int) (e:Int) + Identity_left1_0.term_98 (q:Int) (e:Int) + Identity_left1_0.term_99 (q:Int) (e:Int) + Identity_left1_0.term_100 (q:Int) (e:Int) := by
  classical
  have hs := payload32_count q (e:Int)
  have ht := tally_congr (piecePoints q 32) (rawPieceEvent q 32 e)
    (payload (q:Int) (e:Int) 32) (p32_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual32_count
theorem actual33_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 33) (rawPieceEvent q 33 e)=Identity_left1_0.term_101 (q:Int) (e:Int) + Identity_left1_0.term_102 (q:Int) (e:Int) + Identity_left1_0.term_103 (q:Int) (e:Int) + Identity_left1_0.term_104 (q:Int) (e:Int) + Identity_left1_0.term_105 (q:Int) (e:Int) + Identity_left1_0.term_106 (q:Int) (e:Int) + Identity_left1_0.term_107 (q:Int) (e:Int) := by
  classical
  have hs := payload33_count q (e:Int)
  have ht := tally_congr (piecePoints q 33) (rawPieceEvent q 33 e)
    (payload (q:Int) (e:Int) 33) (p33_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual33_count
theorem actual34_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 34) (rawPieceEvent q 34 e)=Identity_left1_0.term_108 (q:Int) (e:Int) + Identity_left1_0.term_109 (q:Int) (e:Int) + Identity_left1_0.term_110 (q:Int) (e:Int) := by
  classical
  have hs := payload34_count q (e:Int)
  have ht := tally_congr (piecePoints q 34) (rawPieceEvent q 34 e)
    (payload (q:Int) (e:Int) 34) (p34_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual34_count
theorem actual35_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 35) (rawPieceEvent q 35 e)=Identity_left1_0.term_111 (q:Int) (e:Int) + Identity_left1_0.term_112 (q:Int) (e:Int) + Identity_left1_0.term_113 (q:Int) (e:Int) := by
  classical
  have hs := payload35_count q (e:Int)
  have ht := tally_congr (piecePoints q 35) (rawPieceEvent q 35 e)
    (payload (q:Int) (e:Int) 35) (p35_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual35_count
theorem actual36_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 36) (rawPieceEvent q 36 e)=Identity_left1_0.term_114 (q:Int) (e:Int) + Identity_left1_0.term_115 (q:Int) (e:Int) + Identity_left1_0.term_116 (q:Int) (e:Int) := by
  classical
  have hs := payload36_count q (e:Int)
  have ht := tally_congr (piecePoints q 36) (rawPieceEvent q 36 e)
    (payload (q:Int) (e:Int) 36) (p36_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual36_count
theorem actual37_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 37) (rawPieceEvent q 37 e)=Identity_left1_0.term_117 (q:Int) (e:Int) + Identity_left1_0.term_118 (q:Int) (e:Int) + Identity_left1_0.term_119 (q:Int) (e:Int) := by
  classical
  have hs := payload37_count q (e:Int)
  have ht := tally_congr (piecePoints q 37) (rawPieceEvent q 37 e)
    (payload (q:Int) (e:Int) 37) (p37_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual37_count
theorem actual38_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 38) (rawPieceEvent q 38 e)=Identity_left1_0.term_120 (q:Int) (e:Int) + Identity_left1_0.term_121 (q:Int) (e:Int) + Identity_left1_0.term_122 (q:Int) (e:Int) := by
  classical
  have hs := payload38_count q (e:Int)
  have ht := tally_congr (piecePoints q 38) (rawPieceEvent q 38 e)
    (payload (q:Int) (e:Int) 38) (p38_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual38_count
theorem actual39_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 39) (rawPieceEvent q 39 e)=Identity_left1_0.term_123 (q:Int) (e:Int) := by
  classical
  have hs := payload39_count q (e:Int)
  have ht := tally_congr (piecePoints q 39) (rawPieceEvent q 39 e)
    (payload (q:Int) (e:Int) 39) (p39_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual39_count
theorem actual40_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 40) (rawPieceEvent q 40 e)=Identity_left1_0.term_124 (q:Int) (e:Int) := by
  classical
  have hs := payload40_count q (e:Int)
  have ht := tally_congr (piecePoints q 40) (rawPieceEvent q 40 e)
    (payload (q:Int) (e:Int) 40) (p40_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual40_count
theorem actual41_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 41) (rawPieceEvent q 41 e)=Identity_left1_0.term_125 (q:Int) (e:Int) + Identity_left1_0.term_126 (q:Int) (e:Int) + Identity_left1_0.term_127 (q:Int) (e:Int) := by
  classical
  have hs := payload41_count q (e:Int)
  have ht := tally_congr (piecePoints q 41) (rawPieceEvent q 41 e)
    (payload (q:Int) (e:Int) 41) (p41_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual41_count
theorem actual42_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 42) (rawPieceEvent q 42 e)=Identity_left1_0.term_128 (q:Int) (e:Int) + Identity_left1_0.term_129 (q:Int) (e:Int) + Identity_left1_0.term_130 (q:Int) (e:Int) := by
  classical
  have hs := payload42_count q (e:Int)
  have ht := tally_congr (piecePoints q 42) (rawPieceEvent q 42 e)
    (payload (q:Int) (e:Int) 42) (p42_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual42_count
theorem actual43_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 43) (rawPieceEvent q 43 e)=Identity_left1_0.term_131 (q:Int) (e:Int) + Identity_left1_0.term_132 (q:Int) (e:Int) + Identity_left1_0.term_133 (q:Int) (e:Int) := by
  classical
  have hs := payload43_count q (e:Int)
  have ht := tally_congr (piecePoints q 43) (rawPieceEvent q 43 e)
    (payload (q:Int) (e:Int) 43) (p43_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual43_count
theorem actual44_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 44) (rawPieceEvent q 44 e)=Identity_left1_0.term_134 (q:Int) (e:Int) := by
  classical
  have hs := payload44_count q (e:Int)
  have ht := tally_congr (piecePoints q 44) (rawPieceEvent q 44 e)
    (payload (q:Int) (e:Int) 44) (p44_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual44_count
theorem actual45_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 45) (rawPieceEvent q 45 e)=Identity_left1_0.term_135 (q:Int) (e:Int) + Identity_left1_0.term_136 (q:Int) (e:Int) + Identity_left1_0.term_137 (q:Int) (e:Int) + Identity_left1_0.term_138 (q:Int) (e:Int) + Identity_left1_0.term_139 (q:Int) (e:Int) + Identity_left1_0.term_140 (q:Int) (e:Int) + Identity_left1_0.term_141 (q:Int) (e:Int) := by
  classical
  have hs := payload45_count q (e:Int)
  have ht := tally_congr (piecePoints q 45) (rawPieceEvent q 45 e)
    (payload (q:Int) (e:Int) 45) (p45_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual45_count
theorem actual46_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 46) (rawPieceEvent q 46 e)=Identity_left1_0.term_142 (q:Int) (e:Int) + Identity_left1_0.term_143 (q:Int) (e:Int) + Identity_left1_0.term_144 (q:Int) (e:Int) := by
  classical
  have hs := payload46_count q (e:Int)
  have ht := tally_congr (piecePoints q 46) (rawPieceEvent q 46 e)
    (payload (q:Int) (e:Int) 46) (p46_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual46_count
theorem actual47_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 47) (rawPieceEvent q 47 e)=Identity_left1_0.term_145 (q:Int) (e:Int) := by
  classical
  have hs := payload47_count q (e:Int)
  have ht := tally_congr (piecePoints q 47) (rawPieceEvent q 47 e)
    (payload (q:Int) (e:Int) 47) (p47_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual47_count
end
end LuRazClosure.SourcePieces
