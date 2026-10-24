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
theorem actual0_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 0) (rawPieceEvent q 0 e)=Identity_left1_0.term_0 (q:Int) (e:Int) := by
  classical
  have hs := payload0_count q (e:Int)
  have ht := tally_congr (piecePoints q 0) (rawPieceEvent q 0 e)
    (payload (q:Int) (e:Int) 0) (p0_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual0_count
theorem actual1_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 1) (rawPieceEvent q 1 e)=Identity_left1_0.term_1 (q:Int) (e:Int) := by
  classical
  have hs := payload1_count q (e:Int)
  have ht := tally_congr (piecePoints q 1) (rawPieceEvent q 1 e)
    (payload (q:Int) (e:Int) 1) (p1_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual1_count
theorem actual2_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 2) (rawPieceEvent q 2 e)=Identity_left1_0.term_2 (q:Int) (e:Int) + Identity_left1_0.term_3 (q:Int) (e:Int) + Identity_left1_0.term_4 (q:Int) (e:Int) := by
  classical
  have hs := payload2_count q (e:Int)
  have ht := tally_congr (piecePoints q 2) (rawPieceEvent q 2 e)
    (payload (q:Int) (e:Int) 2) (p2_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual2_count
theorem actual3_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 3) (rawPieceEvent q 3 e)=Identity_left1_0.term_5 (q:Int) (e:Int) := by
  classical
  have hs := payload3_count q (e:Int)
  have ht := tally_congr (piecePoints q 3) (rawPieceEvent q 3 e)
    (payload (q:Int) (e:Int) 3) (p3_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual3_count
theorem actual4_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 4) (rawPieceEvent q 4 e)=Identity_left1_0.term_6 (q:Int) (e:Int) + Identity_left1_0.term_7 (q:Int) (e:Int) + Identity_left1_0.term_8 (q:Int) (e:Int) := by
  classical
  have hs := payload4_count q (e:Int)
  have ht := tally_congr (piecePoints q 4) (rawPieceEvent q 4 e)
    (payload (q:Int) (e:Int) 4) (p4_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual4_count
theorem actual5_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 5) (rawPieceEvent q 5 e)=Identity_left1_0.term_9 (q:Int) (e:Int) + Identity_left1_0.term_10 (q:Int) (e:Int) + Identity_left1_0.term_11 (q:Int) (e:Int) := by
  classical
  have hs := payload5_count q (e:Int)
  have ht := tally_congr (piecePoints q 5) (rawPieceEvent q 5 e)
    (payload (q:Int) (e:Int) 5) (p5_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual5_count
theorem actual6_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 6) (rawPieceEvent q 6 e)=Identity_left1_0.term_12 (q:Int) (e:Int) + Identity_left1_0.term_13 (q:Int) (e:Int) + Identity_left1_0.term_14 (q:Int) (e:Int) + Identity_left1_0.term_15 (q:Int) (e:Int) + Identity_left1_0.term_16 (q:Int) (e:Int) + Identity_left1_0.term_17 (q:Int) (e:Int) + Identity_left1_0.term_18 (q:Int) (e:Int) := by
  classical
  have hs := payload6_count q (e:Int)
  have ht := tally_congr (piecePoints q 6) (rawPieceEvent q 6 e)
    (payload (q:Int) (e:Int) 6) (p6_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual6_count
theorem actual7_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 7) (rawPieceEvent q 7 e)=Identity_left1_0.term_19 (q:Int) (e:Int) := by
  classical
  have hs := payload7_count q (e:Int)
  have ht := tally_congr (piecePoints q 7) (rawPieceEvent q 7 e)
    (payload (q:Int) (e:Int) 7) (p7_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual7_count
theorem actual8_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 8) (rawPieceEvent q 8 e)=Identity_left1_0.term_20 (q:Int) (e:Int) + Identity_left1_0.term_21 (q:Int) (e:Int) + Identity_left1_0.term_22 (q:Int) (e:Int) := by
  classical
  have hs := payload8_count q (e:Int)
  have ht := tally_congr (piecePoints q 8) (rawPieceEvent q 8 e)
    (payload (q:Int) (e:Int) 8) (p8_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual8_count
theorem actual9_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 9) (rawPieceEvent q 9 e)=Identity_left1_0.term_23 (q:Int) (e:Int) := by
  classical
  have hs := payload9_count q (e:Int)
  have ht := tally_congr (piecePoints q 9) (rawPieceEvent q 9 e)
    (payload (q:Int) (e:Int) 9) (p9_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual9_count
theorem actual10_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 10) (rawPieceEvent q 10 e)=Identity_left1_0.term_24 (q:Int) (e:Int) + Identity_left1_0.term_25 (q:Int) (e:Int) + Identity_left1_0.term_26 (q:Int) (e:Int) := by
  classical
  have hs := payload10_count q (e:Int)
  have ht := tally_congr (piecePoints q 10) (rawPieceEvent q 10 e)
    (payload (q:Int) (e:Int) 10) (p10_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual10_count
theorem actual11_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 11) (rawPieceEvent q 11 e)=Identity_left1_0.term_27 (q:Int) (e:Int) + Identity_left1_0.term_28 (q:Int) (e:Int) + Identity_left1_0.term_29 (q:Int) (e:Int) + Identity_left1_0.term_30 (q:Int) (e:Int) + Identity_left1_0.term_31 (q:Int) (e:Int) + Identity_left1_0.term_32 (q:Int) (e:Int) + Identity_left1_0.term_33 (q:Int) (e:Int) := by
  classical
  have hs := payload11_count q (e:Int)
  have ht := tally_congr (piecePoints q 11) (rawPieceEvent q 11 e)
    (payload (q:Int) (e:Int) 11) (p11_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual11_count
theorem actual12_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 12) (rawPieceEvent q 12 e)=Identity_left1_0.term_34 (q:Int) (e:Int) + Identity_left1_0.term_35 (q:Int) (e:Int) + Identity_left1_0.term_36 (q:Int) (e:Int) := by
  classical
  have hs := payload12_count q (e:Int)
  have ht := tally_congr (piecePoints q 12) (rawPieceEvent q 12 e)
    (payload (q:Int) (e:Int) 12) (p12_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual12_count
theorem actual13_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 13) (rawPieceEvent q 13 e)=Identity_left1_0.term_37 (q:Int) (e:Int) + Identity_left1_0.term_38 (q:Int) (e:Int) + Identity_left1_0.term_39 (q:Int) (e:Int) := by
  classical
  have hs := payload13_count q (e:Int)
  have ht := tally_congr (piecePoints q 13) (rawPieceEvent q 13 e)
    (payload (q:Int) (e:Int) 13) (p13_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual13_count
theorem actual14_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 14) (rawPieceEvent q 14 e)=Identity_left1_0.term_40 (q:Int) (e:Int) + Identity_left1_0.term_41 (q:Int) (e:Int) + Identity_left1_0.term_42 (q:Int) (e:Int) := by
  classical
  have hs := payload14_count q (e:Int)
  have ht := tally_congr (piecePoints q 14) (rawPieceEvent q 14 e)
    (payload (q:Int) (e:Int) 14) (p14_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual14_count
theorem actual15_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 15) (rawPieceEvent q 15 e)=Identity_left1_0.term_43 (q:Int) (e:Int) + Identity_left1_0.term_44 (q:Int) (e:Int) + Identity_left1_0.term_45 (q:Int) (e:Int) + Identity_left1_0.term_46 (q:Int) (e:Int) := by
  classical
  have hs := payload15_count q (e:Int)
  have ht := tally_congr (piecePoints q 15) (rawPieceEvent q 15 e)
    (fun p => payload (q:Int) (e:Int) 15 p ∧ ¬(p.1=(q:Int)+3 ∧ p.2=(q:Int)+3 ∧ e=4*q)) (p15_event q e hq he)
  rw [ht,tally_and_not]
  have hp : ((piecePoints q 15).filter (fun p => decide (payload (q:Int) (e:Int) 15 p ∧ (p.1=(q:Int)+3 ∧ p.2=(q:Int)+3 ∧ e=4*q)))).Perm
      ((piecePoints q 16).filter (fun p => decide (payload (q:Int) (e:Int) 16 p))) := by
    apply (List.perm_ext_iff_of_nodup
      (List.Nodup.sublist List.filter_sublist (piece_points_nodup q 15))
      (List.Nodup.sublist List.filter_sublist (piece_points_nodup q 16))).mpr
    intro p
    obtain ⟨a,b⟩ := p
    simp only [List.mem_filter,decide_eq_true_eq,piecePoints,orientedPoints_mem,payload]
    simp <;> omega
  have hc : tally (piecePoints q 15) (fun p => payload (q:Int) (e:Int) 15 p ∧ (p.1=(q:Int)+3 ∧ p.2=(q:Int)+3 ∧ e=4*q))=
      tally (piecePoints q 16) (payload (q:Int) (e:Int) 16) := by
    simp only [tally_eq_filter]
    exact congrArg (fun n : Nat => (n:Int)) hp.length_eq
  rw [hc]
  have hn := payload16_count q (e:Int)
  simp only [Int.one_mul] at hs
  omega
#print axioms actual15_count
theorem actual17_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 17) (rawPieceEvent q 17 e)=Identity_left1_0.term_47 (q:Int) (e:Int) + Identity_left1_0.term_48 (q:Int) (e:Int) + Identity_left1_0.term_49 (q:Int) (e:Int) := by
  classical
  have hs := payload17_count q (e:Int)
  have ht := tally_congr (piecePoints q 17) (rawPieceEvent q 17 e)
    (payload (q:Int) (e:Int) 17) (p17_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual17_count
theorem actual18_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 18) (rawPieceEvent q 18 e)=Identity_left1_0.term_50 (q:Int) (e:Int) + Identity_left1_0.term_51 (q:Int) (e:Int) + Identity_left1_0.term_52 (q:Int) (e:Int) := by
  classical
  have hs := payload18_count q (e:Int)
  have ht := tally_congr (piecePoints q 18) (rawPieceEvent q 18 e)
    (payload (q:Int) (e:Int) 18) (p18_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual18_count
theorem actual19_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 19) (rawPieceEvent q 19 e)=Identity_left1_0.term_53 (q:Int) (e:Int) + Identity_left1_0.term_54 (q:Int) (e:Int) + Identity_left1_0.term_55 (q:Int) (e:Int) := by
  classical
  have hs := payload19_count q (e:Int)
  have ht := tally_congr (piecePoints q 19) (rawPieceEvent q 19 e)
    (payload (q:Int) (e:Int) 19) (p19_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual19_count
theorem actual20_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 20) (rawPieceEvent q 20 e)=Identity_left1_0.term_56 (q:Int) (e:Int) := by
  classical
  have hs := payload20_count q (e:Int)
  have ht := tally_congr (piecePoints q 20) (rawPieceEvent q 20 e)
    (payload (q:Int) (e:Int) 20) (p20_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual20_count
theorem actual21_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 21) (rawPieceEvent q 21 e)=Identity_left1_0.term_57 (q:Int) (e:Int) + Identity_left1_0.term_58 (q:Int) (e:Int) + Identity_left1_0.term_59 (q:Int) (e:Int) + Identity_left1_0.term_60 (q:Int) (e:Int) + Identity_left1_0.term_61 (q:Int) (e:Int) + Identity_left1_0.term_62 (q:Int) (e:Int) + Identity_left1_0.term_63 (q:Int) (e:Int) := by
  classical
  have hs := payload21_count q (e:Int)
  have ht := tally_congr (piecePoints q 21) (rawPieceEvent q 21 e)
    (payload (q:Int) (e:Int) 21) (p21_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual21_count
theorem actual22_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 22) (rawPieceEvent q 22 e)=Identity_left1_0.term_64 (q:Int) (e:Int) + Identity_left1_0.term_65 (q:Int) (e:Int) + Identity_left1_0.term_66 (q:Int) (e:Int) + Identity_left1_0.term_67 (q:Int) (e:Int) + Identity_left1_0.term_68 (q:Int) (e:Int) + Identity_left1_0.term_69 (q:Int) (e:Int) + Identity_left1_0.term_70 (q:Int) (e:Int) := by
  classical
  have hs := payload22_count q (e:Int)
  have ht := tally_congr (piecePoints q 22) (rawPieceEvent q 22 e)
    (payload (q:Int) (e:Int) 22) (p22_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual22_count
theorem actual23_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 23) (rawPieceEvent q 23 e)=Identity_left1_0.term_71 (q:Int) (e:Int) + Identity_left1_0.term_72 (q:Int) (e:Int) + Identity_left1_0.term_73 (q:Int) (e:Int) := by
  classical
  have hs := payload23_count q (e:Int)
  have ht := tally_congr (piecePoints q 23) (rawPieceEvent q 23 e)
    (payload (q:Int) (e:Int) 23) (p23_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual23_count
end
end LuRazClosure.SourcePieces
