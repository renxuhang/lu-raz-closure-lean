import LatticePayloadDefs
import LatticeAtomCounts_0_12
import LatticeAtomCounts_12_58
import LatticeAtomCounts_58_104
import LatticeAtomCounts_104_150
import LatticeAtomCounts_150_196
import LatticeAtomCounts_196_242
import LatticeAtomCounts_242_276
namespace LuRazClosure.SourcePieces
open LuRazLattice LuRazLattice.AtomCounts
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
noncomputable section
theorem payload0_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 0) (payload (q:Int) e 0)=Identity_left1_0.term_0 (q:Int) e := by
  have h0 := atom0_count (q:Int) e
  exact h0
#print axioms payload0_count
theorem payload1_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 1) (payload (q:Int) e 1)=Identity_left1_0.term_1 (q:Int) e := by
  have h1 := atom1_count (q:Int) e
  exact h1
#print axioms payload1_count
theorem payload2_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 2) (payload (q:Int) e 2)=Identity_left1_0.term_2 (q:Int) e + Identity_left1_0.term_3 (q:Int) e + Identity_left1_0.term_4 (q:Int) e := by
  have h2 := atom2_count (q:Int) e
  have h3 := atom3_count (q:Int) e
  have h4 := atom4_count (q:Int) e
  have ht : tally (piecePoints q 2) (payload (q:Int) e 2)=tally (piecePoints q 2) (event2 (q:Int) e) + tally (piecePoints q 2) (event3 (q:Int) e) - tally (piecePoints q 2) (event4 (q:Int) e) := by
    exact (tally_or (piecePoints q 2) (event2 (q:Int) e) (event3 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 2) (event2 (q:Int) e) + tally (piecePoints q 2) (event3 (q:Int) e) - tally (piecePoints q 2) (event4 (q:Int) e))=Identity_left1_0.term_2 (q:Int) e + Identity_left1_0.term_3 (q:Int) e + Identity_left1_0.term_4 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 2) (event2 (q:Int) e)=Identity_left1_0.term_2 (q:Int) e at h2
  change (1:Int)*2*tally (piecePoints q 2) (event3 (q:Int) e)=Identity_left1_0.term_3 (q:Int) e at h3
  change (-1:Int)*2*tally (piecePoints q 2) (event4 (q:Int) e)=Identity_left1_0.term_4 (q:Int) e at h4
  omega
#print axioms payload2_count
theorem payload3_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 3) (payload (q:Int) e 3)=Identity_left1_0.term_5 (q:Int) e := by
  have h5 := atom5_count (q:Int) e
  exact h5
#print axioms payload3_count
theorem payload4_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 4) (payload (q:Int) e 4)=Identity_left1_0.term_6 (q:Int) e + Identity_left1_0.term_7 (q:Int) e + Identity_left1_0.term_8 (q:Int) e := by
  have h6 := atom6_count (q:Int) e
  have h7 := atom7_count (q:Int) e
  have h8 := atom8_count (q:Int) e
  have ht : tally (piecePoints q 4) (payload (q:Int) e 4)=tally (piecePoints q 4) (event6 (q:Int) e) + tally (piecePoints q 4) (event7 (q:Int) e) - tally (piecePoints q 4) (event8 (q:Int) e) := by
    exact (tally_or (piecePoints q 4) (event6 (q:Int) e) (event7 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 4) (event6 (q:Int) e) + tally (piecePoints q 4) (event7 (q:Int) e) - tally (piecePoints q 4) (event8 (q:Int) e))=Identity_left1_0.term_6 (q:Int) e + Identity_left1_0.term_7 (q:Int) e + Identity_left1_0.term_8 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 4) (event6 (q:Int) e)=Identity_left1_0.term_6 (q:Int) e at h6
  change (1:Int)*2*tally (piecePoints q 4) (event7 (q:Int) e)=Identity_left1_0.term_7 (q:Int) e at h7
  change (-1:Int)*2*tally (piecePoints q 4) (event8 (q:Int) e)=Identity_left1_0.term_8 (q:Int) e at h8
  omega
#print axioms payload4_count
theorem payload5_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 5) (payload (q:Int) e 5)=Identity_left1_0.term_9 (q:Int) e + Identity_left1_0.term_10 (q:Int) e + Identity_left1_0.term_11 (q:Int) e := by
  have h9 := atom9_count (q:Int) e
  have h10 := atom10_count (q:Int) e
  have h11 := atom11_count (q:Int) e
  have ht : tally (piecePoints q 5) (payload (q:Int) e 5)=tally (piecePoints q 5) (event9 (q:Int) e) + tally (piecePoints q 5) (event10 (q:Int) e) - tally (piecePoints q 5) (event11 (q:Int) e) := by
    exact (tally_or (piecePoints q 5) (event9 (q:Int) e) (event10 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 5) (event9 (q:Int) e) + tally (piecePoints q 5) (event10 (q:Int) e) - tally (piecePoints q 5) (event11 (q:Int) e))=Identity_left1_0.term_9 (q:Int) e + Identity_left1_0.term_10 (q:Int) e + Identity_left1_0.term_11 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 5) (event9 (q:Int) e)=Identity_left1_0.term_9 (q:Int) e at h9
  change (1:Int)*2*tally (piecePoints q 5) (event10 (q:Int) e)=Identity_left1_0.term_10 (q:Int) e at h10
  change (-1:Int)*2*tally (piecePoints q 5) (event11 (q:Int) e)=Identity_left1_0.term_11 (q:Int) e at h11
  omega
#print axioms payload5_count
theorem payload6_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 6) (payload (q:Int) e 6)=Identity_left1_0.term_12 (q:Int) e + Identity_left1_0.term_13 (q:Int) e + Identity_left1_0.term_14 (q:Int) e + Identity_left1_0.term_15 (q:Int) e + Identity_left1_0.term_16 (q:Int) e + Identity_left1_0.term_17 (q:Int) e + Identity_left1_0.term_18 (q:Int) e := by
  have h12 := atom12_count (q:Int) e
  have h13 := atom13_count (q:Int) e
  have h14 := atom14_count (q:Int) e
  have h15 := atom15_count (q:Int) e
  have h16 := atom16_count (q:Int) e
  have h17 := atom17_count (q:Int) e
  have h18 := atom18_count (q:Int) e
  have ht : tally (piecePoints q 6) (payload (q:Int) e 6)=tally (piecePoints q 6) (event12 (q:Int) e) + tally (piecePoints q 6) (event13 (q:Int) e) + tally (piecePoints q 6) (event14 (q:Int) e) - tally (piecePoints q 6) (event15 (q:Int) e) - tally (piecePoints q 6) (event16 (q:Int) e) - tally (piecePoints q 6) (event17 (q:Int) e) + tally (piecePoints q 6) (event18 (q:Int) e) := by
    exact (tally_or3 (piecePoints q 6) (event12 (q:Int) e) (event13 (q:Int) e) (event14 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 6) (event12 (q:Int) e) + tally (piecePoints q 6) (event13 (q:Int) e) + tally (piecePoints q 6) (event14 (q:Int) e) - tally (piecePoints q 6) (event15 (q:Int) e) - tally (piecePoints q 6) (event16 (q:Int) e) - tally (piecePoints q 6) (event17 (q:Int) e) + tally (piecePoints q 6) (event18 (q:Int) e))=Identity_left1_0.term_12 (q:Int) e + Identity_left1_0.term_13 (q:Int) e + Identity_left1_0.term_14 (q:Int) e + Identity_left1_0.term_15 (q:Int) e + Identity_left1_0.term_16 (q:Int) e + Identity_left1_0.term_17 (q:Int) e + Identity_left1_0.term_18 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 6) (event12 (q:Int) e)=Identity_left1_0.term_12 (q:Int) e at h12
  change (1:Int)*2*tally (piecePoints q 6) (event13 (q:Int) e)=Identity_left1_0.term_13 (q:Int) e at h13
  change (1:Int)*2*tally (piecePoints q 6) (event14 (q:Int) e)=Identity_left1_0.term_14 (q:Int) e at h14
  change (-1:Int)*2*tally (piecePoints q 6) (event15 (q:Int) e)=Identity_left1_0.term_15 (q:Int) e at h15
  change (-1:Int)*2*tally (piecePoints q 6) (event16 (q:Int) e)=Identity_left1_0.term_16 (q:Int) e at h16
  change (-1:Int)*2*tally (piecePoints q 6) (event17 (q:Int) e)=Identity_left1_0.term_17 (q:Int) e at h17
  change (1:Int)*2*tally (piecePoints q 6) (event18 (q:Int) e)=Identity_left1_0.term_18 (q:Int) e at h18
  omega
#print axioms payload6_count
theorem payload7_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 7) (payload (q:Int) e 7)=Identity_left1_0.term_19 (q:Int) e := by
  have h19 := atom19_count (q:Int) e
  exact h19
#print axioms payload7_count
theorem payload8_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 8) (payload (q:Int) e 8)=Identity_left1_0.term_20 (q:Int) e + Identity_left1_0.term_21 (q:Int) e + Identity_left1_0.term_22 (q:Int) e := by
  have h20 := atom20_count (q:Int) e
  have h21 := atom21_count (q:Int) e
  have h22 := atom22_count (q:Int) e
  have ht : tally (piecePoints q 8) (payload (q:Int) e 8)=tally (piecePoints q 8) (event20 (q:Int) e) + tally (piecePoints q 8) (event21 (q:Int) e) - tally (piecePoints q 8) (event22 (q:Int) e) := by
    exact (tally_or (piecePoints q 8) (event20 (q:Int) e) (event21 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 8) (event20 (q:Int) e) + tally (piecePoints q 8) (event21 (q:Int) e) - tally (piecePoints q 8) (event22 (q:Int) e))=Identity_left1_0.term_20 (q:Int) e + Identity_left1_0.term_21 (q:Int) e + Identity_left1_0.term_22 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 8) (event20 (q:Int) e)=Identity_left1_0.term_20 (q:Int) e at h20
  change (1:Int)*2*tally (piecePoints q 8) (event21 (q:Int) e)=Identity_left1_0.term_21 (q:Int) e at h21
  change (-1:Int)*2*tally (piecePoints q 8) (event22 (q:Int) e)=Identity_left1_0.term_22 (q:Int) e at h22
  omega
#print axioms payload8_count
theorem payload9_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 9) (payload (q:Int) e 9)=Identity_left1_0.term_23 (q:Int) e := by
  have h23 := atom23_count (q:Int) e
  exact h23
#print axioms payload9_count
theorem payload10_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 10) (payload (q:Int) e 10)=Identity_left1_0.term_24 (q:Int) e + Identity_left1_0.term_25 (q:Int) e + Identity_left1_0.term_26 (q:Int) e := by
  have h24 := atom24_count (q:Int) e
  have h25 := atom25_count (q:Int) e
  have h26 := atom26_count (q:Int) e
  have ht : tally (piecePoints q 10) (payload (q:Int) e 10)=tally (piecePoints q 10) (event24 (q:Int) e) + tally (piecePoints q 10) (event25 (q:Int) e) - tally (piecePoints q 10) (event26 (q:Int) e) := by
    exact (tally_or (piecePoints q 10) (event24 (q:Int) e) (event25 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 10) (event24 (q:Int) e) + tally (piecePoints q 10) (event25 (q:Int) e) - tally (piecePoints q 10) (event26 (q:Int) e))=Identity_left1_0.term_24 (q:Int) e + Identity_left1_0.term_25 (q:Int) e + Identity_left1_0.term_26 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 10) (event24 (q:Int) e)=Identity_left1_0.term_24 (q:Int) e at h24
  change (1:Int)*2*tally (piecePoints q 10) (event25 (q:Int) e)=Identity_left1_0.term_25 (q:Int) e at h25
  change (-1:Int)*2*tally (piecePoints q 10) (event26 (q:Int) e)=Identity_left1_0.term_26 (q:Int) e at h26
  omega
#print axioms payload10_count
theorem payload11_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 11) (payload (q:Int) e 11)=Identity_left1_0.term_27 (q:Int) e + Identity_left1_0.term_28 (q:Int) e + Identity_left1_0.term_29 (q:Int) e + Identity_left1_0.term_30 (q:Int) e + Identity_left1_0.term_31 (q:Int) e + Identity_left1_0.term_32 (q:Int) e + Identity_left1_0.term_33 (q:Int) e := by
  have h27 := atom27_count (q:Int) e
  have h28 := atom28_count (q:Int) e
  have h29 := atom29_count (q:Int) e
  have h30 := atom30_count (q:Int) e
  have h31 := atom31_count (q:Int) e
  have h32 := atom32_count (q:Int) e
  have h33 := atom33_count (q:Int) e
  have ht : tally (piecePoints q 11) (payload (q:Int) e 11)=tally (piecePoints q 11) (event27 (q:Int) e) + tally (piecePoints q 11) (event28 (q:Int) e) + tally (piecePoints q 11) (event29 (q:Int) e) - tally (piecePoints q 11) (event30 (q:Int) e) - tally (piecePoints q 11) (event31 (q:Int) e) - tally (piecePoints q 11) (event32 (q:Int) e) + tally (piecePoints q 11) (event33 (q:Int) e) := by
    exact (tally_or3 (piecePoints q 11) (event27 (q:Int) e) (event28 (q:Int) e) (event29 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 11) (event27 (q:Int) e) + tally (piecePoints q 11) (event28 (q:Int) e) + tally (piecePoints q 11) (event29 (q:Int) e) - tally (piecePoints q 11) (event30 (q:Int) e) - tally (piecePoints q 11) (event31 (q:Int) e) - tally (piecePoints q 11) (event32 (q:Int) e) + tally (piecePoints q 11) (event33 (q:Int) e))=Identity_left1_0.term_27 (q:Int) e + Identity_left1_0.term_28 (q:Int) e + Identity_left1_0.term_29 (q:Int) e + Identity_left1_0.term_30 (q:Int) e + Identity_left1_0.term_31 (q:Int) e + Identity_left1_0.term_32 (q:Int) e + Identity_left1_0.term_33 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 11) (event27 (q:Int) e)=Identity_left1_0.term_27 (q:Int) e at h27
  change (1:Int)*2*tally (piecePoints q 11) (event28 (q:Int) e)=Identity_left1_0.term_28 (q:Int) e at h28
  change (1:Int)*2*tally (piecePoints q 11) (event29 (q:Int) e)=Identity_left1_0.term_29 (q:Int) e at h29
  change (-1:Int)*2*tally (piecePoints q 11) (event30 (q:Int) e)=Identity_left1_0.term_30 (q:Int) e at h30
  change (-1:Int)*2*tally (piecePoints q 11) (event31 (q:Int) e)=Identity_left1_0.term_31 (q:Int) e at h31
  change (-1:Int)*2*tally (piecePoints q 11) (event32 (q:Int) e)=Identity_left1_0.term_32 (q:Int) e at h32
  change (1:Int)*2*tally (piecePoints q 11) (event33 (q:Int) e)=Identity_left1_0.term_33 (q:Int) e at h33
  omega
#print axioms payload11_count
theorem payload12_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 12) (payload (q:Int) e 12)=Identity_left1_0.term_34 (q:Int) e + Identity_left1_0.term_35 (q:Int) e + Identity_left1_0.term_36 (q:Int) e := by
  have h34 := atom34_count (q:Int) e
  have h35 := atom35_count (q:Int) e
  have h36 := atom36_count (q:Int) e
  have ht : tally (piecePoints q 12) (payload (q:Int) e 12)=tally (piecePoints q 12) (event34 (q:Int) e) + tally (piecePoints q 12) (event35 (q:Int) e) - tally (piecePoints q 12) (event36 (q:Int) e) := by
    exact (tally_or (piecePoints q 12) (event34 (q:Int) e) (event35 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 12) (event34 (q:Int) e) + tally (piecePoints q 12) (event35 (q:Int) e) - tally (piecePoints q 12) (event36 (q:Int) e))=Identity_left1_0.term_34 (q:Int) e + Identity_left1_0.term_35 (q:Int) e + Identity_left1_0.term_36 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 12) (event34 (q:Int) e)=Identity_left1_0.term_34 (q:Int) e at h34
  change (1:Int)*2*tally (piecePoints q 12) (event35 (q:Int) e)=Identity_left1_0.term_35 (q:Int) e at h35
  change (-1:Int)*2*tally (piecePoints q 12) (event36 (q:Int) e)=Identity_left1_0.term_36 (q:Int) e at h36
  omega
#print axioms payload12_count
theorem payload13_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 13) (payload (q:Int) e 13)=Identity_left1_0.term_37 (q:Int) e + Identity_left1_0.term_38 (q:Int) e + Identity_left1_0.term_39 (q:Int) e := by
  have h37 := atom37_count (q:Int) e
  have h38 := atom38_count (q:Int) e
  have h39 := atom39_count (q:Int) e
  have ht : tally (piecePoints q 13) (payload (q:Int) e 13)=tally (piecePoints q 13) (event37 (q:Int) e) + tally (piecePoints q 13) (event38 (q:Int) e) - tally (piecePoints q 13) (event39 (q:Int) e) := by
    exact (tally_or (piecePoints q 13) (event37 (q:Int) e) (event38 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 13) (event37 (q:Int) e) + tally (piecePoints q 13) (event38 (q:Int) e) - tally (piecePoints q 13) (event39 (q:Int) e))=Identity_left1_0.term_37 (q:Int) e + Identity_left1_0.term_38 (q:Int) e + Identity_left1_0.term_39 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 13) (event37 (q:Int) e)=Identity_left1_0.term_37 (q:Int) e at h37
  change (1:Int)*2*tally (piecePoints q 13) (event38 (q:Int) e)=Identity_left1_0.term_38 (q:Int) e at h38
  change (-1:Int)*2*tally (piecePoints q 13) (event39 (q:Int) e)=Identity_left1_0.term_39 (q:Int) e at h39
  omega
#print axioms payload13_count
theorem payload14_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 14) (payload (q:Int) e 14)=Identity_left1_0.term_40 (q:Int) e + Identity_left1_0.term_41 (q:Int) e + Identity_left1_0.term_42 (q:Int) e := by
  have h40 := atom40_count (q:Int) e
  have h41 := atom41_count (q:Int) e
  have h42 := atom42_count (q:Int) e
  have ht : tally (piecePoints q 14) (payload (q:Int) e 14)=tally (piecePoints q 14) (event40 (q:Int) e) + tally (piecePoints q 14) (event41 (q:Int) e) - tally (piecePoints q 14) (event42 (q:Int) e) := by
    exact (tally_or (piecePoints q 14) (event40 (q:Int) e) (event41 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 14) (event40 (q:Int) e) + tally (piecePoints q 14) (event41 (q:Int) e) - tally (piecePoints q 14) (event42 (q:Int) e))=Identity_left1_0.term_40 (q:Int) e + Identity_left1_0.term_41 (q:Int) e + Identity_left1_0.term_42 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 14) (event40 (q:Int) e)=Identity_left1_0.term_40 (q:Int) e at h40
  change (1:Int)*2*tally (piecePoints q 14) (event41 (q:Int) e)=Identity_left1_0.term_41 (q:Int) e at h41
  change (-1:Int)*2*tally (piecePoints q 14) (event42 (q:Int) e)=Identity_left1_0.term_42 (q:Int) e at h42
  omega
#print axioms payload14_count
theorem payload15_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 15) (payload (q:Int) e 15)=Identity_left1_0.term_43 (q:Int) e + Identity_left1_0.term_44 (q:Int) e + Identity_left1_0.term_45 (q:Int) e := by
  have h43 := atom43_count (q:Int) e
  have h44 := atom44_count (q:Int) e
  have h45 := atom45_count (q:Int) e
  have ht : tally (piecePoints q 15) (payload (q:Int) e 15)=tally (piecePoints q 15) (event43 (q:Int) e) + tally (piecePoints q 15) (event44 (q:Int) e) - tally (piecePoints q 15) (event45 (q:Int) e) := by
    exact (tally_or (piecePoints q 15) (event43 (q:Int) e) (event44 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 15) (event43 (q:Int) e) + tally (piecePoints q 15) (event44 (q:Int) e) - tally (piecePoints q 15) (event45 (q:Int) e))=Identity_left1_0.term_43 (q:Int) e + Identity_left1_0.term_44 (q:Int) e + Identity_left1_0.term_45 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 15) (event43 (q:Int) e)=Identity_left1_0.term_43 (q:Int) e at h43
  change (1:Int)*2*tally (piecePoints q 15) (event44 (q:Int) e)=Identity_left1_0.term_44 (q:Int) e at h44
  change (-1:Int)*2*tally (piecePoints q 15) (event45 (q:Int) e)=Identity_left1_0.term_45 (q:Int) e at h45
  omega
#print axioms payload15_count
theorem payload16_count (q : Nat) (e : Int) :
    (-1:Int)*2*tally (piecePoints q 16) (payload (q:Int) e 16)=Identity_left1_0.term_46 (q:Int) e := by
  have h46 := atom46_count (q:Int) e
  exact h46
#print axioms payload16_count
theorem payload17_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 17) (payload (q:Int) e 17)=Identity_left1_0.term_47 (q:Int) e + Identity_left1_0.term_48 (q:Int) e + Identity_left1_0.term_49 (q:Int) e := by
  have h47 := atom47_count (q:Int) e
  have h48 := atom48_count (q:Int) e
  have h49 := atom49_count (q:Int) e
  have ht : tally (piecePoints q 17) (payload (q:Int) e 17)=tally (piecePoints q 17) (event47 (q:Int) e) + tally (piecePoints q 17) (event48 (q:Int) e) - tally (piecePoints q 17) (event49 (q:Int) e) := by
    exact (tally_or (piecePoints q 17) (event47 (q:Int) e) (event48 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 17) (event47 (q:Int) e) + tally (piecePoints q 17) (event48 (q:Int) e) - tally (piecePoints q 17) (event49 (q:Int) e))=Identity_left1_0.term_47 (q:Int) e + Identity_left1_0.term_48 (q:Int) e + Identity_left1_0.term_49 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 17) (event47 (q:Int) e)=Identity_left1_0.term_47 (q:Int) e at h47
  change (1:Int)*2*tally (piecePoints q 17) (event48 (q:Int) e)=Identity_left1_0.term_48 (q:Int) e at h48
  change (-1:Int)*2*tally (piecePoints q 17) (event49 (q:Int) e)=Identity_left1_0.term_49 (q:Int) e at h49
  omega
#print axioms payload17_count
theorem payload18_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 18) (payload (q:Int) e 18)=Identity_left1_0.term_50 (q:Int) e + Identity_left1_0.term_51 (q:Int) e + Identity_left1_0.term_52 (q:Int) e := by
  have h50 := atom50_count (q:Int) e
  have h51 := atom51_count (q:Int) e
  have h52 := atom52_count (q:Int) e
  have ht : tally (piecePoints q 18) (payload (q:Int) e 18)=tally (piecePoints q 18) (event50 (q:Int) e) + tally (piecePoints q 18) (event51 (q:Int) e) - tally (piecePoints q 18) (event52 (q:Int) e) := by
    exact (tally_or (piecePoints q 18) (event50 (q:Int) e) (event51 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 18) (event50 (q:Int) e) + tally (piecePoints q 18) (event51 (q:Int) e) - tally (piecePoints q 18) (event52 (q:Int) e))=Identity_left1_0.term_50 (q:Int) e + Identity_left1_0.term_51 (q:Int) e + Identity_left1_0.term_52 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 18) (event50 (q:Int) e)=Identity_left1_0.term_50 (q:Int) e at h50
  change (1:Int)*2*tally (piecePoints q 18) (event51 (q:Int) e)=Identity_left1_0.term_51 (q:Int) e at h51
  change (-1:Int)*2*tally (piecePoints q 18) (event52 (q:Int) e)=Identity_left1_0.term_52 (q:Int) e at h52
  omega
#print axioms payload18_count
theorem payload19_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 19) (payload (q:Int) e 19)=Identity_left1_0.term_53 (q:Int) e + Identity_left1_0.term_54 (q:Int) e + Identity_left1_0.term_55 (q:Int) e := by
  have h53 := atom53_count (q:Int) e
  have h54 := atom54_count (q:Int) e
  have h55 := atom55_count (q:Int) e
  have ht : tally (piecePoints q 19) (payload (q:Int) e 19)=tally (piecePoints q 19) (event53 (q:Int) e) + tally (piecePoints q 19) (event54 (q:Int) e) - tally (piecePoints q 19) (event55 (q:Int) e) := by
    exact (tally_or (piecePoints q 19) (event53 (q:Int) e) (event54 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 19) (event53 (q:Int) e) + tally (piecePoints q 19) (event54 (q:Int) e) - tally (piecePoints q 19) (event55 (q:Int) e))=Identity_left1_0.term_53 (q:Int) e + Identity_left1_0.term_54 (q:Int) e + Identity_left1_0.term_55 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 19) (event53 (q:Int) e)=Identity_left1_0.term_53 (q:Int) e at h53
  change (1:Int)*2*tally (piecePoints q 19) (event54 (q:Int) e)=Identity_left1_0.term_54 (q:Int) e at h54
  change (-1:Int)*2*tally (piecePoints q 19) (event55 (q:Int) e)=Identity_left1_0.term_55 (q:Int) e at h55
  omega
#print axioms payload19_count
theorem payload20_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 20) (payload (q:Int) e 20)=Identity_left1_0.term_56 (q:Int) e := by
  have h56 := atom56_count (q:Int) e
  exact h56
#print axioms payload20_count
theorem payload21_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 21) (payload (q:Int) e 21)=Identity_left1_0.term_57 (q:Int) e + Identity_left1_0.term_58 (q:Int) e + Identity_left1_0.term_59 (q:Int) e + Identity_left1_0.term_60 (q:Int) e + Identity_left1_0.term_61 (q:Int) e + Identity_left1_0.term_62 (q:Int) e + Identity_left1_0.term_63 (q:Int) e := by
  have h57 := atom57_count (q:Int) e
  have h58 := atom58_count (q:Int) e
  have h59 := atom59_count (q:Int) e
  have h60 := atom60_count (q:Int) e
  have h61 := atom61_count (q:Int) e
  have h62 := atom62_count (q:Int) e
  have h63 := atom63_count (q:Int) e
  have ht : tally (piecePoints q 21) (payload (q:Int) e 21)=tally (piecePoints q 21) (event57 (q:Int) e) + tally (piecePoints q 21) (event58 (q:Int) e) + tally (piecePoints q 21) (event59 (q:Int) e) - tally (piecePoints q 21) (event60 (q:Int) e) - tally (piecePoints q 21) (event61 (q:Int) e) - tally (piecePoints q 21) (event62 (q:Int) e) + tally (piecePoints q 21) (event63 (q:Int) e) := by
    exact (tally_or3 (piecePoints q 21) (event57 (q:Int) e) (event58 (q:Int) e) (event59 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 21) (event57 (q:Int) e) + tally (piecePoints q 21) (event58 (q:Int) e) + tally (piecePoints q 21) (event59 (q:Int) e) - tally (piecePoints q 21) (event60 (q:Int) e) - tally (piecePoints q 21) (event61 (q:Int) e) - tally (piecePoints q 21) (event62 (q:Int) e) + tally (piecePoints q 21) (event63 (q:Int) e))=Identity_left1_0.term_57 (q:Int) e + Identity_left1_0.term_58 (q:Int) e + Identity_left1_0.term_59 (q:Int) e + Identity_left1_0.term_60 (q:Int) e + Identity_left1_0.term_61 (q:Int) e + Identity_left1_0.term_62 (q:Int) e + Identity_left1_0.term_63 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 21) (event57 (q:Int) e)=Identity_left1_0.term_57 (q:Int) e at h57
  change (1:Int)*2*tally (piecePoints q 21) (event58 (q:Int) e)=Identity_left1_0.term_58 (q:Int) e at h58
  change (1:Int)*2*tally (piecePoints q 21) (event59 (q:Int) e)=Identity_left1_0.term_59 (q:Int) e at h59
  change (-1:Int)*2*tally (piecePoints q 21) (event60 (q:Int) e)=Identity_left1_0.term_60 (q:Int) e at h60
  change (-1:Int)*2*tally (piecePoints q 21) (event61 (q:Int) e)=Identity_left1_0.term_61 (q:Int) e at h61
  change (-1:Int)*2*tally (piecePoints q 21) (event62 (q:Int) e)=Identity_left1_0.term_62 (q:Int) e at h62
  change (1:Int)*2*tally (piecePoints q 21) (event63 (q:Int) e)=Identity_left1_0.term_63 (q:Int) e at h63
  omega
#print axioms payload21_count
theorem payload22_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 22) (payload (q:Int) e 22)=Identity_left1_0.term_64 (q:Int) e + Identity_left1_0.term_65 (q:Int) e + Identity_left1_0.term_66 (q:Int) e + Identity_left1_0.term_67 (q:Int) e + Identity_left1_0.term_68 (q:Int) e + Identity_left1_0.term_69 (q:Int) e + Identity_left1_0.term_70 (q:Int) e := by
  have h64 := atom64_count (q:Int) e
  have h65 := atom65_count (q:Int) e
  have h66 := atom66_count (q:Int) e
  have h67 := atom67_count (q:Int) e
  have h68 := atom68_count (q:Int) e
  have h69 := atom69_count (q:Int) e
  have h70 := atom70_count (q:Int) e
  have ht : tally (piecePoints q 22) (payload (q:Int) e 22)=tally (piecePoints q 22) (event64 (q:Int) e) + tally (piecePoints q 22) (event65 (q:Int) e) + tally (piecePoints q 22) (event66 (q:Int) e) - tally (piecePoints q 22) (event67 (q:Int) e) - tally (piecePoints q 22) (event68 (q:Int) e) - tally (piecePoints q 22) (event69 (q:Int) e) + tally (piecePoints q 22) (event70 (q:Int) e) := by
    exact (tally_or3 (piecePoints q 22) (event64 (q:Int) e) (event65 (q:Int) e) (event66 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 22) (event64 (q:Int) e) + tally (piecePoints q 22) (event65 (q:Int) e) + tally (piecePoints q 22) (event66 (q:Int) e) - tally (piecePoints q 22) (event67 (q:Int) e) - tally (piecePoints q 22) (event68 (q:Int) e) - tally (piecePoints q 22) (event69 (q:Int) e) + tally (piecePoints q 22) (event70 (q:Int) e))=Identity_left1_0.term_64 (q:Int) e + Identity_left1_0.term_65 (q:Int) e + Identity_left1_0.term_66 (q:Int) e + Identity_left1_0.term_67 (q:Int) e + Identity_left1_0.term_68 (q:Int) e + Identity_left1_0.term_69 (q:Int) e + Identity_left1_0.term_70 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 22) (event64 (q:Int) e)=Identity_left1_0.term_64 (q:Int) e at h64
  change (1:Int)*2*tally (piecePoints q 22) (event65 (q:Int) e)=Identity_left1_0.term_65 (q:Int) e at h65
  change (1:Int)*2*tally (piecePoints q 22) (event66 (q:Int) e)=Identity_left1_0.term_66 (q:Int) e at h66
  change (-1:Int)*2*tally (piecePoints q 22) (event67 (q:Int) e)=Identity_left1_0.term_67 (q:Int) e at h67
  change (-1:Int)*2*tally (piecePoints q 22) (event68 (q:Int) e)=Identity_left1_0.term_68 (q:Int) e at h68
  change (-1:Int)*2*tally (piecePoints q 22) (event69 (q:Int) e)=Identity_left1_0.term_69 (q:Int) e at h69
  change (1:Int)*2*tally (piecePoints q 22) (event70 (q:Int) e)=Identity_left1_0.term_70 (q:Int) e at h70
  omega
#print axioms payload22_count
end
end LuRazClosure.SourcePieces
