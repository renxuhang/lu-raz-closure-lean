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
theorem payload23_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 23) (payload (q:Int) e 23)=Identity_left1_0.term_71 (q:Int) e + Identity_left1_0.term_72 (q:Int) e + Identity_left1_0.term_73 (q:Int) e := by
  have h71 := atom71_count (q:Int) e
  have h72 := atom72_count (q:Int) e
  have h73 := atom73_count (q:Int) e
  have ht : tally (piecePoints q 23) (payload (q:Int) e 23)=tally (piecePoints q 23) (event71 (q:Int) e) + tally (piecePoints q 23) (event72 (q:Int) e) - tally (piecePoints q 23) (event73 (q:Int) e) := by
    exact (tally_or (piecePoints q 23) (event71 (q:Int) e) (event72 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 23) (event71 (q:Int) e) + tally (piecePoints q 23) (event72 (q:Int) e) - tally (piecePoints q 23) (event73 (q:Int) e))=Identity_left1_0.term_71 (q:Int) e + Identity_left1_0.term_72 (q:Int) e + Identity_left1_0.term_73 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 23) (event71 (q:Int) e)=Identity_left1_0.term_71 (q:Int) e at h71
  change (1:Int)*2*tally (piecePoints q 23) (event72 (q:Int) e)=Identity_left1_0.term_72 (q:Int) e at h72
  change (-1:Int)*2*tally (piecePoints q 23) (event73 (q:Int) e)=Identity_left1_0.term_73 (q:Int) e at h73
  omega
#print axioms payload23_count
theorem payload24_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 24) (payload (q:Int) e 24)=Identity_left1_0.term_74 (q:Int) e + Identity_left1_0.term_75 (q:Int) e + Identity_left1_0.term_76 (q:Int) e := by
  have h74 := atom74_count (q:Int) e
  have h75 := atom75_count (q:Int) e
  have h76 := atom76_count (q:Int) e
  have ht : tally (piecePoints q 24) (payload (q:Int) e 24)=tally (piecePoints q 24) (event74 (q:Int) e) + tally (piecePoints q 24) (event75 (q:Int) e) - tally (piecePoints q 24) (event76 (q:Int) e) := by
    exact (tally_or (piecePoints q 24) (event74 (q:Int) e) (event75 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 24) (event74 (q:Int) e) + tally (piecePoints q 24) (event75 (q:Int) e) - tally (piecePoints q 24) (event76 (q:Int) e))=Identity_left1_0.term_74 (q:Int) e + Identity_left1_0.term_75 (q:Int) e + Identity_left1_0.term_76 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 24) (event74 (q:Int) e)=Identity_left1_0.term_74 (q:Int) e at h74
  change (1:Int)*2*tally (piecePoints q 24) (event75 (q:Int) e)=Identity_left1_0.term_75 (q:Int) e at h75
  change (-1:Int)*2*tally (piecePoints q 24) (event76 (q:Int) e)=Identity_left1_0.term_76 (q:Int) e at h76
  omega
#print axioms payload24_count
theorem payload25_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 25) (payload (q:Int) e 25)=Identity_left1_0.term_77 (q:Int) e + Identity_left1_0.term_78 (q:Int) e + Identity_left1_0.term_79 (q:Int) e := by
  have h77 := atom77_count (q:Int) e
  have h78 := atom78_count (q:Int) e
  have h79 := atom79_count (q:Int) e
  have ht : tally (piecePoints q 25) (payload (q:Int) e 25)=tally (piecePoints q 25) (event77 (q:Int) e) + tally (piecePoints q 25) (event78 (q:Int) e) - tally (piecePoints q 25) (event79 (q:Int) e) := by
    exact (tally_or (piecePoints q 25) (event77 (q:Int) e) (event78 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 25) (event77 (q:Int) e) + tally (piecePoints q 25) (event78 (q:Int) e) - tally (piecePoints q 25) (event79 (q:Int) e))=Identity_left1_0.term_77 (q:Int) e + Identity_left1_0.term_78 (q:Int) e + Identity_left1_0.term_79 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 25) (event77 (q:Int) e)=Identity_left1_0.term_77 (q:Int) e at h77
  change (1:Int)*2*tally (piecePoints q 25) (event78 (q:Int) e)=Identity_left1_0.term_78 (q:Int) e at h78
  change (-1:Int)*2*tally (piecePoints q 25) (event79 (q:Int) e)=Identity_left1_0.term_79 (q:Int) e at h79
  omega
#print axioms payload25_count
theorem payload26_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 26) (payload (q:Int) e 26)=Identity_left1_0.term_80 (q:Int) e + Identity_left1_0.term_81 (q:Int) e + Identity_left1_0.term_82 (q:Int) e := by
  have h80 := atom80_count (q:Int) e
  have h81 := atom81_count (q:Int) e
  have h82 := atom82_count (q:Int) e
  have ht : tally (piecePoints q 26) (payload (q:Int) e 26)=tally (piecePoints q 26) (event80 (q:Int) e) + tally (piecePoints q 26) (event81 (q:Int) e) - tally (piecePoints q 26) (event82 (q:Int) e) := by
    exact (tally_or (piecePoints q 26) (event80 (q:Int) e) (event81 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 26) (event80 (q:Int) e) + tally (piecePoints q 26) (event81 (q:Int) e) - tally (piecePoints q 26) (event82 (q:Int) e))=Identity_left1_0.term_80 (q:Int) e + Identity_left1_0.term_81 (q:Int) e + Identity_left1_0.term_82 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 26) (event80 (q:Int) e)=Identity_left1_0.term_80 (q:Int) e at h80
  change (1:Int)*2*tally (piecePoints q 26) (event81 (q:Int) e)=Identity_left1_0.term_81 (q:Int) e at h81
  change (-1:Int)*2*tally (piecePoints q 26) (event82 (q:Int) e)=Identity_left1_0.term_82 (q:Int) e at h82
  omega
#print axioms payload26_count
theorem payload27_count (q : Nat) (e : Int) :
    (-1:Int)*2*tally (piecePoints q 27) (payload (q:Int) e 27)=Identity_left1_0.term_83 (q:Int) e := by
  have h83 := atom83_count (q:Int) e
  exact h83
#print axioms payload27_count
theorem payload28_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 28) (payload (q:Int) e 28)=Identity_left1_0.term_84 (q:Int) e + Identity_left1_0.term_85 (q:Int) e + Identity_left1_0.term_86 (q:Int) e := by
  have h84 := atom84_count (q:Int) e
  have h85 := atom85_count (q:Int) e
  have h86 := atom86_count (q:Int) e
  have ht : tally (piecePoints q 28) (payload (q:Int) e 28)=tally (piecePoints q 28) (event84 (q:Int) e) + tally (piecePoints q 28) (event85 (q:Int) e) - tally (piecePoints q 28) (event86 (q:Int) e) := by
    exact (tally_or (piecePoints q 28) (event84 (q:Int) e) (event85 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 28) (event84 (q:Int) e) + tally (piecePoints q 28) (event85 (q:Int) e) - tally (piecePoints q 28) (event86 (q:Int) e))=Identity_left1_0.term_84 (q:Int) e + Identity_left1_0.term_85 (q:Int) e + Identity_left1_0.term_86 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 28) (event84 (q:Int) e)=Identity_left1_0.term_84 (q:Int) e at h84
  change (1:Int)*2*tally (piecePoints q 28) (event85 (q:Int) e)=Identity_left1_0.term_85 (q:Int) e at h85
  change (-1:Int)*2*tally (piecePoints q 28) (event86 (q:Int) e)=Identity_left1_0.term_86 (q:Int) e at h86
  omega
#print axioms payload28_count
theorem payload29_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 29) (payload (q:Int) e 29)=Identity_left1_0.term_87 (q:Int) e + Identity_left1_0.term_88 (q:Int) e + Identity_left1_0.term_89 (q:Int) e := by
  have h87 := atom87_count (q:Int) e
  have h88 := atom88_count (q:Int) e
  have h89 := atom89_count (q:Int) e
  have ht : tally (piecePoints q 29) (payload (q:Int) e 29)=tally (piecePoints q 29) (event87 (q:Int) e) + tally (piecePoints q 29) (event88 (q:Int) e) - tally (piecePoints q 29) (event89 (q:Int) e) := by
    exact (tally_or (piecePoints q 29) (event87 (q:Int) e) (event88 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 29) (event87 (q:Int) e) + tally (piecePoints q 29) (event88 (q:Int) e) - tally (piecePoints q 29) (event89 (q:Int) e))=Identity_left1_0.term_87 (q:Int) e + Identity_left1_0.term_88 (q:Int) e + Identity_left1_0.term_89 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 29) (event87 (q:Int) e)=Identity_left1_0.term_87 (q:Int) e at h87
  change (1:Int)*2*tally (piecePoints q 29) (event88 (q:Int) e)=Identity_left1_0.term_88 (q:Int) e at h88
  change (-1:Int)*2*tally (piecePoints q 29) (event89 (q:Int) e)=Identity_left1_0.term_89 (q:Int) e at h89
  omega
#print axioms payload29_count
theorem payload30_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 30) (payload (q:Int) e 30)=Identity_left1_0.term_90 (q:Int) e + Identity_left1_0.term_91 (q:Int) e + Identity_left1_0.term_92 (q:Int) e := by
  have h90 := atom90_count (q:Int) e
  have h91 := atom91_count (q:Int) e
  have h92 := atom92_count (q:Int) e
  have ht : tally (piecePoints q 30) (payload (q:Int) e 30)=tally (piecePoints q 30) (event90 (q:Int) e) + tally (piecePoints q 30) (event91 (q:Int) e) - tally (piecePoints q 30) (event92 (q:Int) e) := by
    exact (tally_or (piecePoints q 30) (event90 (q:Int) e) (event91 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 30) (event90 (q:Int) e) + tally (piecePoints q 30) (event91 (q:Int) e) - tally (piecePoints q 30) (event92 (q:Int) e))=Identity_left1_0.term_90 (q:Int) e + Identity_left1_0.term_91 (q:Int) e + Identity_left1_0.term_92 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 30) (event90 (q:Int) e)=Identity_left1_0.term_90 (q:Int) e at h90
  change (1:Int)*2*tally (piecePoints q 30) (event91 (q:Int) e)=Identity_left1_0.term_91 (q:Int) e at h91
  change (-1:Int)*2*tally (piecePoints q 30) (event92 (q:Int) e)=Identity_left1_0.term_92 (q:Int) e at h92
  omega
#print axioms payload30_count
theorem payload31_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 31) (payload (q:Int) e 31)=Identity_left1_0.term_93 (q:Int) e := by
  have h93 := atom93_count (q:Int) e
  exact h93
#print axioms payload31_count
theorem payload32_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 32) (payload (q:Int) e 32)=Identity_left1_0.term_94 (q:Int) e + Identity_left1_0.term_95 (q:Int) e + Identity_left1_0.term_96 (q:Int) e + Identity_left1_0.term_97 (q:Int) e + Identity_left1_0.term_98 (q:Int) e + Identity_left1_0.term_99 (q:Int) e + Identity_left1_0.term_100 (q:Int) e := by
  have h94 := atom94_count (q:Int) e
  have h95 := atom95_count (q:Int) e
  have h96 := atom96_count (q:Int) e
  have h97 := atom97_count (q:Int) e
  have h98 := atom98_count (q:Int) e
  have h99 := atom99_count (q:Int) e
  have h100 := atom100_count (q:Int) e
  have ht : tally (piecePoints q 32) (payload (q:Int) e 32)=tally (piecePoints q 32) (event94 (q:Int) e) + tally (piecePoints q 32) (event95 (q:Int) e) + tally (piecePoints q 32) (event96 (q:Int) e) - tally (piecePoints q 32) (event97 (q:Int) e) - tally (piecePoints q 32) (event98 (q:Int) e) - tally (piecePoints q 32) (event99 (q:Int) e) + tally (piecePoints q 32) (event100 (q:Int) e) := by
    exact (tally_or3 (piecePoints q 32) (event94 (q:Int) e) (event95 (q:Int) e) (event96 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 32) (event94 (q:Int) e) + tally (piecePoints q 32) (event95 (q:Int) e) + tally (piecePoints q 32) (event96 (q:Int) e) - tally (piecePoints q 32) (event97 (q:Int) e) - tally (piecePoints q 32) (event98 (q:Int) e) - tally (piecePoints q 32) (event99 (q:Int) e) + tally (piecePoints q 32) (event100 (q:Int) e))=Identity_left1_0.term_94 (q:Int) e + Identity_left1_0.term_95 (q:Int) e + Identity_left1_0.term_96 (q:Int) e + Identity_left1_0.term_97 (q:Int) e + Identity_left1_0.term_98 (q:Int) e + Identity_left1_0.term_99 (q:Int) e + Identity_left1_0.term_100 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 32) (event94 (q:Int) e)=Identity_left1_0.term_94 (q:Int) e at h94
  change (1:Int)*2*tally (piecePoints q 32) (event95 (q:Int) e)=Identity_left1_0.term_95 (q:Int) e at h95
  change (1:Int)*2*tally (piecePoints q 32) (event96 (q:Int) e)=Identity_left1_0.term_96 (q:Int) e at h96
  change (-1:Int)*2*tally (piecePoints q 32) (event97 (q:Int) e)=Identity_left1_0.term_97 (q:Int) e at h97
  change (-1:Int)*2*tally (piecePoints q 32) (event98 (q:Int) e)=Identity_left1_0.term_98 (q:Int) e at h98
  change (-1:Int)*2*tally (piecePoints q 32) (event99 (q:Int) e)=Identity_left1_0.term_99 (q:Int) e at h99
  change (1:Int)*2*tally (piecePoints q 32) (event100 (q:Int) e)=Identity_left1_0.term_100 (q:Int) e at h100
  omega
#print axioms payload32_count
theorem payload33_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 33) (payload (q:Int) e 33)=Identity_left1_0.term_101 (q:Int) e + Identity_left1_0.term_102 (q:Int) e + Identity_left1_0.term_103 (q:Int) e + Identity_left1_0.term_104 (q:Int) e + Identity_left1_0.term_105 (q:Int) e + Identity_left1_0.term_106 (q:Int) e + Identity_left1_0.term_107 (q:Int) e := by
  have h101 := atom101_count (q:Int) e
  have h102 := atom102_count (q:Int) e
  have h103 := atom103_count (q:Int) e
  have h104 := atom104_count (q:Int) e
  have h105 := atom105_count (q:Int) e
  have h106 := atom106_count (q:Int) e
  have h107 := atom107_count (q:Int) e
  have ht : tally (piecePoints q 33) (payload (q:Int) e 33)=tally (piecePoints q 33) (event101 (q:Int) e) + tally (piecePoints q 33) (event102 (q:Int) e) + tally (piecePoints q 33) (event103 (q:Int) e) - tally (piecePoints q 33) (event104 (q:Int) e) - tally (piecePoints q 33) (event105 (q:Int) e) - tally (piecePoints q 33) (event106 (q:Int) e) + tally (piecePoints q 33) (event107 (q:Int) e) := by
    exact (tally_or3 (piecePoints q 33) (event101 (q:Int) e) (event102 (q:Int) e) (event103 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 33) (event101 (q:Int) e) + tally (piecePoints q 33) (event102 (q:Int) e) + tally (piecePoints q 33) (event103 (q:Int) e) - tally (piecePoints q 33) (event104 (q:Int) e) - tally (piecePoints q 33) (event105 (q:Int) e) - tally (piecePoints q 33) (event106 (q:Int) e) + tally (piecePoints q 33) (event107 (q:Int) e))=Identity_left1_0.term_101 (q:Int) e + Identity_left1_0.term_102 (q:Int) e + Identity_left1_0.term_103 (q:Int) e + Identity_left1_0.term_104 (q:Int) e + Identity_left1_0.term_105 (q:Int) e + Identity_left1_0.term_106 (q:Int) e + Identity_left1_0.term_107 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 33) (event101 (q:Int) e)=Identity_left1_0.term_101 (q:Int) e at h101
  change (1:Int)*2*tally (piecePoints q 33) (event102 (q:Int) e)=Identity_left1_0.term_102 (q:Int) e at h102
  change (1:Int)*2*tally (piecePoints q 33) (event103 (q:Int) e)=Identity_left1_0.term_103 (q:Int) e at h103
  change (-1:Int)*2*tally (piecePoints q 33) (event104 (q:Int) e)=Identity_left1_0.term_104 (q:Int) e at h104
  change (-1:Int)*2*tally (piecePoints q 33) (event105 (q:Int) e)=Identity_left1_0.term_105 (q:Int) e at h105
  change (-1:Int)*2*tally (piecePoints q 33) (event106 (q:Int) e)=Identity_left1_0.term_106 (q:Int) e at h106
  change (1:Int)*2*tally (piecePoints q 33) (event107 (q:Int) e)=Identity_left1_0.term_107 (q:Int) e at h107
  omega
#print axioms payload33_count
theorem payload34_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 34) (payload (q:Int) e 34)=Identity_left1_0.term_108 (q:Int) e + Identity_left1_0.term_109 (q:Int) e + Identity_left1_0.term_110 (q:Int) e := by
  have h108 := atom108_count (q:Int) e
  have h109 := atom109_count (q:Int) e
  have h110 := atom110_count (q:Int) e
  have ht : tally (piecePoints q 34) (payload (q:Int) e 34)=tally (piecePoints q 34) (event108 (q:Int) e) + tally (piecePoints q 34) (event109 (q:Int) e) - tally (piecePoints q 34) (event110 (q:Int) e) := by
    exact (tally_or (piecePoints q 34) (event108 (q:Int) e) (event109 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 34) (event108 (q:Int) e) + tally (piecePoints q 34) (event109 (q:Int) e) - tally (piecePoints q 34) (event110 (q:Int) e))=Identity_left1_0.term_108 (q:Int) e + Identity_left1_0.term_109 (q:Int) e + Identity_left1_0.term_110 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 34) (event108 (q:Int) e)=Identity_left1_0.term_108 (q:Int) e at h108
  change (1:Int)*2*tally (piecePoints q 34) (event109 (q:Int) e)=Identity_left1_0.term_109 (q:Int) e at h109
  change (-1:Int)*2*tally (piecePoints q 34) (event110 (q:Int) e)=Identity_left1_0.term_110 (q:Int) e at h110
  omega
#print axioms payload34_count
theorem payload35_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 35) (payload (q:Int) e 35)=Identity_left1_0.term_111 (q:Int) e + Identity_left1_0.term_112 (q:Int) e + Identity_left1_0.term_113 (q:Int) e := by
  have h111 := atom111_count (q:Int) e
  have h112 := atom112_count (q:Int) e
  have h113 := atom113_count (q:Int) e
  have ht : tally (piecePoints q 35) (payload (q:Int) e 35)=tally (piecePoints q 35) (event111 (q:Int) e) + tally (piecePoints q 35) (event112 (q:Int) e) - tally (piecePoints q 35) (event113 (q:Int) e) := by
    exact (tally_or (piecePoints q 35) (event111 (q:Int) e) (event112 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 35) (event111 (q:Int) e) + tally (piecePoints q 35) (event112 (q:Int) e) - tally (piecePoints q 35) (event113 (q:Int) e))=Identity_left1_0.term_111 (q:Int) e + Identity_left1_0.term_112 (q:Int) e + Identity_left1_0.term_113 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 35) (event111 (q:Int) e)=Identity_left1_0.term_111 (q:Int) e at h111
  change (1:Int)*2*tally (piecePoints q 35) (event112 (q:Int) e)=Identity_left1_0.term_112 (q:Int) e at h112
  change (-1:Int)*2*tally (piecePoints q 35) (event113 (q:Int) e)=Identity_left1_0.term_113 (q:Int) e at h113
  omega
#print axioms payload35_count
theorem payload36_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 36) (payload (q:Int) e 36)=Identity_left1_0.term_114 (q:Int) e + Identity_left1_0.term_115 (q:Int) e + Identity_left1_0.term_116 (q:Int) e := by
  have h114 := atom114_count (q:Int) e
  have h115 := atom115_count (q:Int) e
  have h116 := atom116_count (q:Int) e
  have ht : tally (piecePoints q 36) (payload (q:Int) e 36)=tally (piecePoints q 36) (event114 (q:Int) e) + tally (piecePoints q 36) (event115 (q:Int) e) - tally (piecePoints q 36) (event116 (q:Int) e) := by
    exact (tally_or (piecePoints q 36) (event114 (q:Int) e) (event115 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 36) (event114 (q:Int) e) + tally (piecePoints q 36) (event115 (q:Int) e) - tally (piecePoints q 36) (event116 (q:Int) e))=Identity_left1_0.term_114 (q:Int) e + Identity_left1_0.term_115 (q:Int) e + Identity_left1_0.term_116 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 36) (event114 (q:Int) e)=Identity_left1_0.term_114 (q:Int) e at h114
  change (1:Int)*2*tally (piecePoints q 36) (event115 (q:Int) e)=Identity_left1_0.term_115 (q:Int) e at h115
  change (-1:Int)*2*tally (piecePoints q 36) (event116 (q:Int) e)=Identity_left1_0.term_116 (q:Int) e at h116
  omega
#print axioms payload36_count
theorem payload37_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 37) (payload (q:Int) e 37)=Identity_left1_0.term_117 (q:Int) e + Identity_left1_0.term_118 (q:Int) e + Identity_left1_0.term_119 (q:Int) e := by
  have h117 := atom117_count (q:Int) e
  have h118 := atom118_count (q:Int) e
  have h119 := atom119_count (q:Int) e
  have ht : tally (piecePoints q 37) (payload (q:Int) e 37)=tally (piecePoints q 37) (event117 (q:Int) e) + tally (piecePoints q 37) (event118 (q:Int) e) - tally (piecePoints q 37) (event119 (q:Int) e) := by
    exact (tally_or (piecePoints q 37) (event117 (q:Int) e) (event118 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 37) (event117 (q:Int) e) + tally (piecePoints q 37) (event118 (q:Int) e) - tally (piecePoints q 37) (event119 (q:Int) e))=Identity_left1_0.term_117 (q:Int) e + Identity_left1_0.term_118 (q:Int) e + Identity_left1_0.term_119 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 37) (event117 (q:Int) e)=Identity_left1_0.term_117 (q:Int) e at h117
  change (1:Int)*2*tally (piecePoints q 37) (event118 (q:Int) e)=Identity_left1_0.term_118 (q:Int) e at h118
  change (-1:Int)*2*tally (piecePoints q 37) (event119 (q:Int) e)=Identity_left1_0.term_119 (q:Int) e at h119
  omega
#print axioms payload37_count
theorem payload38_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 38) (payload (q:Int) e 38)=Identity_left1_0.term_120 (q:Int) e + Identity_left1_0.term_121 (q:Int) e + Identity_left1_0.term_122 (q:Int) e := by
  have h120 := atom120_count (q:Int) e
  have h121 := atom121_count (q:Int) e
  have h122 := atom122_count (q:Int) e
  have ht : tally (piecePoints q 38) (payload (q:Int) e 38)=tally (piecePoints q 38) (event120 (q:Int) e) + tally (piecePoints q 38) (event121 (q:Int) e) - tally (piecePoints q 38) (event122 (q:Int) e) := by
    exact (tally_or (piecePoints q 38) (event120 (q:Int) e) (event121 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 38) (event120 (q:Int) e) + tally (piecePoints q 38) (event121 (q:Int) e) - tally (piecePoints q 38) (event122 (q:Int) e))=Identity_left1_0.term_120 (q:Int) e + Identity_left1_0.term_121 (q:Int) e + Identity_left1_0.term_122 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 38) (event120 (q:Int) e)=Identity_left1_0.term_120 (q:Int) e at h120
  change (1:Int)*2*tally (piecePoints q 38) (event121 (q:Int) e)=Identity_left1_0.term_121 (q:Int) e at h121
  change (-1:Int)*2*tally (piecePoints q 38) (event122 (q:Int) e)=Identity_left1_0.term_122 (q:Int) e at h122
  omega
#print axioms payload38_count
theorem payload39_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 39) (payload (q:Int) e 39)=Identity_left1_0.term_123 (q:Int) e := by
  have h123 := atom123_count (q:Int) e
  exact h123
#print axioms payload39_count
theorem payload40_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 40) (payload (q:Int) e 40)=Identity_left1_0.term_124 (q:Int) e := by
  have h124 := atom124_count (q:Int) e
  exact h124
#print axioms payload40_count
theorem payload41_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 41) (payload (q:Int) e 41)=Identity_left1_0.term_125 (q:Int) e + Identity_left1_0.term_126 (q:Int) e + Identity_left1_0.term_127 (q:Int) e := by
  have h125 := atom125_count (q:Int) e
  have h126 := atom126_count (q:Int) e
  have h127 := atom127_count (q:Int) e
  have ht : tally (piecePoints q 41) (payload (q:Int) e 41)=tally (piecePoints q 41) (event125 (q:Int) e) + tally (piecePoints q 41) (event126 (q:Int) e) - tally (piecePoints q 41) (event127 (q:Int) e) := by
    exact (tally_or (piecePoints q 41) (event125 (q:Int) e) (event126 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 41) (event125 (q:Int) e) + tally (piecePoints q 41) (event126 (q:Int) e) - tally (piecePoints q 41) (event127 (q:Int) e))=Identity_left1_0.term_125 (q:Int) e + Identity_left1_0.term_126 (q:Int) e + Identity_left1_0.term_127 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 41) (event125 (q:Int) e)=Identity_left1_0.term_125 (q:Int) e at h125
  change (1:Int)*2*tally (piecePoints q 41) (event126 (q:Int) e)=Identity_left1_0.term_126 (q:Int) e at h126
  change (-1:Int)*2*tally (piecePoints q 41) (event127 (q:Int) e)=Identity_left1_0.term_127 (q:Int) e at h127
  omega
#print axioms payload41_count
theorem payload42_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 42) (payload (q:Int) e 42)=Identity_left1_0.term_128 (q:Int) e + Identity_left1_0.term_129 (q:Int) e + Identity_left1_0.term_130 (q:Int) e := by
  have h128 := atom128_count (q:Int) e
  have h129 := atom129_count (q:Int) e
  have h130 := atom130_count (q:Int) e
  have ht : tally (piecePoints q 42) (payload (q:Int) e 42)=tally (piecePoints q 42) (event128 (q:Int) e) + tally (piecePoints q 42) (event129 (q:Int) e) - tally (piecePoints q 42) (event130 (q:Int) e) := by
    exact (tally_or (piecePoints q 42) (event128 (q:Int) e) (event129 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 42) (event128 (q:Int) e) + tally (piecePoints q 42) (event129 (q:Int) e) - tally (piecePoints q 42) (event130 (q:Int) e))=Identity_left1_0.term_128 (q:Int) e + Identity_left1_0.term_129 (q:Int) e + Identity_left1_0.term_130 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 42) (event128 (q:Int) e)=Identity_left1_0.term_128 (q:Int) e at h128
  change (1:Int)*2*tally (piecePoints q 42) (event129 (q:Int) e)=Identity_left1_0.term_129 (q:Int) e at h129
  change (-1:Int)*2*tally (piecePoints q 42) (event130 (q:Int) e)=Identity_left1_0.term_130 (q:Int) e at h130
  omega
#print axioms payload42_count
theorem payload43_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 43) (payload (q:Int) e 43)=Identity_left1_0.term_131 (q:Int) e + Identity_left1_0.term_132 (q:Int) e + Identity_left1_0.term_133 (q:Int) e := by
  have h131 := atom131_count (q:Int) e
  have h132 := atom132_count (q:Int) e
  have h133 := atom133_count (q:Int) e
  have ht : tally (piecePoints q 43) (payload (q:Int) e 43)=tally (piecePoints q 43) (event131 (q:Int) e) + tally (piecePoints q 43) (event132 (q:Int) e) - tally (piecePoints q 43) (event133 (q:Int) e) := by
    exact (tally_or (piecePoints q 43) (event131 (q:Int) e) (event132 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 43) (event131 (q:Int) e) + tally (piecePoints q 43) (event132 (q:Int) e) - tally (piecePoints q 43) (event133 (q:Int) e))=Identity_left1_0.term_131 (q:Int) e + Identity_left1_0.term_132 (q:Int) e + Identity_left1_0.term_133 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 43) (event131 (q:Int) e)=Identity_left1_0.term_131 (q:Int) e at h131
  change (1:Int)*2*tally (piecePoints q 43) (event132 (q:Int) e)=Identity_left1_0.term_132 (q:Int) e at h132
  change (-1:Int)*2*tally (piecePoints q 43) (event133 (q:Int) e)=Identity_left1_0.term_133 (q:Int) e at h133
  omega
#print axioms payload43_count
theorem payload44_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 44) (payload (q:Int) e 44)=Identity_left1_0.term_134 (q:Int) e := by
  have h134 := atom134_count (q:Int) e
  exact h134
#print axioms payload44_count
theorem payload45_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 45) (payload (q:Int) e 45)=Identity_left1_0.term_135 (q:Int) e + Identity_left1_0.term_136 (q:Int) e + Identity_left1_0.term_137 (q:Int) e + Identity_left1_0.term_138 (q:Int) e + Identity_left1_0.term_139 (q:Int) e + Identity_left1_0.term_140 (q:Int) e + Identity_left1_0.term_141 (q:Int) e := by
  have h135 := atom135_count (q:Int) e
  have h136 := atom136_count (q:Int) e
  have h137 := atom137_count (q:Int) e
  have h138 := atom138_count (q:Int) e
  have h139 := atom139_count (q:Int) e
  have h140 := atom140_count (q:Int) e
  have h141 := atom141_count (q:Int) e
  have ht : tally (piecePoints q 45) (payload (q:Int) e 45)=tally (piecePoints q 45) (event135 (q:Int) e) + tally (piecePoints q 45) (event136 (q:Int) e) + tally (piecePoints q 45) (event137 (q:Int) e) - tally (piecePoints q 45) (event138 (q:Int) e) - tally (piecePoints q 45) (event139 (q:Int) e) - tally (piecePoints q 45) (event140 (q:Int) e) + tally (piecePoints q 45) (event141 (q:Int) e) := by
    exact (tally_or3 (piecePoints q 45) (event135 (q:Int) e) (event136 (q:Int) e) (event137 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 45) (event135 (q:Int) e) + tally (piecePoints q 45) (event136 (q:Int) e) + tally (piecePoints q 45) (event137 (q:Int) e) - tally (piecePoints q 45) (event138 (q:Int) e) - tally (piecePoints q 45) (event139 (q:Int) e) - tally (piecePoints q 45) (event140 (q:Int) e) + tally (piecePoints q 45) (event141 (q:Int) e))=Identity_left1_0.term_135 (q:Int) e + Identity_left1_0.term_136 (q:Int) e + Identity_left1_0.term_137 (q:Int) e + Identity_left1_0.term_138 (q:Int) e + Identity_left1_0.term_139 (q:Int) e + Identity_left1_0.term_140 (q:Int) e + Identity_left1_0.term_141 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 45) (event135 (q:Int) e)=Identity_left1_0.term_135 (q:Int) e at h135
  change (1:Int)*2*tally (piecePoints q 45) (event136 (q:Int) e)=Identity_left1_0.term_136 (q:Int) e at h136
  change (1:Int)*2*tally (piecePoints q 45) (event137 (q:Int) e)=Identity_left1_0.term_137 (q:Int) e at h137
  change (-1:Int)*2*tally (piecePoints q 45) (event138 (q:Int) e)=Identity_left1_0.term_138 (q:Int) e at h138
  change (-1:Int)*2*tally (piecePoints q 45) (event139 (q:Int) e)=Identity_left1_0.term_139 (q:Int) e at h139
  change (-1:Int)*2*tally (piecePoints q 45) (event140 (q:Int) e)=Identity_left1_0.term_140 (q:Int) e at h140
  change (1:Int)*2*tally (piecePoints q 45) (event141 (q:Int) e)=Identity_left1_0.term_141 (q:Int) e at h141
  omega
#print axioms payload45_count
end
end LuRazClosure.SourcePieces
