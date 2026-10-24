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
theorem actual48_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 48) (rawPieceEvent q 48 e)=Identity_left1_0.term_146 (q:Int) (e:Int) := by
  classical
  have hs := payload48_count q (e:Int)
  have ht := tally_congr (piecePoints q 48) (rawPieceEvent q 48 e)
    (payload (q:Int) (e:Int) 48) (p48_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual48_count
theorem actual49_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 49) (rawPieceEvent q 49 e)=Identity_left1_0.term_147 (q:Int) (e:Int) := by
  classical
  have hs := payload49_count q (e:Int)
  have ht := tally_congr (piecePoints q 49) (rawPieceEvent q 49 e)
    (payload (q:Int) (e:Int) 49) (p49_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual49_count
theorem actual50_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 50) (rawPieceEvent q 50 e)=Identity_left1_0.term_148 (q:Int) (e:Int) := by
  classical
  have hs := payload50_count q (e:Int)
  have ht := tally_congr (piecePoints q 50) (rawPieceEvent q 50 e)
    (payload (q:Int) (e:Int) 50) (p50_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual50_count
theorem actual51_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 51) (rawPieceEvent q 51 e)=Identity_left1_0.term_149 (q:Int) (e:Int) := by
  classical
  have hs := payload51_count q (e:Int)
  have ht := tally_congr (piecePoints q 51) (rawPieceEvent q 51 e)
    (payload (q:Int) (e:Int) 51) (p51_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual51_count
theorem actual52_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 52) (rawPieceEvent q 52 e)=Identity_left1_0.term_150 (q:Int) (e:Int) := by
  classical
  have hs := payload52_count q (e:Int)
  have ht := tally_congr (piecePoints q 52) (rawPieceEvent q 52 e)
    (payload (q:Int) (e:Int) 52) (p52_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual52_count
theorem actual53_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 53) (rawPieceEvent q 53 e)=Identity_left1_0.term_151 (q:Int) (e:Int) := by
  classical
  have hs := payload53_count q (e:Int)
  have ht := tally_congr (piecePoints q 53) (rawPieceEvent q 53 e)
    (payload (q:Int) (e:Int) 53) (p53_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual53_count
theorem actual54_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 54) (rawPieceEvent q 54 e)=Identity_left1_0.term_152 (q:Int) (e:Int) + Identity_left1_0.term_153 (q:Int) (e:Int) + Identity_left1_0.term_154 (q:Int) (e:Int) := by
  classical
  have hs := payload54_count q (e:Int)
  have ht := tally_congr (piecePoints q 54) (rawPieceEvent q 54 e)
    (payload (q:Int) (e:Int) 54) (p54_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual54_count
theorem actual55_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 55) (rawPieceEvent q 55 e)=Identity_left1_0.term_155 (q:Int) (e:Int) + Identity_left1_0.term_156 (q:Int) (e:Int) + Identity_left1_0.term_157 (q:Int) (e:Int) := by
  classical
  have hs := payload55_count q (e:Int)
  have ht := tally_congr (piecePoints q 55) (rawPieceEvent q 55 e)
    (payload (q:Int) (e:Int) 55) (p55_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual55_count
theorem actual56_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 56) (rawPieceEvent q 56 e)=Identity_left1_0.term_158 (q:Int) (e:Int) + Identity_left1_0.term_159 (q:Int) (e:Int) + Identity_left1_0.term_160 (q:Int) (e:Int) := by
  classical
  have hs := payload56_count q (e:Int)
  have ht := tally_congr (piecePoints q 56) (rawPieceEvent q 56 e)
    (payload (q:Int) (e:Int) 56) (p56_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual56_count
theorem actual57_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 57) (rawPieceEvent q 57 e)=Identity_left1_0.term_161 (q:Int) (e:Int) + Identity_left1_0.term_162 (q:Int) (e:Int) + Identity_left1_0.term_163 (q:Int) (e:Int) := by
  classical
  have hs := payload57_count q (e:Int)
  have ht := tally_congr (piecePoints q 57) (rawPieceEvent q 57 e)
    (payload (q:Int) (e:Int) 57) (p57_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual57_count
theorem actual58_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 58) (rawPieceEvent q 58 e)=Identity_left1_0.term_164 (q:Int) (e:Int) + Identity_left1_0.term_165 (q:Int) (e:Int) + Identity_left1_0.term_166 (q:Int) (e:Int) := by
  classical
  have hs := payload58_count q (e:Int)
  have ht := tally_congr (piecePoints q 58) (rawPieceEvent q 58 e)
    (payload (q:Int) (e:Int) 58) (p58_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual58_count
theorem actual59_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 59) (rawPieceEvent q 59 e)=Identity_left1_0.term_167 (q:Int) (e:Int) + Identity_left1_0.term_168 (q:Int) (e:Int) + Identity_left1_0.term_169 (q:Int) (e:Int) := by
  classical
  have hs := payload59_count q (e:Int)
  have ht := tally_congr (piecePoints q 59) (rawPieceEvent q 59 e)
    (payload (q:Int) (e:Int) 59) (p59_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual59_count
theorem actual60_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 60) (rawPieceEvent q 60 e)=Identity_left1_0.term_170 (q:Int) (e:Int) := by
  classical
  have hs := payload60_count q (e:Int)
  have ht := tally_congr (piecePoints q 60) (rawPieceEvent q 60 e)
    (payload (q:Int) (e:Int) 60) (p60_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual60_count
theorem actual61_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 61) (rawPieceEvent q 61 e)=Identity_left1_0.term_171 (q:Int) (e:Int) + Identity_left1_0.term_172 (q:Int) (e:Int) + Identity_left1_0.term_173 (q:Int) (e:Int) := by
  classical
  have hs := payload61_count q (e:Int)
  have ht := tally_congr (piecePoints q 61) (rawPieceEvent q 61 e)
    (payload (q:Int) (e:Int) 61) (p61_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual61_count
theorem actual62_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 62) (rawPieceEvent q 62 e)=Identity_left1_0.term_174 (q:Int) (e:Int) + Identity_left1_0.term_175 (q:Int) (e:Int) + Identity_left1_0.term_176 (q:Int) (e:Int) := by
  classical
  have hs := payload62_count q (e:Int)
  have ht := tally_congr (piecePoints q 62) (rawPieceEvent q 62 e)
    (payload (q:Int) (e:Int) 62) (p62_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual62_count
theorem actual63_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 63) (rawPieceEvent q 63 e)=Identity_left1_0.term_177 (q:Int) (e:Int) + Identity_left1_0.term_178 (q:Int) (e:Int) + Identity_left1_0.term_179 (q:Int) (e:Int) := by
  classical
  have hs := payload63_count q (e:Int)
  have ht := tally_congr (piecePoints q 63) (rawPieceEvent q 63 e)
    (payload (q:Int) (e:Int) 63) (p63_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual63_count
theorem actual64_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 64) (rawPieceEvent q 64 e)=Identity_left1_0.term_180 (q:Int) (e:Int) + Identity_left1_0.term_181 (q:Int) (e:Int) + Identity_left1_0.term_182 (q:Int) (e:Int) := by
  classical
  have hs := payload64_count q (e:Int)
  have ht := tally_congr (piecePoints q 64) (rawPieceEvent q 64 e)
    (payload (q:Int) (e:Int) 64) (p64_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual64_count
theorem actual65_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 65) (rawPieceEvent q 65 e)=Identity_left1_0.term_183 (q:Int) (e:Int) + Identity_left1_0.term_184 (q:Int) (e:Int) + Identity_left1_0.term_185 (q:Int) (e:Int) + Identity_left1_0.term_186 (q:Int) (e:Int) + Identity_left1_0.term_187 (q:Int) (e:Int) + Identity_left1_0.term_188 (q:Int) (e:Int) + Identity_left1_0.term_189 (q:Int) (e:Int) := by
  classical
  have hs := payload65_count q (e:Int)
  have ht := tally_congr (piecePoints q 65) (rawPieceEvent q 65 e)
    (payload (q:Int) (e:Int) 65) (p65_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual65_count
theorem actual66_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 66) (rawPieceEvent q 66 e)=Identity_left1_0.term_190 (q:Int) (e:Int) + Identity_left1_0.term_191 (q:Int) (e:Int) + Identity_left1_0.term_192 (q:Int) (e:Int) := by
  classical
  have hs := payload66_count q (e:Int)
  have ht := tally_congr (piecePoints q 66) (rawPieceEvent q 66 e)
    (payload (q:Int) (e:Int) 66) (p66_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual66_count
theorem actual67_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 67) (rawPieceEvent q 67 e)=Identity_left1_0.term_193 (q:Int) (e:Int) + Identity_left1_0.term_194 (q:Int) (e:Int) + Identity_left1_0.term_195 (q:Int) (e:Int) := by
  classical
  have hs := payload67_count q (e:Int)
  have ht := tally_congr (piecePoints q 67) (rawPieceEvent q 67 e)
    (payload (q:Int) (e:Int) 67) (p67_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual67_count
theorem actual68_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 68) (rawPieceEvent q 68 e)=Identity_left1_0.term_196 (q:Int) (e:Int) + Identity_left1_0.term_197 (q:Int) (e:Int) + Identity_left1_0.term_198 (q:Int) (e:Int) := by
  classical
  have hs := payload68_count q (e:Int)
  have ht := tally_congr (piecePoints q 68) (rawPieceEvent q 68 e)
    (payload (q:Int) (e:Int) 68) (p68_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual68_count
theorem actual69_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 69) (rawPieceEvent q 69 e)=Identity_left1_0.term_199 (q:Int) (e:Int) + Identity_left1_0.term_200 (q:Int) (e:Int) + Identity_left1_0.term_201 (q:Int) (e:Int) + Identity_left1_0.term_202 (q:Int) (e:Int) + Identity_left1_0.term_203 (q:Int) (e:Int) + Identity_left1_0.term_204 (q:Int) (e:Int) + Identity_left1_0.term_205 (q:Int) (e:Int) := by
  classical
  have hs := payload69_count q (e:Int)
  have ht := tally_congr (piecePoints q 69) (rawPieceEvent q 69 e)
    (payload (q:Int) (e:Int) 69) (p69_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual69_count
theorem actual70_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 70) (rawPieceEvent q 70 e)=Identity_left1_0.term_206 (q:Int) (e:Int) + Identity_left1_0.term_207 (q:Int) (e:Int) + Identity_left1_0.term_208 (q:Int) (e:Int) + Identity_left1_0.term_209 (q:Int) (e:Int) + Identity_left1_0.term_210 (q:Int) (e:Int) + Identity_left1_0.term_211 (q:Int) (e:Int) + Identity_left1_0.term_212 (q:Int) (e:Int) := by
  classical
  have hs := payload70_count q (e:Int)
  have ht := tally_congr (piecePoints q 70) (rawPieceEvent q 70 e)
    (payload (q:Int) (e:Int) 70) (p70_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual70_count
end
end LuRazClosure.SourcePieces
