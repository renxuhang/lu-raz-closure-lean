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
theorem actual71_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 71) (rawPieceEvent q 71 e)=Identity_left1_0.term_213 (q:Int) (e:Int) + Identity_left1_0.term_214 (q:Int) (e:Int) + Identity_left1_0.term_215 (q:Int) (e:Int) := by
  classical
  have hs := payload71_count q (e:Int)
  have ht := tally_congr (piecePoints q 71) (rawPieceEvent q 71 e)
    (payload (q:Int) (e:Int) 71) (p71_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual71_count
theorem actual72_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 72) (rawPieceEvent q 72 e)=Identity_left1_0.term_216 (q:Int) (e:Int) + Identity_left1_0.term_217 (q:Int) (e:Int) + Identity_left1_0.term_218 (q:Int) (e:Int) := by
  classical
  have hs := payload72_count q (e:Int)
  have ht := tally_congr (piecePoints q 72) (rawPieceEvent q 72 e)
    (payload (q:Int) (e:Int) 72) (p72_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual72_count
theorem actual73_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 73) (rawPieceEvent q 73 e)=Identity_left1_0.term_219 (q:Int) (e:Int) + Identity_left1_0.term_220 (q:Int) (e:Int) + Identity_left1_0.term_221 (q:Int) (e:Int) := by
  classical
  have hs := payload73_count q (e:Int)
  have ht := tally_congr (piecePoints q 73) (rawPieceEvent q 73 e)
    (payload (q:Int) (e:Int) 73) (p73_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual73_count
theorem actual74_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 74) (rawPieceEvent q 74 e)=Identity_left1_0.term_222 (q:Int) (e:Int) + Identity_left1_0.term_223 (q:Int) (e:Int) + Identity_left1_0.term_224 (q:Int) (e:Int) := by
  classical
  have hs := payload74_count q (e:Int)
  have ht := tally_congr (piecePoints q 74) (rawPieceEvent q 74 e)
    (payload (q:Int) (e:Int) 74) (p74_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual74_count
theorem actual75_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 75) (rawPieceEvent q 75 e)=Identity_left1_0.term_225 (q:Int) (e:Int) + Identity_left1_0.term_226 (q:Int) (e:Int) + Identity_left1_0.term_227 (q:Int) (e:Int) := by
  classical
  have hs := payload75_count q (e:Int)
  have ht := tally_congr (piecePoints q 75) (rawPieceEvent q 75 e)
    (payload (q:Int) (e:Int) 75) (p75_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual75_count
theorem actual76_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 76) (rawPieceEvent q 76 e)=Identity_left1_0.term_228 (q:Int) (e:Int) := by
  classical
  have hs := payload76_count q (e:Int)
  have ht := tally_congr (piecePoints q 76) (rawPieceEvent q 76 e)
    (payload (q:Int) (e:Int) 76) (p76_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual76_count
theorem actual77_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 77) (rawPieceEvent q 77 e)=Identity_left1_0.term_229 (q:Int) (e:Int) + Identity_left1_0.term_230 (q:Int) (e:Int) + Identity_left1_0.term_231 (q:Int) (e:Int) := by
  classical
  have hs := payload77_count q (e:Int)
  have ht := tally_congr (piecePoints q 77) (rawPieceEvent q 77 e)
    (payload (q:Int) (e:Int) 77) (p77_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual77_count
theorem actual78_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 78) (rawPieceEvent q 78 e)=Identity_left1_0.term_232 (q:Int) (e:Int) := by
  classical
  have hs := payload78_count q (e:Int)
  have ht := tally_congr (piecePoints q 78) (rawPieceEvent q 78 e)
    (payload (q:Int) (e:Int) 78) (p78_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual78_count
theorem actual79_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 79) (rawPieceEvent q 79 e)=Identity_left1_0.term_233 (q:Int) (e:Int) + Identity_left1_0.term_234 (q:Int) (e:Int) + Identity_left1_0.term_235 (q:Int) (e:Int) := by
  classical
  have hs := payload79_count q (e:Int)
  have ht := tally_congr (piecePoints q 79) (rawPieceEvent q 79 e)
    (payload (q:Int) (e:Int) 79) (p79_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual79_count
theorem actual80_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 80) (rawPieceEvent q 80 e)=Identity_left1_0.term_236 (q:Int) (e:Int) + Identity_left1_0.term_237 (q:Int) (e:Int) + Identity_left1_0.term_238 (q:Int) (e:Int) := by
  classical
  have hs := payload80_count q (e:Int)
  have ht := tally_congr (piecePoints q 80) (rawPieceEvent q 80 e)
    (payload (q:Int) (e:Int) 80) (p80_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual80_count
theorem actual81_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 81) (rawPieceEvent q 81 e)=Identity_left1_0.term_239 (q:Int) (e:Int) + Identity_left1_0.term_240 (q:Int) (e:Int) + Identity_left1_0.term_241 (q:Int) (e:Int) := by
  classical
  have hs := payload81_count q (e:Int)
  have ht := tally_congr (piecePoints q 81) (rawPieceEvent q 81 e)
    (payload (q:Int) (e:Int) 81) (p81_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual81_count
theorem actual82_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 82) (rawPieceEvent q 82 e)=Identity_left1_0.term_242 (q:Int) (e:Int) + Identity_left1_0.term_243 (q:Int) (e:Int) + Identity_left1_0.term_244 (q:Int) (e:Int) := by
  classical
  have hs := payload82_count q (e:Int)
  have ht := tally_congr (piecePoints q 82) (rawPieceEvent q 82 e)
    (payload (q:Int) (e:Int) 82) (p82_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual82_count
theorem actual83_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 83) (rawPieceEvent q 83 e)=Identity_left1_0.term_245 (q:Int) (e:Int) + Identity_left1_0.term_246 (q:Int) (e:Int) + Identity_left1_0.term_247 (q:Int) (e:Int) := by
  classical
  have hs := payload83_count q (e:Int)
  have ht := tally_congr (piecePoints q 83) (rawPieceEvent q 83 e)
    (payload (q:Int) (e:Int) 83) (p83_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual83_count
theorem actual84_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 84) (rawPieceEvent q 84 e)=Identity_left1_0.term_248 (q:Int) (e:Int) + Identity_left1_0.term_249 (q:Int) (e:Int) + Identity_left1_0.term_250 (q:Int) (e:Int) := by
  classical
  have hs := payload84_count q (e:Int)
  have ht := tally_congr (piecePoints q 84) (rawPieceEvent q 84 e)
    (payload (q:Int) (e:Int) 84) (p84_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual84_count
theorem actual85_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 85) (rawPieceEvent q 85 e)=Identity_left1_0.term_251 (q:Int) (e:Int) + Identity_left1_0.term_252 (q:Int) (e:Int) + Identity_left1_0.term_253 (q:Int) (e:Int) + Identity_left1_0.term_254 (q:Int) (e:Int) + Identity_left1_0.term_255 (q:Int) (e:Int) + Identity_left1_0.term_256 (q:Int) (e:Int) + Identity_left1_0.term_257 (q:Int) (e:Int) := by
  classical
  have hs := payload85_count q (e:Int)
  have ht := tally_congr (piecePoints q 85) (rawPieceEvent q 85 e)
    (payload (q:Int) (e:Int) 85) (p85_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual85_count
theorem actual86_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 86) (rawPieceEvent q 86 e)=Identity_left1_0.term_258 (q:Int) (e:Int) + Identity_left1_0.term_259 (q:Int) (e:Int) + Identity_left1_0.term_260 (q:Int) (e:Int) := by
  classical
  have hs := payload86_count q (e:Int)
  have ht := tally_congr (piecePoints q 86) (rawPieceEvent q 86 e)
    (payload (q:Int) (e:Int) 86) (p86_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual86_count
theorem actual87_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 87) (rawPieceEvent q 87 e)=Identity_left1_0.term_261 (q:Int) (e:Int) := by
  classical
  have hs := payload87_count q (e:Int)
  have ht := tally_congr (piecePoints q 87) (rawPieceEvent q 87 e)
    (payload (q:Int) (e:Int) 87) (p87_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual87_count
theorem actual88_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 88) (rawPieceEvent q 88 e)=Identity_left1_0.term_262 (q:Int) (e:Int) + Identity_left1_0.term_263 (q:Int) (e:Int) + Identity_left1_0.term_264 (q:Int) (e:Int) := by
  classical
  have hs := payload88_count q (e:Int)
  have ht := tally_congr (piecePoints q 88) (rawPieceEvent q 88 e)
    (payload (q:Int) (e:Int) 88) (p88_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual88_count
theorem actual89_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 89) (rawPieceEvent q 89 e)=Identity_left1_0.term_265 (q:Int) (e:Int) := by
  classical
  have hs := payload89_count q (e:Int)
  have ht := tally_congr (piecePoints q 89) (rawPieceEvent q 89 e)
    (payload (q:Int) (e:Int) 89) (p89_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual89_count
theorem actual90_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 90) (rawPieceEvent q 90 e)=Identity_left1_0.term_266 (q:Int) (e:Int) + Identity_left1_0.term_267 (q:Int) (e:Int) + Identity_left1_0.term_268 (q:Int) (e:Int) := by
  classical
  have hs := payload90_count q (e:Int)
  have ht := tally_congr (piecePoints q 90) (rawPieceEvent q 90 e)
    (payload (q:Int) (e:Int) 90) (p90_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual90_count
theorem actual91_count (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    2*tally (piecePoints q 91) (rawPieceEvent q 91 e)=Identity_left1_0.term_269 (q:Int) (e:Int) + Identity_left1_0.term_270 (q:Int) (e:Int) + Identity_left1_0.term_271 (q:Int) (e:Int) + Identity_left1_0.term_272 (q:Int) (e:Int) + Identity_left1_0.term_273 (q:Int) (e:Int) + Identity_left1_0.term_274 (q:Int) (e:Int) + Identity_left1_0.term_275 (q:Int) (e:Int) := by
  classical
  have hs := payload91_count q (e:Int)
  have ht := tally_congr (piecePoints q 91) (rawPieceEvent q 91 e)
    (payload (q:Int) (e:Int) 91) (p91_event q e hq he)
  rw [ht]
  simpa only [Int.one_mul] using hs
#print axioms actual91_count
end
end LuRazClosure.SourcePieces
