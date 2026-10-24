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
theorem payload69_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 69) (payload (q:Int) e 69)=Identity_left1_0.term_199 (q:Int) e + Identity_left1_0.term_200 (q:Int) e + Identity_left1_0.term_201 (q:Int) e + Identity_left1_0.term_202 (q:Int) e + Identity_left1_0.term_203 (q:Int) e + Identity_left1_0.term_204 (q:Int) e + Identity_left1_0.term_205 (q:Int) e := by
  have h199 := atom199_count (q:Int) e
  have h200 := atom200_count (q:Int) e
  have h201 := atom201_count (q:Int) e
  have h202 := atom202_count (q:Int) e
  have h203 := atom203_count (q:Int) e
  have h204 := atom204_count (q:Int) e
  have h205 := atom205_count (q:Int) e
  have ht : tally (piecePoints q 69) (payload (q:Int) e 69)=tally (piecePoints q 69) (event199 (q:Int) e) + tally (piecePoints q 69) (event200 (q:Int) e) + tally (piecePoints q 69) (event201 (q:Int) e) - tally (piecePoints q 69) (event202 (q:Int) e) - tally (piecePoints q 69) (event203 (q:Int) e) - tally (piecePoints q 69) (event204 (q:Int) e) + tally (piecePoints q 69) (event205 (q:Int) e) := by
    exact (tally_or3 (piecePoints q 69) (event199 (q:Int) e) (event200 (q:Int) e) (event201 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 69) (event199 (q:Int) e) + tally (piecePoints q 69) (event200 (q:Int) e) + tally (piecePoints q 69) (event201 (q:Int) e) - tally (piecePoints q 69) (event202 (q:Int) e) - tally (piecePoints q 69) (event203 (q:Int) e) - tally (piecePoints q 69) (event204 (q:Int) e) + tally (piecePoints q 69) (event205 (q:Int) e))=Identity_left1_0.term_199 (q:Int) e + Identity_left1_0.term_200 (q:Int) e + Identity_left1_0.term_201 (q:Int) e + Identity_left1_0.term_202 (q:Int) e + Identity_left1_0.term_203 (q:Int) e + Identity_left1_0.term_204 (q:Int) e + Identity_left1_0.term_205 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 69) (event199 (q:Int) e)=Identity_left1_0.term_199 (q:Int) e at h199
  change (1:Int)*2*tally (piecePoints q 69) (event200 (q:Int) e)=Identity_left1_0.term_200 (q:Int) e at h200
  change (1:Int)*2*tally (piecePoints q 69) (event201 (q:Int) e)=Identity_left1_0.term_201 (q:Int) e at h201
  change (-1:Int)*2*tally (piecePoints q 69) (event202 (q:Int) e)=Identity_left1_0.term_202 (q:Int) e at h202
  change (-1:Int)*2*tally (piecePoints q 69) (event203 (q:Int) e)=Identity_left1_0.term_203 (q:Int) e at h203
  change (-1:Int)*2*tally (piecePoints q 69) (event204 (q:Int) e)=Identity_left1_0.term_204 (q:Int) e at h204
  change (1:Int)*2*tally (piecePoints q 69) (event205 (q:Int) e)=Identity_left1_0.term_205 (q:Int) e at h205
  omega
#print axioms payload69_count
theorem payload70_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 70) (payload (q:Int) e 70)=Identity_left1_0.term_206 (q:Int) e + Identity_left1_0.term_207 (q:Int) e + Identity_left1_0.term_208 (q:Int) e + Identity_left1_0.term_209 (q:Int) e + Identity_left1_0.term_210 (q:Int) e + Identity_left1_0.term_211 (q:Int) e + Identity_left1_0.term_212 (q:Int) e := by
  have h206 := atom206_count (q:Int) e
  have h207 := atom207_count (q:Int) e
  have h208 := atom208_count (q:Int) e
  have h209 := atom209_count (q:Int) e
  have h210 := atom210_count (q:Int) e
  have h211 := atom211_count (q:Int) e
  have h212 := atom212_count (q:Int) e
  have ht : tally (piecePoints q 70) (payload (q:Int) e 70)=tally (piecePoints q 70) (event206 (q:Int) e) + tally (piecePoints q 70) (event207 (q:Int) e) + tally (piecePoints q 70) (event208 (q:Int) e) - tally (piecePoints q 70) (event209 (q:Int) e) - tally (piecePoints q 70) (event210 (q:Int) e) - tally (piecePoints q 70) (event211 (q:Int) e) + tally (piecePoints q 70) (event212 (q:Int) e) := by
    exact (tally_or3 (piecePoints q 70) (event206 (q:Int) e) (event207 (q:Int) e) (event208 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 70) (event206 (q:Int) e) + tally (piecePoints q 70) (event207 (q:Int) e) + tally (piecePoints q 70) (event208 (q:Int) e) - tally (piecePoints q 70) (event209 (q:Int) e) - tally (piecePoints q 70) (event210 (q:Int) e) - tally (piecePoints q 70) (event211 (q:Int) e) + tally (piecePoints q 70) (event212 (q:Int) e))=Identity_left1_0.term_206 (q:Int) e + Identity_left1_0.term_207 (q:Int) e + Identity_left1_0.term_208 (q:Int) e + Identity_left1_0.term_209 (q:Int) e + Identity_left1_0.term_210 (q:Int) e + Identity_left1_0.term_211 (q:Int) e + Identity_left1_0.term_212 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 70) (event206 (q:Int) e)=Identity_left1_0.term_206 (q:Int) e at h206
  change (1:Int)*2*tally (piecePoints q 70) (event207 (q:Int) e)=Identity_left1_0.term_207 (q:Int) e at h207
  change (1:Int)*2*tally (piecePoints q 70) (event208 (q:Int) e)=Identity_left1_0.term_208 (q:Int) e at h208
  change (-1:Int)*2*tally (piecePoints q 70) (event209 (q:Int) e)=Identity_left1_0.term_209 (q:Int) e at h209
  change (-1:Int)*2*tally (piecePoints q 70) (event210 (q:Int) e)=Identity_left1_0.term_210 (q:Int) e at h210
  change (-1:Int)*2*tally (piecePoints q 70) (event211 (q:Int) e)=Identity_left1_0.term_211 (q:Int) e at h211
  change (1:Int)*2*tally (piecePoints q 70) (event212 (q:Int) e)=Identity_left1_0.term_212 (q:Int) e at h212
  omega
#print axioms payload70_count
theorem payload71_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 71) (payload (q:Int) e 71)=Identity_left1_0.term_213 (q:Int) e + Identity_left1_0.term_214 (q:Int) e + Identity_left1_0.term_215 (q:Int) e := by
  have h213 := atom213_count (q:Int) e
  have h214 := atom214_count (q:Int) e
  have h215 := atom215_count (q:Int) e
  have ht : tally (piecePoints q 71) (payload (q:Int) e 71)=tally (piecePoints q 71) (event213 (q:Int) e) + tally (piecePoints q 71) (event214 (q:Int) e) - tally (piecePoints q 71) (event215 (q:Int) e) := by
    exact (tally_or (piecePoints q 71) (event213 (q:Int) e) (event214 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 71) (event213 (q:Int) e) + tally (piecePoints q 71) (event214 (q:Int) e) - tally (piecePoints q 71) (event215 (q:Int) e))=Identity_left1_0.term_213 (q:Int) e + Identity_left1_0.term_214 (q:Int) e + Identity_left1_0.term_215 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 71) (event213 (q:Int) e)=Identity_left1_0.term_213 (q:Int) e at h213
  change (1:Int)*2*tally (piecePoints q 71) (event214 (q:Int) e)=Identity_left1_0.term_214 (q:Int) e at h214
  change (-1:Int)*2*tally (piecePoints q 71) (event215 (q:Int) e)=Identity_left1_0.term_215 (q:Int) e at h215
  omega
#print axioms payload71_count
theorem payload72_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 72) (payload (q:Int) e 72)=Identity_left1_0.term_216 (q:Int) e + Identity_left1_0.term_217 (q:Int) e + Identity_left1_0.term_218 (q:Int) e := by
  have h216 := atom216_count (q:Int) e
  have h217 := atom217_count (q:Int) e
  have h218 := atom218_count (q:Int) e
  have ht : tally (piecePoints q 72) (payload (q:Int) e 72)=tally (piecePoints q 72) (event216 (q:Int) e) + tally (piecePoints q 72) (event217 (q:Int) e) - tally (piecePoints q 72) (event218 (q:Int) e) := by
    exact (tally_or (piecePoints q 72) (event216 (q:Int) e) (event217 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 72) (event216 (q:Int) e) + tally (piecePoints q 72) (event217 (q:Int) e) - tally (piecePoints q 72) (event218 (q:Int) e))=Identity_left1_0.term_216 (q:Int) e + Identity_left1_0.term_217 (q:Int) e + Identity_left1_0.term_218 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 72) (event216 (q:Int) e)=Identity_left1_0.term_216 (q:Int) e at h216
  change (1:Int)*2*tally (piecePoints q 72) (event217 (q:Int) e)=Identity_left1_0.term_217 (q:Int) e at h217
  change (-1:Int)*2*tally (piecePoints q 72) (event218 (q:Int) e)=Identity_left1_0.term_218 (q:Int) e at h218
  omega
#print axioms payload72_count
theorem payload73_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 73) (payload (q:Int) e 73)=Identity_left1_0.term_219 (q:Int) e + Identity_left1_0.term_220 (q:Int) e + Identity_left1_0.term_221 (q:Int) e := by
  have h219 := atom219_count (q:Int) e
  have h220 := atom220_count (q:Int) e
  have h221 := atom221_count (q:Int) e
  have ht : tally (piecePoints q 73) (payload (q:Int) e 73)=tally (piecePoints q 73) (event219 (q:Int) e) + tally (piecePoints q 73) (event220 (q:Int) e) - tally (piecePoints q 73) (event221 (q:Int) e) := by
    exact (tally_or (piecePoints q 73) (event219 (q:Int) e) (event220 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 73) (event219 (q:Int) e) + tally (piecePoints q 73) (event220 (q:Int) e) - tally (piecePoints q 73) (event221 (q:Int) e))=Identity_left1_0.term_219 (q:Int) e + Identity_left1_0.term_220 (q:Int) e + Identity_left1_0.term_221 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 73) (event219 (q:Int) e)=Identity_left1_0.term_219 (q:Int) e at h219
  change (1:Int)*2*tally (piecePoints q 73) (event220 (q:Int) e)=Identity_left1_0.term_220 (q:Int) e at h220
  change (-1:Int)*2*tally (piecePoints q 73) (event221 (q:Int) e)=Identity_left1_0.term_221 (q:Int) e at h221
  omega
#print axioms payload73_count
theorem payload74_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 74) (payload (q:Int) e 74)=Identity_left1_0.term_222 (q:Int) e + Identity_left1_0.term_223 (q:Int) e + Identity_left1_0.term_224 (q:Int) e := by
  have h222 := atom222_count (q:Int) e
  have h223 := atom223_count (q:Int) e
  have h224 := atom224_count (q:Int) e
  have ht : tally (piecePoints q 74) (payload (q:Int) e 74)=tally (piecePoints q 74) (event222 (q:Int) e) + tally (piecePoints q 74) (event223 (q:Int) e) - tally (piecePoints q 74) (event224 (q:Int) e) := by
    exact (tally_or (piecePoints q 74) (event222 (q:Int) e) (event223 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 74) (event222 (q:Int) e) + tally (piecePoints q 74) (event223 (q:Int) e) - tally (piecePoints q 74) (event224 (q:Int) e))=Identity_left1_0.term_222 (q:Int) e + Identity_left1_0.term_223 (q:Int) e + Identity_left1_0.term_224 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 74) (event222 (q:Int) e)=Identity_left1_0.term_222 (q:Int) e at h222
  change (1:Int)*2*tally (piecePoints q 74) (event223 (q:Int) e)=Identity_left1_0.term_223 (q:Int) e at h223
  change (-1:Int)*2*tally (piecePoints q 74) (event224 (q:Int) e)=Identity_left1_0.term_224 (q:Int) e at h224
  omega
#print axioms payload74_count
theorem payload75_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 75) (payload (q:Int) e 75)=Identity_left1_0.term_225 (q:Int) e + Identity_left1_0.term_226 (q:Int) e + Identity_left1_0.term_227 (q:Int) e := by
  have h225 := atom225_count (q:Int) e
  have h226 := atom226_count (q:Int) e
  have h227 := atom227_count (q:Int) e
  have ht : tally (piecePoints q 75) (payload (q:Int) e 75)=tally (piecePoints q 75) (event225 (q:Int) e) + tally (piecePoints q 75) (event226 (q:Int) e) - tally (piecePoints q 75) (event227 (q:Int) e) := by
    exact (tally_or (piecePoints q 75) (event225 (q:Int) e) (event226 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 75) (event225 (q:Int) e) + tally (piecePoints q 75) (event226 (q:Int) e) - tally (piecePoints q 75) (event227 (q:Int) e))=Identity_left1_0.term_225 (q:Int) e + Identity_left1_0.term_226 (q:Int) e + Identity_left1_0.term_227 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 75) (event225 (q:Int) e)=Identity_left1_0.term_225 (q:Int) e at h225
  change (1:Int)*2*tally (piecePoints q 75) (event226 (q:Int) e)=Identity_left1_0.term_226 (q:Int) e at h226
  change (-1:Int)*2*tally (piecePoints q 75) (event227 (q:Int) e)=Identity_left1_0.term_227 (q:Int) e at h227
  omega
#print axioms payload75_count
theorem payload76_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 76) (payload (q:Int) e 76)=Identity_left1_0.term_228 (q:Int) e := by
  have h228 := atom228_count (q:Int) e
  exact h228
#print axioms payload76_count
theorem payload77_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 77) (payload (q:Int) e 77)=Identity_left1_0.term_229 (q:Int) e + Identity_left1_0.term_230 (q:Int) e + Identity_left1_0.term_231 (q:Int) e := by
  have h229 := atom229_count (q:Int) e
  have h230 := atom230_count (q:Int) e
  have h231 := atom231_count (q:Int) e
  have ht : tally (piecePoints q 77) (payload (q:Int) e 77)=tally (piecePoints q 77) (event229 (q:Int) e) + tally (piecePoints q 77) (event230 (q:Int) e) - tally (piecePoints q 77) (event231 (q:Int) e) := by
    exact (tally_or (piecePoints q 77) (event229 (q:Int) e) (event230 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 77) (event229 (q:Int) e) + tally (piecePoints q 77) (event230 (q:Int) e) - tally (piecePoints q 77) (event231 (q:Int) e))=Identity_left1_0.term_229 (q:Int) e + Identity_left1_0.term_230 (q:Int) e + Identity_left1_0.term_231 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 77) (event229 (q:Int) e)=Identity_left1_0.term_229 (q:Int) e at h229
  change (1:Int)*2*tally (piecePoints q 77) (event230 (q:Int) e)=Identity_left1_0.term_230 (q:Int) e at h230
  change (-1:Int)*2*tally (piecePoints q 77) (event231 (q:Int) e)=Identity_left1_0.term_231 (q:Int) e at h231
  omega
#print axioms payload77_count
theorem payload78_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 78) (payload (q:Int) e 78)=Identity_left1_0.term_232 (q:Int) e := by
  have h232 := atom232_count (q:Int) e
  exact h232
#print axioms payload78_count
theorem payload79_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 79) (payload (q:Int) e 79)=Identity_left1_0.term_233 (q:Int) e + Identity_left1_0.term_234 (q:Int) e + Identity_left1_0.term_235 (q:Int) e := by
  have h233 := atom233_count (q:Int) e
  have h234 := atom234_count (q:Int) e
  have h235 := atom235_count (q:Int) e
  have ht : tally (piecePoints q 79) (payload (q:Int) e 79)=tally (piecePoints q 79) (event233 (q:Int) e) + tally (piecePoints q 79) (event234 (q:Int) e) - tally (piecePoints q 79) (event235 (q:Int) e) := by
    exact (tally_or (piecePoints q 79) (event233 (q:Int) e) (event234 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 79) (event233 (q:Int) e) + tally (piecePoints q 79) (event234 (q:Int) e) - tally (piecePoints q 79) (event235 (q:Int) e))=Identity_left1_0.term_233 (q:Int) e + Identity_left1_0.term_234 (q:Int) e + Identity_left1_0.term_235 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 79) (event233 (q:Int) e)=Identity_left1_0.term_233 (q:Int) e at h233
  change (1:Int)*2*tally (piecePoints q 79) (event234 (q:Int) e)=Identity_left1_0.term_234 (q:Int) e at h234
  change (-1:Int)*2*tally (piecePoints q 79) (event235 (q:Int) e)=Identity_left1_0.term_235 (q:Int) e at h235
  omega
#print axioms payload79_count
theorem payload80_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 80) (payload (q:Int) e 80)=Identity_left1_0.term_236 (q:Int) e + Identity_left1_0.term_237 (q:Int) e + Identity_left1_0.term_238 (q:Int) e := by
  have h236 := atom236_count (q:Int) e
  have h237 := atom237_count (q:Int) e
  have h238 := atom238_count (q:Int) e
  have ht : tally (piecePoints q 80) (payload (q:Int) e 80)=tally (piecePoints q 80) (event236 (q:Int) e) + tally (piecePoints q 80) (event237 (q:Int) e) - tally (piecePoints q 80) (event238 (q:Int) e) := by
    exact (tally_or (piecePoints q 80) (event236 (q:Int) e) (event237 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 80) (event236 (q:Int) e) + tally (piecePoints q 80) (event237 (q:Int) e) - tally (piecePoints q 80) (event238 (q:Int) e))=Identity_left1_0.term_236 (q:Int) e + Identity_left1_0.term_237 (q:Int) e + Identity_left1_0.term_238 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 80) (event236 (q:Int) e)=Identity_left1_0.term_236 (q:Int) e at h236
  change (1:Int)*2*tally (piecePoints q 80) (event237 (q:Int) e)=Identity_left1_0.term_237 (q:Int) e at h237
  change (-1:Int)*2*tally (piecePoints q 80) (event238 (q:Int) e)=Identity_left1_0.term_238 (q:Int) e at h238
  omega
#print axioms payload80_count
theorem payload81_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 81) (payload (q:Int) e 81)=Identity_left1_0.term_239 (q:Int) e + Identity_left1_0.term_240 (q:Int) e + Identity_left1_0.term_241 (q:Int) e := by
  have h239 := atom239_count (q:Int) e
  have h240 := atom240_count (q:Int) e
  have h241 := atom241_count (q:Int) e
  have ht : tally (piecePoints q 81) (payload (q:Int) e 81)=tally (piecePoints q 81) (event239 (q:Int) e) + tally (piecePoints q 81) (event240 (q:Int) e) - tally (piecePoints q 81) (event241 (q:Int) e) := by
    exact (tally_or (piecePoints q 81) (event239 (q:Int) e) (event240 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 81) (event239 (q:Int) e) + tally (piecePoints q 81) (event240 (q:Int) e) - tally (piecePoints q 81) (event241 (q:Int) e))=Identity_left1_0.term_239 (q:Int) e + Identity_left1_0.term_240 (q:Int) e + Identity_left1_0.term_241 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 81) (event239 (q:Int) e)=Identity_left1_0.term_239 (q:Int) e at h239
  change (1:Int)*2*tally (piecePoints q 81) (event240 (q:Int) e)=Identity_left1_0.term_240 (q:Int) e at h240
  change (-1:Int)*2*tally (piecePoints q 81) (event241 (q:Int) e)=Identity_left1_0.term_241 (q:Int) e at h241
  omega
#print axioms payload81_count
theorem payload82_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 82) (payload (q:Int) e 82)=Identity_left1_0.term_242 (q:Int) e + Identity_left1_0.term_243 (q:Int) e + Identity_left1_0.term_244 (q:Int) e := by
  have h242 := atom242_count (q:Int) e
  have h243 := atom243_count (q:Int) e
  have h244 := atom244_count (q:Int) e
  have ht : tally (piecePoints q 82) (payload (q:Int) e 82)=tally (piecePoints q 82) (event242 (q:Int) e) + tally (piecePoints q 82) (event243 (q:Int) e) - tally (piecePoints q 82) (event244 (q:Int) e) := by
    exact (tally_or (piecePoints q 82) (event242 (q:Int) e) (event243 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 82) (event242 (q:Int) e) + tally (piecePoints q 82) (event243 (q:Int) e) - tally (piecePoints q 82) (event244 (q:Int) e))=Identity_left1_0.term_242 (q:Int) e + Identity_left1_0.term_243 (q:Int) e + Identity_left1_0.term_244 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 82) (event242 (q:Int) e)=Identity_left1_0.term_242 (q:Int) e at h242
  change (1:Int)*2*tally (piecePoints q 82) (event243 (q:Int) e)=Identity_left1_0.term_243 (q:Int) e at h243
  change (-1:Int)*2*tally (piecePoints q 82) (event244 (q:Int) e)=Identity_left1_0.term_244 (q:Int) e at h244
  omega
#print axioms payload82_count
theorem payload83_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 83) (payload (q:Int) e 83)=Identity_left1_0.term_245 (q:Int) e + Identity_left1_0.term_246 (q:Int) e + Identity_left1_0.term_247 (q:Int) e := by
  have h245 := atom245_count (q:Int) e
  have h246 := atom246_count (q:Int) e
  have h247 := atom247_count (q:Int) e
  have ht : tally (piecePoints q 83) (payload (q:Int) e 83)=tally (piecePoints q 83) (event245 (q:Int) e) + tally (piecePoints q 83) (event246 (q:Int) e) - tally (piecePoints q 83) (event247 (q:Int) e) := by
    exact (tally_or (piecePoints q 83) (event245 (q:Int) e) (event246 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 83) (event245 (q:Int) e) + tally (piecePoints q 83) (event246 (q:Int) e) - tally (piecePoints q 83) (event247 (q:Int) e))=Identity_left1_0.term_245 (q:Int) e + Identity_left1_0.term_246 (q:Int) e + Identity_left1_0.term_247 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 83) (event245 (q:Int) e)=Identity_left1_0.term_245 (q:Int) e at h245
  change (1:Int)*2*tally (piecePoints q 83) (event246 (q:Int) e)=Identity_left1_0.term_246 (q:Int) e at h246
  change (-1:Int)*2*tally (piecePoints q 83) (event247 (q:Int) e)=Identity_left1_0.term_247 (q:Int) e at h247
  omega
#print axioms payload83_count
theorem payload84_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 84) (payload (q:Int) e 84)=Identity_left1_0.term_248 (q:Int) e + Identity_left1_0.term_249 (q:Int) e + Identity_left1_0.term_250 (q:Int) e := by
  have h248 := atom248_count (q:Int) e
  have h249 := atom249_count (q:Int) e
  have h250 := atom250_count (q:Int) e
  have ht : tally (piecePoints q 84) (payload (q:Int) e 84)=tally (piecePoints q 84) (event248 (q:Int) e) + tally (piecePoints q 84) (event249 (q:Int) e) - tally (piecePoints q 84) (event250 (q:Int) e) := by
    exact (tally_or (piecePoints q 84) (event248 (q:Int) e) (event249 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 84) (event248 (q:Int) e) + tally (piecePoints q 84) (event249 (q:Int) e) - tally (piecePoints q 84) (event250 (q:Int) e))=Identity_left1_0.term_248 (q:Int) e + Identity_left1_0.term_249 (q:Int) e + Identity_left1_0.term_250 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 84) (event248 (q:Int) e)=Identity_left1_0.term_248 (q:Int) e at h248
  change (1:Int)*2*tally (piecePoints q 84) (event249 (q:Int) e)=Identity_left1_0.term_249 (q:Int) e at h249
  change (-1:Int)*2*tally (piecePoints q 84) (event250 (q:Int) e)=Identity_left1_0.term_250 (q:Int) e at h250
  omega
#print axioms payload84_count
theorem payload85_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 85) (payload (q:Int) e 85)=Identity_left1_0.term_251 (q:Int) e + Identity_left1_0.term_252 (q:Int) e + Identity_left1_0.term_253 (q:Int) e + Identity_left1_0.term_254 (q:Int) e + Identity_left1_0.term_255 (q:Int) e + Identity_left1_0.term_256 (q:Int) e + Identity_left1_0.term_257 (q:Int) e := by
  have h251 := atom251_count (q:Int) e
  have h252 := atom252_count (q:Int) e
  have h253 := atom253_count (q:Int) e
  have h254 := atom254_count (q:Int) e
  have h255 := atom255_count (q:Int) e
  have h256 := atom256_count (q:Int) e
  have h257 := atom257_count (q:Int) e
  have ht : tally (piecePoints q 85) (payload (q:Int) e 85)=tally (piecePoints q 85) (event251 (q:Int) e) + tally (piecePoints q 85) (event252 (q:Int) e) + tally (piecePoints q 85) (event253 (q:Int) e) - tally (piecePoints q 85) (event254 (q:Int) e) - tally (piecePoints q 85) (event255 (q:Int) e) - tally (piecePoints q 85) (event256 (q:Int) e) + tally (piecePoints q 85) (event257 (q:Int) e) := by
    exact (tally_or3 (piecePoints q 85) (event251 (q:Int) e) (event252 (q:Int) e) (event253 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 85) (event251 (q:Int) e) + tally (piecePoints q 85) (event252 (q:Int) e) + tally (piecePoints q 85) (event253 (q:Int) e) - tally (piecePoints q 85) (event254 (q:Int) e) - tally (piecePoints q 85) (event255 (q:Int) e) - tally (piecePoints q 85) (event256 (q:Int) e) + tally (piecePoints q 85) (event257 (q:Int) e))=Identity_left1_0.term_251 (q:Int) e + Identity_left1_0.term_252 (q:Int) e + Identity_left1_0.term_253 (q:Int) e + Identity_left1_0.term_254 (q:Int) e + Identity_left1_0.term_255 (q:Int) e + Identity_left1_0.term_256 (q:Int) e + Identity_left1_0.term_257 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 85) (event251 (q:Int) e)=Identity_left1_0.term_251 (q:Int) e at h251
  change (1:Int)*2*tally (piecePoints q 85) (event252 (q:Int) e)=Identity_left1_0.term_252 (q:Int) e at h252
  change (1:Int)*2*tally (piecePoints q 85) (event253 (q:Int) e)=Identity_left1_0.term_253 (q:Int) e at h253
  change (-1:Int)*2*tally (piecePoints q 85) (event254 (q:Int) e)=Identity_left1_0.term_254 (q:Int) e at h254
  change (-1:Int)*2*tally (piecePoints q 85) (event255 (q:Int) e)=Identity_left1_0.term_255 (q:Int) e at h255
  change (-1:Int)*2*tally (piecePoints q 85) (event256 (q:Int) e)=Identity_left1_0.term_256 (q:Int) e at h256
  change (1:Int)*2*tally (piecePoints q 85) (event257 (q:Int) e)=Identity_left1_0.term_257 (q:Int) e at h257
  omega
#print axioms payload85_count
theorem payload86_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 86) (payload (q:Int) e 86)=Identity_left1_0.term_258 (q:Int) e + Identity_left1_0.term_259 (q:Int) e + Identity_left1_0.term_260 (q:Int) e := by
  have h258 := atom258_count (q:Int) e
  have h259 := atom259_count (q:Int) e
  have h260 := atom260_count (q:Int) e
  have ht : tally (piecePoints q 86) (payload (q:Int) e 86)=tally (piecePoints q 86) (event258 (q:Int) e) + tally (piecePoints q 86) (event259 (q:Int) e) - tally (piecePoints q 86) (event260 (q:Int) e) := by
    exact (tally_or (piecePoints q 86) (event258 (q:Int) e) (event259 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 86) (event258 (q:Int) e) + tally (piecePoints q 86) (event259 (q:Int) e) - tally (piecePoints q 86) (event260 (q:Int) e))=Identity_left1_0.term_258 (q:Int) e + Identity_left1_0.term_259 (q:Int) e + Identity_left1_0.term_260 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 86) (event258 (q:Int) e)=Identity_left1_0.term_258 (q:Int) e at h258
  change (1:Int)*2*tally (piecePoints q 86) (event259 (q:Int) e)=Identity_left1_0.term_259 (q:Int) e at h259
  change (-1:Int)*2*tally (piecePoints q 86) (event260 (q:Int) e)=Identity_left1_0.term_260 (q:Int) e at h260
  omega
#print axioms payload86_count
theorem payload87_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 87) (payload (q:Int) e 87)=Identity_left1_0.term_261 (q:Int) e := by
  have h261 := atom261_count (q:Int) e
  exact h261
#print axioms payload87_count
theorem payload88_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 88) (payload (q:Int) e 88)=Identity_left1_0.term_262 (q:Int) e + Identity_left1_0.term_263 (q:Int) e + Identity_left1_0.term_264 (q:Int) e := by
  have h262 := atom262_count (q:Int) e
  have h263 := atom263_count (q:Int) e
  have h264 := atom264_count (q:Int) e
  have ht : tally (piecePoints q 88) (payload (q:Int) e 88)=tally (piecePoints q 88) (event262 (q:Int) e) + tally (piecePoints q 88) (event263 (q:Int) e) - tally (piecePoints q 88) (event264 (q:Int) e) := by
    exact (tally_or (piecePoints q 88) (event262 (q:Int) e) (event263 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 88) (event262 (q:Int) e) + tally (piecePoints q 88) (event263 (q:Int) e) - tally (piecePoints q 88) (event264 (q:Int) e))=Identity_left1_0.term_262 (q:Int) e + Identity_left1_0.term_263 (q:Int) e + Identity_left1_0.term_264 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 88) (event262 (q:Int) e)=Identity_left1_0.term_262 (q:Int) e at h262
  change (1:Int)*2*tally (piecePoints q 88) (event263 (q:Int) e)=Identity_left1_0.term_263 (q:Int) e at h263
  change (-1:Int)*2*tally (piecePoints q 88) (event264 (q:Int) e)=Identity_left1_0.term_264 (q:Int) e at h264
  omega
#print axioms payload88_count
theorem payload89_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 89) (payload (q:Int) e 89)=Identity_left1_0.term_265 (q:Int) e := by
  have h265 := atom265_count (q:Int) e
  exact h265
#print axioms payload89_count
theorem payload90_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 90) (payload (q:Int) e 90)=Identity_left1_0.term_266 (q:Int) e + Identity_left1_0.term_267 (q:Int) e + Identity_left1_0.term_268 (q:Int) e := by
  have h266 := atom266_count (q:Int) e
  have h267 := atom267_count (q:Int) e
  have h268 := atom268_count (q:Int) e
  have ht : tally (piecePoints q 90) (payload (q:Int) e 90)=tally (piecePoints q 90) (event266 (q:Int) e) + tally (piecePoints q 90) (event267 (q:Int) e) - tally (piecePoints q 90) (event268 (q:Int) e) := by
    exact (tally_or (piecePoints q 90) (event266 (q:Int) e) (event267 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 90) (event266 (q:Int) e) + tally (piecePoints q 90) (event267 (q:Int) e) - tally (piecePoints q 90) (event268 (q:Int) e))=Identity_left1_0.term_266 (q:Int) e + Identity_left1_0.term_267 (q:Int) e + Identity_left1_0.term_268 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 90) (event266 (q:Int) e)=Identity_left1_0.term_266 (q:Int) e at h266
  change (1:Int)*2*tally (piecePoints q 90) (event267 (q:Int) e)=Identity_left1_0.term_267 (q:Int) e at h267
  change (-1:Int)*2*tally (piecePoints q 90) (event268 (q:Int) e)=Identity_left1_0.term_268 (q:Int) e at h268
  omega
#print axioms payload90_count
theorem payload91_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 91) (payload (q:Int) e 91)=Identity_left1_0.term_269 (q:Int) e + Identity_left1_0.term_270 (q:Int) e + Identity_left1_0.term_271 (q:Int) e + Identity_left1_0.term_272 (q:Int) e + Identity_left1_0.term_273 (q:Int) e + Identity_left1_0.term_274 (q:Int) e + Identity_left1_0.term_275 (q:Int) e := by
  have h269 := atom269_count (q:Int) e
  have h270 := atom270_count (q:Int) e
  have h271 := atom271_count (q:Int) e
  have h272 := atom272_count (q:Int) e
  have h273 := atom273_count (q:Int) e
  have h274 := atom274_count (q:Int) e
  have h275 := atom275_count (q:Int) e
  have ht : tally (piecePoints q 91) (payload (q:Int) e 91)=tally (piecePoints q 91) (event269 (q:Int) e) + tally (piecePoints q 91) (event270 (q:Int) e) + tally (piecePoints q 91) (event271 (q:Int) e) - tally (piecePoints q 91) (event272 (q:Int) e) - tally (piecePoints q 91) (event273 (q:Int) e) - tally (piecePoints q 91) (event274 (q:Int) e) + tally (piecePoints q 91) (event275 (q:Int) e) := by
    exact (tally_or3 (piecePoints q 91) (event269 (q:Int) e) (event270 (q:Int) e) (event271 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 91) (event269 (q:Int) e) + tally (piecePoints q 91) (event270 (q:Int) e) + tally (piecePoints q 91) (event271 (q:Int) e) - tally (piecePoints q 91) (event272 (q:Int) e) - tally (piecePoints q 91) (event273 (q:Int) e) - tally (piecePoints q 91) (event274 (q:Int) e) + tally (piecePoints q 91) (event275 (q:Int) e))=Identity_left1_0.term_269 (q:Int) e + Identity_left1_0.term_270 (q:Int) e + Identity_left1_0.term_271 (q:Int) e + Identity_left1_0.term_272 (q:Int) e + Identity_left1_0.term_273 (q:Int) e + Identity_left1_0.term_274 (q:Int) e + Identity_left1_0.term_275 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 91) (event269 (q:Int) e)=Identity_left1_0.term_269 (q:Int) e at h269
  change (1:Int)*2*tally (piecePoints q 91) (event270 (q:Int) e)=Identity_left1_0.term_270 (q:Int) e at h270
  change (1:Int)*2*tally (piecePoints q 91) (event271 (q:Int) e)=Identity_left1_0.term_271 (q:Int) e at h271
  change (-1:Int)*2*tally (piecePoints q 91) (event272 (q:Int) e)=Identity_left1_0.term_272 (q:Int) e at h272
  change (-1:Int)*2*tally (piecePoints q 91) (event273 (q:Int) e)=Identity_left1_0.term_273 (q:Int) e at h273
  change (-1:Int)*2*tally (piecePoints q 91) (event274 (q:Int) e)=Identity_left1_0.term_274 (q:Int) e at h274
  change (1:Int)*2*tally (piecePoints q 91) (event275 (q:Int) e)=Identity_left1_0.term_275 (q:Int) e at h275
  omega
#print axioms payload91_count
end
end LuRazClosure.SourcePieces
