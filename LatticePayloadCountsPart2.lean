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
theorem payload46_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 46) (payload (q:Int) e 46)=Identity_left1_0.term_142 (q:Int) e + Identity_left1_0.term_143 (q:Int) e + Identity_left1_0.term_144 (q:Int) e := by
  have h142 := atom142_count (q:Int) e
  have h143 := atom143_count (q:Int) e
  have h144 := atom144_count (q:Int) e
  have ht : tally (piecePoints q 46) (payload (q:Int) e 46)=tally (piecePoints q 46) (event142 (q:Int) e) + tally (piecePoints q 46) (event143 (q:Int) e) - tally (piecePoints q 46) (event144 (q:Int) e) := by
    exact (tally_or (piecePoints q 46) (event142 (q:Int) e) (event143 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 46) (event142 (q:Int) e) + tally (piecePoints q 46) (event143 (q:Int) e) - tally (piecePoints q 46) (event144 (q:Int) e))=Identity_left1_0.term_142 (q:Int) e + Identity_left1_0.term_143 (q:Int) e + Identity_left1_0.term_144 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 46) (event142 (q:Int) e)=Identity_left1_0.term_142 (q:Int) e at h142
  change (1:Int)*2*tally (piecePoints q 46) (event143 (q:Int) e)=Identity_left1_0.term_143 (q:Int) e at h143
  change (-1:Int)*2*tally (piecePoints q 46) (event144 (q:Int) e)=Identity_left1_0.term_144 (q:Int) e at h144
  omega
#print axioms payload46_count
theorem payload47_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 47) (payload (q:Int) e 47)=Identity_left1_0.term_145 (q:Int) e := by
  have h145 := atom145_count (q:Int) e
  exact h145
#print axioms payload47_count
theorem payload48_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 48) (payload (q:Int) e 48)=Identity_left1_0.term_146 (q:Int) e := by
  have h146 := atom146_count (q:Int) e
  exact h146
#print axioms payload48_count
theorem payload49_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 49) (payload (q:Int) e 49)=Identity_left1_0.term_147 (q:Int) e := by
  have h147 := atom147_count (q:Int) e
  exact h147
#print axioms payload49_count
theorem payload50_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 50) (payload (q:Int) e 50)=Identity_left1_0.term_148 (q:Int) e := by
  have h148 := atom148_count (q:Int) e
  exact h148
#print axioms payload50_count
theorem payload51_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 51) (payload (q:Int) e 51)=Identity_left1_0.term_149 (q:Int) e := by
  have h149 := atom149_count (q:Int) e
  exact h149
#print axioms payload51_count
theorem payload52_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 52) (payload (q:Int) e 52)=Identity_left1_0.term_150 (q:Int) e := by
  have h150 := atom150_count (q:Int) e
  exact h150
#print axioms payload52_count
theorem payload53_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 53) (payload (q:Int) e 53)=Identity_left1_0.term_151 (q:Int) e := by
  have h151 := atom151_count (q:Int) e
  exact h151
#print axioms payload53_count
theorem payload54_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 54) (payload (q:Int) e 54)=Identity_left1_0.term_152 (q:Int) e + Identity_left1_0.term_153 (q:Int) e + Identity_left1_0.term_154 (q:Int) e := by
  have h152 := atom152_count (q:Int) e
  have h153 := atom153_count (q:Int) e
  have h154 := atom154_count (q:Int) e
  have ht : tally (piecePoints q 54) (payload (q:Int) e 54)=tally (piecePoints q 54) (event152 (q:Int) e) + tally (piecePoints q 54) (event153 (q:Int) e) - tally (piecePoints q 54) (event154 (q:Int) e) := by
    exact (tally_or (piecePoints q 54) (event152 (q:Int) e) (event153 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 54) (event152 (q:Int) e) + tally (piecePoints q 54) (event153 (q:Int) e) - tally (piecePoints q 54) (event154 (q:Int) e))=Identity_left1_0.term_152 (q:Int) e + Identity_left1_0.term_153 (q:Int) e + Identity_left1_0.term_154 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 54) (event152 (q:Int) e)=Identity_left1_0.term_152 (q:Int) e at h152
  change (1:Int)*2*tally (piecePoints q 54) (event153 (q:Int) e)=Identity_left1_0.term_153 (q:Int) e at h153
  change (-1:Int)*2*tally (piecePoints q 54) (event154 (q:Int) e)=Identity_left1_0.term_154 (q:Int) e at h154
  omega
#print axioms payload54_count
theorem payload55_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 55) (payload (q:Int) e 55)=Identity_left1_0.term_155 (q:Int) e + Identity_left1_0.term_156 (q:Int) e + Identity_left1_0.term_157 (q:Int) e := by
  have h155 := atom155_count (q:Int) e
  have h156 := atom156_count (q:Int) e
  have h157 := atom157_count (q:Int) e
  have ht : tally (piecePoints q 55) (payload (q:Int) e 55)=tally (piecePoints q 55) (event155 (q:Int) e) + tally (piecePoints q 55) (event156 (q:Int) e) - tally (piecePoints q 55) (event157 (q:Int) e) := by
    exact (tally_or (piecePoints q 55) (event155 (q:Int) e) (event156 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 55) (event155 (q:Int) e) + tally (piecePoints q 55) (event156 (q:Int) e) - tally (piecePoints q 55) (event157 (q:Int) e))=Identity_left1_0.term_155 (q:Int) e + Identity_left1_0.term_156 (q:Int) e + Identity_left1_0.term_157 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 55) (event155 (q:Int) e)=Identity_left1_0.term_155 (q:Int) e at h155
  change (1:Int)*2*tally (piecePoints q 55) (event156 (q:Int) e)=Identity_left1_0.term_156 (q:Int) e at h156
  change (-1:Int)*2*tally (piecePoints q 55) (event157 (q:Int) e)=Identity_left1_0.term_157 (q:Int) e at h157
  omega
#print axioms payload55_count
theorem payload56_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 56) (payload (q:Int) e 56)=Identity_left1_0.term_158 (q:Int) e + Identity_left1_0.term_159 (q:Int) e + Identity_left1_0.term_160 (q:Int) e := by
  have h158 := atom158_count (q:Int) e
  have h159 := atom159_count (q:Int) e
  have h160 := atom160_count (q:Int) e
  have ht : tally (piecePoints q 56) (payload (q:Int) e 56)=tally (piecePoints q 56) (event158 (q:Int) e) + tally (piecePoints q 56) (event159 (q:Int) e) - tally (piecePoints q 56) (event160 (q:Int) e) := by
    exact (tally_or (piecePoints q 56) (event158 (q:Int) e) (event159 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 56) (event158 (q:Int) e) + tally (piecePoints q 56) (event159 (q:Int) e) - tally (piecePoints q 56) (event160 (q:Int) e))=Identity_left1_0.term_158 (q:Int) e + Identity_left1_0.term_159 (q:Int) e + Identity_left1_0.term_160 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 56) (event158 (q:Int) e)=Identity_left1_0.term_158 (q:Int) e at h158
  change (1:Int)*2*tally (piecePoints q 56) (event159 (q:Int) e)=Identity_left1_0.term_159 (q:Int) e at h159
  change (-1:Int)*2*tally (piecePoints q 56) (event160 (q:Int) e)=Identity_left1_0.term_160 (q:Int) e at h160
  omega
#print axioms payload56_count
theorem payload57_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 57) (payload (q:Int) e 57)=Identity_left1_0.term_161 (q:Int) e + Identity_left1_0.term_162 (q:Int) e + Identity_left1_0.term_163 (q:Int) e := by
  have h161 := atom161_count (q:Int) e
  have h162 := atom162_count (q:Int) e
  have h163 := atom163_count (q:Int) e
  have ht : tally (piecePoints q 57) (payload (q:Int) e 57)=tally (piecePoints q 57) (event161 (q:Int) e) + tally (piecePoints q 57) (event162 (q:Int) e) - tally (piecePoints q 57) (event163 (q:Int) e) := by
    exact (tally_or (piecePoints q 57) (event161 (q:Int) e) (event162 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 57) (event161 (q:Int) e) + tally (piecePoints q 57) (event162 (q:Int) e) - tally (piecePoints q 57) (event163 (q:Int) e))=Identity_left1_0.term_161 (q:Int) e + Identity_left1_0.term_162 (q:Int) e + Identity_left1_0.term_163 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 57) (event161 (q:Int) e)=Identity_left1_0.term_161 (q:Int) e at h161
  change (1:Int)*2*tally (piecePoints q 57) (event162 (q:Int) e)=Identity_left1_0.term_162 (q:Int) e at h162
  change (-1:Int)*2*tally (piecePoints q 57) (event163 (q:Int) e)=Identity_left1_0.term_163 (q:Int) e at h163
  omega
#print axioms payload57_count
theorem payload58_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 58) (payload (q:Int) e 58)=Identity_left1_0.term_164 (q:Int) e + Identity_left1_0.term_165 (q:Int) e + Identity_left1_0.term_166 (q:Int) e := by
  have h164 := atom164_count (q:Int) e
  have h165 := atom165_count (q:Int) e
  have h166 := atom166_count (q:Int) e
  have ht : tally (piecePoints q 58) (payload (q:Int) e 58)=tally (piecePoints q 58) (event164 (q:Int) e) + tally (piecePoints q 58) (event165 (q:Int) e) - tally (piecePoints q 58) (event166 (q:Int) e) := by
    exact (tally_or (piecePoints q 58) (event164 (q:Int) e) (event165 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 58) (event164 (q:Int) e) + tally (piecePoints q 58) (event165 (q:Int) e) - tally (piecePoints q 58) (event166 (q:Int) e))=Identity_left1_0.term_164 (q:Int) e + Identity_left1_0.term_165 (q:Int) e + Identity_left1_0.term_166 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 58) (event164 (q:Int) e)=Identity_left1_0.term_164 (q:Int) e at h164
  change (1:Int)*2*tally (piecePoints q 58) (event165 (q:Int) e)=Identity_left1_0.term_165 (q:Int) e at h165
  change (-1:Int)*2*tally (piecePoints q 58) (event166 (q:Int) e)=Identity_left1_0.term_166 (q:Int) e at h166
  omega
#print axioms payload58_count
theorem payload59_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 59) (payload (q:Int) e 59)=Identity_left1_0.term_167 (q:Int) e + Identity_left1_0.term_168 (q:Int) e + Identity_left1_0.term_169 (q:Int) e := by
  have h167 := atom167_count (q:Int) e
  have h168 := atom168_count (q:Int) e
  have h169 := atom169_count (q:Int) e
  have ht : tally (piecePoints q 59) (payload (q:Int) e 59)=tally (piecePoints q 59) (event167 (q:Int) e) + tally (piecePoints q 59) (event168 (q:Int) e) - tally (piecePoints q 59) (event169 (q:Int) e) := by
    exact (tally_or (piecePoints q 59) (event167 (q:Int) e) (event168 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 59) (event167 (q:Int) e) + tally (piecePoints q 59) (event168 (q:Int) e) - tally (piecePoints q 59) (event169 (q:Int) e))=Identity_left1_0.term_167 (q:Int) e + Identity_left1_0.term_168 (q:Int) e + Identity_left1_0.term_169 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 59) (event167 (q:Int) e)=Identity_left1_0.term_167 (q:Int) e at h167
  change (1:Int)*2*tally (piecePoints q 59) (event168 (q:Int) e)=Identity_left1_0.term_168 (q:Int) e at h168
  change (-1:Int)*2*tally (piecePoints q 59) (event169 (q:Int) e)=Identity_left1_0.term_169 (q:Int) e at h169
  omega
#print axioms payload59_count
theorem payload60_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 60) (payload (q:Int) e 60)=Identity_left1_0.term_170 (q:Int) e := by
  have h170 := atom170_count (q:Int) e
  exact h170
#print axioms payload60_count
theorem payload61_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 61) (payload (q:Int) e 61)=Identity_left1_0.term_171 (q:Int) e + Identity_left1_0.term_172 (q:Int) e + Identity_left1_0.term_173 (q:Int) e := by
  have h171 := atom171_count (q:Int) e
  have h172 := atom172_count (q:Int) e
  have h173 := atom173_count (q:Int) e
  have ht : tally (piecePoints q 61) (payload (q:Int) e 61)=tally (piecePoints q 61) (event171 (q:Int) e) + tally (piecePoints q 61) (event172 (q:Int) e) - tally (piecePoints q 61) (event173 (q:Int) e) := by
    exact (tally_or (piecePoints q 61) (event171 (q:Int) e) (event172 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 61) (event171 (q:Int) e) + tally (piecePoints q 61) (event172 (q:Int) e) - tally (piecePoints q 61) (event173 (q:Int) e))=Identity_left1_0.term_171 (q:Int) e + Identity_left1_0.term_172 (q:Int) e + Identity_left1_0.term_173 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 61) (event171 (q:Int) e)=Identity_left1_0.term_171 (q:Int) e at h171
  change (1:Int)*2*tally (piecePoints q 61) (event172 (q:Int) e)=Identity_left1_0.term_172 (q:Int) e at h172
  change (-1:Int)*2*tally (piecePoints q 61) (event173 (q:Int) e)=Identity_left1_0.term_173 (q:Int) e at h173
  omega
#print axioms payload61_count
theorem payload62_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 62) (payload (q:Int) e 62)=Identity_left1_0.term_174 (q:Int) e + Identity_left1_0.term_175 (q:Int) e + Identity_left1_0.term_176 (q:Int) e := by
  have h174 := atom174_count (q:Int) e
  have h175 := atom175_count (q:Int) e
  have h176 := atom176_count (q:Int) e
  have ht : tally (piecePoints q 62) (payload (q:Int) e 62)=tally (piecePoints q 62) (event174 (q:Int) e) + tally (piecePoints q 62) (event175 (q:Int) e) - tally (piecePoints q 62) (event176 (q:Int) e) := by
    exact (tally_or (piecePoints q 62) (event174 (q:Int) e) (event175 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 62) (event174 (q:Int) e) + tally (piecePoints q 62) (event175 (q:Int) e) - tally (piecePoints q 62) (event176 (q:Int) e))=Identity_left1_0.term_174 (q:Int) e + Identity_left1_0.term_175 (q:Int) e + Identity_left1_0.term_176 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 62) (event174 (q:Int) e)=Identity_left1_0.term_174 (q:Int) e at h174
  change (1:Int)*2*tally (piecePoints q 62) (event175 (q:Int) e)=Identity_left1_0.term_175 (q:Int) e at h175
  change (-1:Int)*2*tally (piecePoints q 62) (event176 (q:Int) e)=Identity_left1_0.term_176 (q:Int) e at h176
  omega
#print axioms payload62_count
theorem payload63_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 63) (payload (q:Int) e 63)=Identity_left1_0.term_177 (q:Int) e + Identity_left1_0.term_178 (q:Int) e + Identity_left1_0.term_179 (q:Int) e := by
  have h177 := atom177_count (q:Int) e
  have h178 := atom178_count (q:Int) e
  have h179 := atom179_count (q:Int) e
  have ht : tally (piecePoints q 63) (payload (q:Int) e 63)=tally (piecePoints q 63) (event177 (q:Int) e) + tally (piecePoints q 63) (event178 (q:Int) e) - tally (piecePoints q 63) (event179 (q:Int) e) := by
    exact (tally_or (piecePoints q 63) (event177 (q:Int) e) (event178 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 63) (event177 (q:Int) e) + tally (piecePoints q 63) (event178 (q:Int) e) - tally (piecePoints q 63) (event179 (q:Int) e))=Identity_left1_0.term_177 (q:Int) e + Identity_left1_0.term_178 (q:Int) e + Identity_left1_0.term_179 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 63) (event177 (q:Int) e)=Identity_left1_0.term_177 (q:Int) e at h177
  change (1:Int)*2*tally (piecePoints q 63) (event178 (q:Int) e)=Identity_left1_0.term_178 (q:Int) e at h178
  change (-1:Int)*2*tally (piecePoints q 63) (event179 (q:Int) e)=Identity_left1_0.term_179 (q:Int) e at h179
  omega
#print axioms payload63_count
theorem payload64_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 64) (payload (q:Int) e 64)=Identity_left1_0.term_180 (q:Int) e + Identity_left1_0.term_181 (q:Int) e + Identity_left1_0.term_182 (q:Int) e := by
  have h180 := atom180_count (q:Int) e
  have h181 := atom181_count (q:Int) e
  have h182 := atom182_count (q:Int) e
  have ht : tally (piecePoints q 64) (payload (q:Int) e 64)=tally (piecePoints q 64) (event180 (q:Int) e) + tally (piecePoints q 64) (event181 (q:Int) e) - tally (piecePoints q 64) (event182 (q:Int) e) := by
    exact (tally_or (piecePoints q 64) (event180 (q:Int) e) (event181 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 64) (event180 (q:Int) e) + tally (piecePoints q 64) (event181 (q:Int) e) - tally (piecePoints q 64) (event182 (q:Int) e))=Identity_left1_0.term_180 (q:Int) e + Identity_left1_0.term_181 (q:Int) e + Identity_left1_0.term_182 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 64) (event180 (q:Int) e)=Identity_left1_0.term_180 (q:Int) e at h180
  change (1:Int)*2*tally (piecePoints q 64) (event181 (q:Int) e)=Identity_left1_0.term_181 (q:Int) e at h181
  change (-1:Int)*2*tally (piecePoints q 64) (event182 (q:Int) e)=Identity_left1_0.term_182 (q:Int) e at h182
  omega
#print axioms payload64_count
theorem payload65_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 65) (payload (q:Int) e 65)=Identity_left1_0.term_183 (q:Int) e + Identity_left1_0.term_184 (q:Int) e + Identity_left1_0.term_185 (q:Int) e + Identity_left1_0.term_186 (q:Int) e + Identity_left1_0.term_187 (q:Int) e + Identity_left1_0.term_188 (q:Int) e + Identity_left1_0.term_189 (q:Int) e := by
  have h183 := atom183_count (q:Int) e
  have h184 := atom184_count (q:Int) e
  have h185 := atom185_count (q:Int) e
  have h186 := atom186_count (q:Int) e
  have h187 := atom187_count (q:Int) e
  have h188 := atom188_count (q:Int) e
  have h189 := atom189_count (q:Int) e
  have ht : tally (piecePoints q 65) (payload (q:Int) e 65)=tally (piecePoints q 65) (event183 (q:Int) e) + tally (piecePoints q 65) (event184 (q:Int) e) + tally (piecePoints q 65) (event185 (q:Int) e) - tally (piecePoints q 65) (event186 (q:Int) e) - tally (piecePoints q 65) (event187 (q:Int) e) - tally (piecePoints q 65) (event188 (q:Int) e) + tally (piecePoints q 65) (event189 (q:Int) e) := by
    exact (tally_or3 (piecePoints q 65) (event183 (q:Int) e) (event184 (q:Int) e) (event185 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 65) (event183 (q:Int) e) + tally (piecePoints q 65) (event184 (q:Int) e) + tally (piecePoints q 65) (event185 (q:Int) e) - tally (piecePoints q 65) (event186 (q:Int) e) - tally (piecePoints q 65) (event187 (q:Int) e) - tally (piecePoints q 65) (event188 (q:Int) e) + tally (piecePoints q 65) (event189 (q:Int) e))=Identity_left1_0.term_183 (q:Int) e + Identity_left1_0.term_184 (q:Int) e + Identity_left1_0.term_185 (q:Int) e + Identity_left1_0.term_186 (q:Int) e + Identity_left1_0.term_187 (q:Int) e + Identity_left1_0.term_188 (q:Int) e + Identity_left1_0.term_189 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 65) (event183 (q:Int) e)=Identity_left1_0.term_183 (q:Int) e at h183
  change (1:Int)*2*tally (piecePoints q 65) (event184 (q:Int) e)=Identity_left1_0.term_184 (q:Int) e at h184
  change (1:Int)*2*tally (piecePoints q 65) (event185 (q:Int) e)=Identity_left1_0.term_185 (q:Int) e at h185
  change (-1:Int)*2*tally (piecePoints q 65) (event186 (q:Int) e)=Identity_left1_0.term_186 (q:Int) e at h186
  change (-1:Int)*2*tally (piecePoints q 65) (event187 (q:Int) e)=Identity_left1_0.term_187 (q:Int) e at h187
  change (-1:Int)*2*tally (piecePoints q 65) (event188 (q:Int) e)=Identity_left1_0.term_188 (q:Int) e at h188
  change (1:Int)*2*tally (piecePoints q 65) (event189 (q:Int) e)=Identity_left1_0.term_189 (q:Int) e at h189
  omega
#print axioms payload65_count
theorem payload66_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 66) (payload (q:Int) e 66)=Identity_left1_0.term_190 (q:Int) e + Identity_left1_0.term_191 (q:Int) e + Identity_left1_0.term_192 (q:Int) e := by
  have h190 := atom190_count (q:Int) e
  have h191 := atom191_count (q:Int) e
  have h192 := atom192_count (q:Int) e
  have ht : tally (piecePoints q 66) (payload (q:Int) e 66)=tally (piecePoints q 66) (event190 (q:Int) e) + tally (piecePoints q 66) (event191 (q:Int) e) - tally (piecePoints q 66) (event192 (q:Int) e) := by
    exact (tally_or (piecePoints q 66) (event190 (q:Int) e) (event191 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 66) (event190 (q:Int) e) + tally (piecePoints q 66) (event191 (q:Int) e) - tally (piecePoints q 66) (event192 (q:Int) e))=Identity_left1_0.term_190 (q:Int) e + Identity_left1_0.term_191 (q:Int) e + Identity_left1_0.term_192 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 66) (event190 (q:Int) e)=Identity_left1_0.term_190 (q:Int) e at h190
  change (1:Int)*2*tally (piecePoints q 66) (event191 (q:Int) e)=Identity_left1_0.term_191 (q:Int) e at h191
  change (-1:Int)*2*tally (piecePoints q 66) (event192 (q:Int) e)=Identity_left1_0.term_192 (q:Int) e at h192
  omega
#print axioms payload66_count
theorem payload67_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 67) (payload (q:Int) e 67)=Identity_left1_0.term_193 (q:Int) e + Identity_left1_0.term_194 (q:Int) e + Identity_left1_0.term_195 (q:Int) e := by
  have h193 := atom193_count (q:Int) e
  have h194 := atom194_count (q:Int) e
  have h195 := atom195_count (q:Int) e
  have ht : tally (piecePoints q 67) (payload (q:Int) e 67)=tally (piecePoints q 67) (event193 (q:Int) e) + tally (piecePoints q 67) (event194 (q:Int) e) - tally (piecePoints q 67) (event195 (q:Int) e) := by
    exact (tally_or (piecePoints q 67) (event193 (q:Int) e) (event194 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 67) (event193 (q:Int) e) + tally (piecePoints q 67) (event194 (q:Int) e) - tally (piecePoints q 67) (event195 (q:Int) e))=Identity_left1_0.term_193 (q:Int) e + Identity_left1_0.term_194 (q:Int) e + Identity_left1_0.term_195 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 67) (event193 (q:Int) e)=Identity_left1_0.term_193 (q:Int) e at h193
  change (1:Int)*2*tally (piecePoints q 67) (event194 (q:Int) e)=Identity_left1_0.term_194 (q:Int) e at h194
  change (-1:Int)*2*tally (piecePoints q 67) (event195 (q:Int) e)=Identity_left1_0.term_195 (q:Int) e at h195
  omega
#print axioms payload67_count
theorem payload68_count (q : Nat) (e : Int) :
    (1:Int)*2*tally (piecePoints q 68) (payload (q:Int) e 68)=Identity_left1_0.term_196 (q:Int) e + Identity_left1_0.term_197 (q:Int) e + Identity_left1_0.term_198 (q:Int) e := by
  have h196 := atom196_count (q:Int) e
  have h197 := atom197_count (q:Int) e
  have h198 := atom198_count (q:Int) e
  have ht : tally (piecePoints q 68) (payload (q:Int) e 68)=tally (piecePoints q 68) (event196 (q:Int) e) + tally (piecePoints q 68) (event197 (q:Int) e) - tally (piecePoints q 68) (event198 (q:Int) e) := by
    exact (tally_or (piecePoints q 68) (event196 (q:Int) e) (event197 (q:Int) e))
  rw [ht]
  change (1:Int)*2*(tally (piecePoints q 68) (event196 (q:Int) e) + tally (piecePoints q 68) (event197 (q:Int) e) - tally (piecePoints q 68) (event198 (q:Int) e))=Identity_left1_0.term_196 (q:Int) e + Identity_left1_0.term_197 (q:Int) e + Identity_left1_0.term_198 (q:Int) e
  change (1:Int)*2*tally (piecePoints q 68) (event196 (q:Int) e)=Identity_left1_0.term_196 (q:Int) e at h196
  change (1:Int)*2*tally (piecePoints q 68) (event197 (q:Int) e)=Identity_left1_0.term_197 (q:Int) e at h197
  change (-1:Int)*2*tally (piecePoints q 68) (event198 (q:Int) e)=Identity_left1_0.term_198 (q:Int) e at h198
  omega
#print axioms payload68_count
end
end LuRazClosure.SourcePieces
