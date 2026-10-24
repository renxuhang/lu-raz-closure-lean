import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem inverse_valid_NF123 (q : Nat) (hq : 4≤q) (z : NF123) (hz : z.Valid q) :
    let p := invNF123 q z
    Domain q p.1 p.2.1 p.2.2 ∧ decode q p.1 p.2.1 p.2.2=.c123 z := by
  cases z with
  | low t =>
    simp only [invNF123]
    all_goals repeat first | split | (simp_all [Domain,decode,p24Domain,p25Domain,p26Domain,p28Domain,p29Domain,p30Domain,p31Domain,p32Domain,p33Domain,p34Domain,p35Domain,p36Domain,p37Domain,p38Domain,p24NF,p25NF,p26NF,p28NF,p29NF,p30NF,p31NF,p32NF,p33NF,p34NF,p35NF,p36NF,p37NF,p38NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | high t p =>
    simp only [invNF123]
    all_goals repeat first | split | (simp_all [Domain,decode,p24Domain,p25Domain,p26Domain,p28Domain,p29Domain,p30Domain,p31Domain,p32Domain,p33Domain,p34Domain,p35Domain,p36Domain,p37Domain,p38Domain,p24NF,p25NF,p26NF,p28NF,p29NF,p30NF,p31NF,p32NF,p33NF,p34NF,p35NF,p36NF,p37NF,p38NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | filled =>
    simp only [invNF123]
    all_goals repeat first | split | (simp_all [Domain,decode,p24Domain,p25Domain,p26Domain,p28Domain,p29Domain,p30Domain,p31Domain,p32Domain,p33Domain,p34Domain,p35Domain,p36Domain,p37Domain,p38Domain,p24NF,p25NF,p26NF,p28NF,p29NF,p30NF,p31NF,p32NF,p33NF,p34NF,p35NF,p36NF,p37NF,p38NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | dg p =>
    simp only [invNF123]
    all_goals repeat first | split | (simp_all [Domain,decode,p24Domain,p25Domain,p26Domain,p28Domain,p29Domain,p30Domain,p31Domain,p32Domain,p33Domain,p34Domain,p35Domain,p36Domain,p37Domain,p38Domain,p24NF,p25NF,p26NF,p28NF,p29NF,p30NF,p31NF,p32NF,p33NF,p34NF,p35NF,p36NF,p37NF,p38NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | full =>
    simp only [invNF123]
    all_goals repeat first | split | (simp_all [Domain,decode,p24Domain,p25Domain,p26Domain,p28Domain,p29Domain,p30Domain,p31Domain,p32Domain,p33Domain,p34Domain,p35Domain,p36Domain,p37Domain,p38Domain,p24NF,p25NF,p26NF,p28NF,p29NF,p30NF,p31NF,p32NF,p33NF,p34NF,p35NF,p36NF,p37NF,p38NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | creg t =>
    simp only [invNF123]
    all_goals repeat first | split | (simp_all [Domain,decode,p24Domain,p25Domain,p26Domain,p28Domain,p29Domain,p30Domain,p31Domain,p32Domain,p33Domain,p34Domain,p35Domain,p36Domain,p37Domain,p38Domain,p24NF,p25NF,p26NF,p28NF,p29NF,p30NF,p31NF,p32NF,p33NF,p34NF,p35NF,p36NF,p37NF,p38NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | cex =>
    simp only [invNF123]
    all_goals repeat first | split | (simp_all [Domain,decode,p24Domain,p25Domain,p26Domain,p28Domain,p29Domain,p30Domain,p31Domain,p32Domain,p33Domain,p34Domain,p35Domain,p36Domain,p37Domain,p38Domain,p24NF,p25NF,p26NF,p28NF,p29NF,p30NF,p31NF,p32NF,p33NF,p34NF,p35NF,p36NF,p37NF,p38NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | er p =>
    simp only [invNF123]
    all_goals repeat first | split | (simp_all [Domain,decode,p24Domain,p25Domain,p26Domain,p28Domain,p29Domain,p30Domain,p31Domain,p32Domain,p33Domain,p34Domain,p35Domain,p36Domain,p37Domain,p38Domain,p24NF,p25NF,p26NF,p28NF,p29NF,p30NF,p31NF,p32NF,p33NF,p34NF,p35NF,p36NF,p37NF,p38NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | ed p =>
    simp only [invNF123]
    all_goals repeat first | split | (simp_all [Domain,decode,p24Domain,p25Domain,p26Domain,p28Domain,p29Domain,p30Domain,p31Domain,p32Domain,p33Domain,p34Domain,p35Domain,p36Domain,p37Domain,p38Domain,p24NF,p25NF,p26NF,p28NF,p29NF,p30NF,p31NF,p32NF,p33NF,p34NF,p35NF,p36NF,p37NF,p38NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
#print axioms inverse_valid_NF123
end LuRazClosure.SourcePieces
