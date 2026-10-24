import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem inverse_valid_NF134 (q : Nat) (hq : 4≤q) (z : NF134) (hz : z.Valid q) :
    let p := invNF134 q z
    Domain q p.1 p.2.1 p.2.2 ∧ decode q p.1 p.2.1 p.2.2=.c134 z := by
  cases z with
  | ej a =>
    simp only [invNF134]
    all_goals repeat first | split | (simp_all [Domain,decode,p60Domain,p61Domain,p62Domain,p63Domain,p64Domain,p65Domain,p66Domain,p67Domain,p68Domain,p69Domain,p70Domain,p60NF,p61NF,p62NF,p63NF,p64NF,p65NF,p66NF,p67NF,p68NF,p69NF,p70NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | aej a =>
    simp only [invNF134]
    all_goals repeat first | split | (simp_all [Domain,decode,p60Domain,p61Domain,p62Domain,p63Domain,p64Domain,p65Domain,p66Domain,p67Domain,p68Domain,p69Domain,p70Domain,p60NF,p61NF,p62NF,p63NF,p64NF,p65NF,p66NF,p67NF,p68NF,p69NF,p70NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | cj b =>
    simp only [invNF134]
    all_goals repeat first | split | (simp_all [Domain,decode,p60Domain,p61Domain,p62Domain,p63Domain,p64Domain,p65Domain,p66Domain,p67Domain,p68Domain,p69Domain,p70Domain,p60NF,p61NF,p62NF,p63NF,p64NF,p65NF,p66NF,p67NF,p68NF,p69NF,p70NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | zj b =>
    simp only [invNF134]
    all_goals repeat first | split | (simp_all [Domain,decode,p60Domain,p61Domain,p62Domain,p63Domain,p64Domain,p65Domain,p66Domain,p67Domain,p68Domain,p69Domain,p70Domain,p60NF,p61NF,p62NF,p63NF,p64NF,p65NF,p66NF,p67NF,p68NF,p69NF,p70NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | czj b =>
    simp only [invNF134]
    all_goals repeat first | split | (simp_all [Domain,decode,p60Domain,p61Domain,p62Domain,p63Domain,p64Domain,p65Domain,p66Domain,p67Domain,p68Domain,p69Domain,p70Domain,p60NF,p61NF,p62NF,p63NF,p64NF,p65NF,p66NF,p67NF,p68NF,p69NF,p70NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | zjb b =>
    simp only [invNF134]
    all_goals repeat first | split | (simp_all [Domain,decode,p60Domain,p61Domain,p62Domain,p63Domain,p64Domain,p65Domain,p66Domain,p67Domain,p68Domain,p69Domain,p70Domain,p60NF,p61NF,p62NF,p63NF,p64NF,p65NF,p66NF,p67NF,p68NF,p69NF,p70NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | cjb b =>
    simp only [invNF134]
    all_goals repeat first | split | (simp_all [Domain,decode,p60Domain,p61Domain,p62Domain,p63Domain,p64Domain,p65Domain,p66Domain,p67Domain,p68Domain,p69Domain,p70Domain,p60NF,p61NF,p62NF,p63NF,p64NF,p65NF,p66NF,p67NF,p68NF,p69NF,p70NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | extra k =>
    simp only [invNF134]
    all_goals repeat first | split | (simp_all [Domain,decode,p60Domain,p61Domain,p62Domain,p63Domain,p64Domain,p65Domain,p66Domain,p67Domain,p68Domain,p69Domain,p70Domain,p60NF,p61NF,p62NF,p63NF,p64NF,p65NF,p66NF,p67NF,p68NF,p69NF,p70NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
#print axioms inverse_valid_NF134
end LuRazClosure.SourcePieces
