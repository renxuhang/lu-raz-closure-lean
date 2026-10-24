import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem inverse_valid_NF234 (q : Nat) (hq : 4≤q) (z : NF234) (hz : z.Valid q) :
    let p := invNF234 q z
    Domain q p.1 p.2.1 p.2.2 ∧ decode q p.1 p.2.1 p.2.2=.c234 z := by
  cases z with
  | kr p k =>
    simp only [invNF234]
    all_goals repeat first | split | (simp_all [Domain,decode,p71Domain,p72Domain,p73Domain,p74Domain,p75Domain,p76Domain,p77Domain,p71NF,p72NF,p73NF,p74NF,p75NF,p76NF,p77NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | dg p =>
    simp only [invNF234]
    all_goals repeat first | split | (simp_all [Domain,decode,p71Domain,p72Domain,p73Domain,p74Domain,p75Domain,p76Domain,p77Domain,p71NF,p72NF,p73NF,p74NF,p75NF,p76NF,p77NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | km k =>
    simp only [invNF234]
    all_goals repeat first | split | (simp_all [Domain,decode,p71Domain,p72Domain,p73Domain,p74Domain,p75Domain,p76Domain,p77Domain,p71NF,p72NF,p73NF,p74NF,p75NF,p76NF,p77NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | ck k =>
    simp only [invNF234]
    all_goals repeat first | split | (simp_all [Domain,decode,p71Domain,p72Domain,p73Domain,p74Domain,p75Domain,p76Domain,p77Domain,p71NF,p72NF,p73NF,p74NF,p75NF,p76NF,p77NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | last =>
    simp only [invNF234]
    all_goals repeat first | split | (simp_all [Domain,decode,p71Domain,p72Domain,p73Domain,p74Domain,p75Domain,p76Domain,p77Domain,p71NF,p72NF,p73NF,p74NF,p75NF,p76NF,p77NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
#print axioms inverse_valid_NF234
end LuRazClosure.SourcePieces
