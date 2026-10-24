import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem inverse_valid_NF124 (q : Nat) (hq : 4≤q) (z : NF124) (hz : z.Valid q) :
    let p := invNF124 q z
    Domain q p.1 p.2.1 p.2.2 ∧ decode q p.1 p.2.1 p.2.2=.c124 z := by
  cases z with
  | interval a k =>
    simp only [invNF124]
    all_goals repeat first | split | (simp_all [Domain,decode,p53Domain,p54Domain,p55Domain,p56Domain,p57Domain,p58Domain,p59Domain,p53NF,p54NF,p55NF,p56NF,p57NF,p58NF,p59NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | agap a k =>
    simp only [invNF124]
    all_goals repeat first | split | (simp_all [Domain,decode,p53Domain,p54Domain,p55Domain,p56Domain,p57Domain,p58Domain,p59Domain,p53NF,p54NF,p55NF,p56NF,p57NF,p58NF,p59NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | ak z =>
    simp only [invNF124]
    cases z
    all_goals repeat first | split | (simp_all [Domain,decode,p53Domain,p54Domain,p55Domain,p56Domain,p57Domain,p58Domain,p59Domain,p53NF,p54NF,p55NF,p56NF,p57NF,p58NF,p59NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
#print axioms inverse_valid_NF124
end LuRazClosure.SourcePieces
