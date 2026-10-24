import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem inverse_valid_NF24 (q : Nat) (hq : 4≤q) (z : NF24)  :
    let p := invNF24 q z
    Domain q p.1 p.2.1 p.2.2 ∧ decode q p.1 p.2.1 p.2.2=.c24 z := by
  cases z with
  | k1 =>
    simp only [invNF24]
    all_goals repeat first | split | (simp_all [Domain,decode,p47Domain,p48Domain,p49Domain,p50Domain,p51Domain,p52Domain,p47NF,p48NF,p49NF,p50NF,p51NF,p52NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | k2 =>
    simp only [invNF24]
    all_goals repeat first | split | (simp_all [Domain,decode,p47Domain,p48Domain,p49Domain,p50Domain,p51Domain,p52Domain,p47NF,p48NF,p49NF,p50NF,p51NF,p52NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | joinK =>
    simp only [invNF24]
    all_goals repeat first | split | (simp_all [Domain,decode,p47Domain,p48Domain,p49Domain,p50Domain,p51Domain,p52Domain,p47NF,p48NF,p49NF,p50NF,p51NF,p52NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | fill1 =>
    simp only [invNF24]
    all_goals repeat first | split | (simp_all [Domain,decode,p47Domain,p48Domain,p49Domain,p50Domain,p51Domain,p52Domain,p47NF,p48NF,p49NF,p50NF,p51NF,p52NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | fill2 =>
    simp only [invNF24]
    all_goals repeat first | split | (simp_all [Domain,decode,p47Domain,p48Domain,p49Domain,p50Domain,p51Domain,p52Domain,p47NF,p48NF,p49NF,p50NF,p51NF,p52NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | dBig =>
    simp only [invNF24]
    all_goals repeat first | split | (simp_all [Domain,decode,p47Domain,p48Domain,p49Domain,p50Domain,p51Domain,p52Domain,p47NF,p48NF,p49NF,p50NF,p51NF,p52NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
#print axioms inverse_valid_NF24
end LuRazClosure.SourcePieces
