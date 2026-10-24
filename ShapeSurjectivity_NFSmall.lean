import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem inverse_valid_NFSmall (q : Nat) (hq : 4≤q) (z : NFSmall)  :
    let p := invNFSmall q z
    Domain q p.1 p.2.1 p.2.2 ∧ decode q p.1 p.2.1 p.2.2=.small z := by
  cases z with
  | bOnly =>
    simp only [invNFSmall]
    all_goals repeat first | split | (simp_all [Domain,decode,p0Domain,p1Domain,p2Domain,p3Domain,p4Domain,p5Domain,p6Domain,p7Domain,p8Domain,p9Domain,p10Domain,p11Domain,p0NF,p1NF,p2NF,p3NF,p4NF,p5NF,p6NF,p7NF,p8NF,p9NF,p10NF,p11NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | aOnly =>
    simp only [invNFSmall]
    all_goals repeat first | split | (simp_all [Domain,decode,p0Domain,p1Domain,p2Domain,p3Domain,p4Domain,p5Domain,p6Domain,p7Domain,p8Domain,p9Domain,p10Domain,p11Domain,p0NF,p1NF,p2NF,p3NF,p4NF,p5NF,p6NF,p7NF,p8NF,p9NF,p10NF,p11NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | ab =>
    simp only [invNFSmall]
    all_goals repeat first | split | (simp_all [Domain,decode,p0Domain,p1Domain,p2Domain,p3Domain,p4Domain,p5Domain,p6Domain,p7Domain,p8Domain,p9Domain,p10Domain,p11Domain,p0NF,p1NF,p2NF,p3NF,p4NF,p5NF,p6NF,p7NF,p8NF,p9NF,p10NF,p11NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | dOnly =>
    simp only [invNFSmall]
    all_goals repeat first | split | (simp_all [Domain,decode,p0Domain,p1Domain,p2Domain,p3Domain,p4Domain,p5Domain,p6Domain,p7Domain,p8Domain,p9Domain,p10Domain,p11Domain,p0NF,p1NF,p2NF,p3NF,p4NF,p5NF,p6NF,p7NF,p8NF,p9NF,p10NF,p11NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | ad =>
    simp only [invNFSmall]
    all_goals repeat first | split | (simp_all [Domain,decode,p0Domain,p1Domain,p2Domain,p3Domain,p4Domain,p5Domain,p6Domain,p7Domain,p8Domain,p9Domain,p10Domain,p11Domain,p0NF,p1NF,p2NF,p3NF,p4NF,p5NF,p6NF,p7NF,p8NF,p9NF,p10NF,p11NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | cOnly =>
    simp only [invNFSmall]
    all_goals repeat first | split | (simp_all [Domain,decode,p0Domain,p1Domain,p2Domain,p3Domain,p4Domain,p5Domain,p6Domain,p7Domain,p8Domain,p9Domain,p10Domain,p11Domain,p0NF,p1NF,p2NF,p3NF,p4NF,p5NF,p6NF,p7NF,p8NF,p9NF,p10NF,p11NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | cb =>
    simp only [invNFSmall]
    all_goals repeat first | split | (simp_all [Domain,decode,p0Domain,p1Domain,p2Domain,p3Domain,p4Domain,p5Domain,p6Domain,p7Domain,p8Domain,p9Domain,p10Domain,p11Domain,p0NF,p1NF,p2NF,p3NF,p4NF,p5NF,p6NF,p7NF,p8NF,p9NF,p10NF,p11NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | eOnly =>
    simp only [invNFSmall]
    all_goals repeat first | split | (simp_all [Domain,decode,p0Domain,p1Domain,p2Domain,p3Domain,p4Domain,p5Domain,p6Domain,p7Domain,p8Domain,p9Domain,p10Domain,p11Domain,p0NF,p1NF,p2NF,p3NF,p4NF,p5NF,p6NF,p7NF,p8NF,p9NF,p10NF,p11NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | ae =>
    simp only [invNFSmall]
    all_goals repeat first | split | (simp_all [Domain,decode,p0Domain,p1Domain,p2Domain,p3Domain,p4Domain,p5Domain,p6Domain,p7Domain,p8Domain,p9Domain,p10Domain,p11Domain,p0NF,p1NF,p2NF,p3NF,p4NF,p5NF,p6NF,p7NF,p8NF,p9NF,p10NF,p11NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | ce =>
    simp only [invNFSmall]
    all_goals repeat first | split | (simp_all [Domain,decode,p0Domain,p1Domain,p2Domain,p3Domain,p4Domain,p5Domain,p6Domain,p7Domain,p8Domain,p9Domain,p10Domain,p11Domain,p0NF,p1NF,p2NF,p3NF,p4NF,p5NF,p6NF,p7NF,p8NF,p9NF,p10NF,p11NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | ac =>
    simp only [invNFSmall]
    all_goals repeat first | split | (simp_all [Domain,decode,p0Domain,p1Domain,p2Domain,p3Domain,p4Domain,p5Domain,p6Domain,p7Domain,p8Domain,p9Domain,p10Domain,p11Domain,p0NF,p1NF,p2NF,p3NF,p4NF,p5NF,p6NF,p7NF,p8NF,p9NF,p10NF,p11NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | acb =>
    simp only [invNFSmall]
    all_goals repeat first | split | (simp_all [Domain,decode,p0Domain,p1Domain,p2Domain,p3Domain,p4Domain,p5Domain,p6Domain,p7Domain,p8Domain,p9Domain,p10Domain,p11Domain,p0NF,p1NF,p2NF,p3NF,p4NF,p5NF,p6NF,p7NF,p8NF,p9NF,p10NF,p11NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
#print axioms inverse_valid_NFSmall
end LuRazClosure.SourcePieces
