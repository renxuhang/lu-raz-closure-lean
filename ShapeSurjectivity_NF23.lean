import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem inverse_valid_NF23 (q : Nat) (hq : 4≤q) (z : NF23) (hz : z.Valid q) :
    let p := invNF23 q z
    Domain q p.1 p.2.1 p.2.2 ∧ decode q p.1 p.2.1 p.2.2=.c23 z := by
  cases z with
  | lp t p =>
    simp only [invNF23]
    all_goals repeat first | split | (simp_all [Domain,decode,p12Domain,p13Domain,p14Domain,p15Domain,p17Domain,p18Domain,p19Domain,p20Domain,p21Domain,p22Domain,p23Domain,p12NF,p13NF,p14NF,p15NF,p17NF,p18NF,p19NF,p20NF,p21NF,p22NF,p23NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | filledM =>
    simp only [invNF23]
    all_goals repeat first | split | (simp_all [Domain,decode,p12Domain,p13Domain,p14Domain,p15Domain,p17Domain,p18Domain,p19Domain,p20Domain,p21Domain,p22Domain,p23Domain,p12NF,p13NF,p14NF,p15NF,p17NF,p18NF,p19NF,p20NF,p21NF,p22NF,p23NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | dgap p =>
    simp only [invNF23]
    all_goals repeat first | split | (simp_all [Domain,decode,p12Domain,p13Domain,p14Domain,p15Domain,p17Domain,p18Domain,p19Domain,p20Domain,p21Domain,p22Domain,p23Domain,p12NF,p13NF,p14NF,p15NF,p17NF,p18NF,p19NF,p20NF,p21NF,p22NF,p23NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | full =>
    simp only [invNF23]
    all_goals repeat first | split | (simp_all [Domain,decode,p12Domain,p13Domain,p14Domain,p15Domain,p17Domain,p18Domain,p19Domain,p20Domain,p21Domain,p22Domain,p23Domain,p12NF,p13NF,p14NF,p15NF,p17NF,p18NF,p19NF,p20NF,p21NF,p22NF,p23NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | creg t =>
    simp only [invNF23]
    all_goals repeat first | split | (simp_all [Domain,decode,p12Domain,p13Domain,p14Domain,p15Domain,p17Domain,p18Domain,p19Domain,p20Domain,p21Domain,p22Domain,p23Domain,p12NF,p13NF,p14NF,p15NF,p17NF,p18NF,p19NF,p20NF,p21NF,p22NF,p23NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | cexception =>
    simp only [invNF23]
    all_goals repeat first | split | (simp_all [Domain,decode,p12Domain,p13Domain,p14Domain,p15Domain,p17Domain,p18Domain,p19Domain,p20Domain,p21Domain,p22Domain,p23Domain,p12NF,p13NF,p14NF,p15NF,p17NF,p18NF,p19NF,p20NF,p21NF,p22NF,p23NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
#print axioms inverse_valid_NF23
end LuRazClosure.SourcePieces
