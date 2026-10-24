import LatticeShapeDefs
namespace LuRazClosure.SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem inverse_valid_NFFull (q : Nat) (hq : 4≤q) (z : NFFull) (hz : z.Valid q) :
    let p := invNFFull q z
    Domain q p.1 p.2.1 p.2.2 ∧ decode q p.1 p.2.1 p.2.2=.full z := by
  cases z with
  | noNInterval k =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | noNMJRight b =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | noNMJLeft a =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | noNMK k =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | noNCMJ b =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | noH1Short p k =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | noH1ZL a =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | noH1Exception =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | noH2 a =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | noFive a =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | leftGap p a =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | full =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | rightGap b c =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
  | isolatedR b c =>
    simp only [invNFFull]
    all_goals repeat first | split | (simp_all [Domain,decode,p78Domain,p79Domain,p80Domain,p81Domain,p82Domain,p83Domain,p84Domain,p85Domain,p86Domain,p87Domain,p88Domain,p89Domain,p90Domain,p91Domain,p78NF,p79NF,p80NF,p81NF,p82NF,p83NF,p84NF,p85NF,p86NF,p87NF,p88NF,p89NF,p90NF,p91NF,P,JReachable,g,NF23.Valid,NF123.Valid,NF14.Valid,NF124.Valid,NF134.Valid,NF234.Valid,NFFull.Valid] <;> omega) | constructor | congr 1
#print axioms inverse_valid_NFFull
end LuRazClosure.SourcePieces
