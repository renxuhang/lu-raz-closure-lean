import LatticeInversePart0
import LatticeInversePart1
import LatticeInversePart2
import LatticeInversePart3
import LatticeInversePart4
import LatticeInversePart5
import LatticeInversePart6
import LatticeInversePart7
import LatticeInversePart8
namespace LuRazClosure.SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem full_code (R : Nat → Prop) : CoreFull R ↔ coreCode R=15 := by
  classical
  by_cases h1 : R 1 <;> by_cases h2 : R 2 <;> by_cases h3 : R 3 <;> by_cases h4 : R 4 <;> simp [CoreFull,coreCode,h1,h2,h3,h4]
theorem small_tag_le (z : NFSmall) : z.tag≤5 := by cases z <;> decide
theorem Shape.code_eq (q : Nat) (hq : 4≤q) (z : Shape) (hz : z.Valid q) : coreCode (z.eval q)=z.code := by
  cases z with
  | small z =>
    exact (small_core_code z.tag (small_tag_le z) (z.eval q)).mp (NFSmall.core q hq z)
  | c23 z =>
    exact (core23_code (z.eval q)).mp (NF23.core q hq z hz)
  | c123 z =>
    exact (core123_code (z.eval q)).mp (NF123.core q hq z hz)
  | c14 z =>
    exact (core14_code (z.eval q)).mp (NF14.core q hq z hz)
  | c24 z =>
    exact (core24_code (z.eval q)).mp (NF24.core q hq z)
  | c124 z =>
    exact (core124_code (z.eval q)).mp (NF124.core q hq z hz)
  | c134 z =>
    exact (core134_code (z.eval q)).mp (NF134.core q hq z hz)
  | c234 z =>
    exact (core234_code (z.eval q)).mp (NF234.core q hq z hz)
  | full z =>
    exact (full_code (z.eval q)).mp (NFFull.core q hq z hz)
theorem Shape.generated (q : Nat) (hq : 4≤q) (z : Shape) (hz : z.Valid q) : Generated q (z.eval q) := by
  cases z with
  | small z => exact NFSmall.generated q hq z
  | c23 z => exact NF23.generated q hq z hz
  | c123 z => exact NF123.generated q hq z hz
  | c14 z => exact NF14.generated q hq z hz
  | c24 z => exact NF24.generated q hq z
  | c124 z => exact NF124.generated q hq z hz
  | c134 z => exact NF134.generated q hq z hz
  | c234 z => exact NF234.generated q hq z hz
  | full z => exact NFFull.generated q hq z hz
theorem Shape.unique (q : Nat) (hq : 4≤q) (a b : Shape) (ha : a.Valid q) (hb : b.Valid q)
    (he : ∀ e,a.eval q e↔b.eval q e) : a=b := by
  have hc : a.code=b.code := by
    rw [←Shape.code_eq q hq a ha,←Shape.code_eq q hq b hb]
    apply congrArg coreCode
    funext e
    exact propext (he e)
  cases a with
  | small a =>
    cases b with
    | small b =>
      exact congrArg Shape.small (NFSmall.unique q hq a b he)
    | c23 b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le a
      omega
    | c123 b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le a
      omega
    | c14 b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le a
      omega
    | c24 b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le a
      omega
    | c124 b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le a
      omega
    | c134 b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le a
      omega
    | c234 b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le a
      omega
    | full b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le a
      omega
  | c23 a =>
    cases b with
    | small b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le b
      omega
    | c23 b =>
      exact congrArg Shape.c23 (NF23.unique q hq a b ha hb he)
    | c123 b =>
      simp only [Shape.code] at hc
      omega
    | c14 b =>
      simp only [Shape.code] at hc
      omega
    | c24 b =>
      simp only [Shape.code] at hc
      omega
    | c124 b =>
      simp only [Shape.code] at hc
      omega
    | c134 b =>
      simp only [Shape.code] at hc
      omega
    | c234 b =>
      simp only [Shape.code] at hc
      omega
    | full b =>
      simp only [Shape.code] at hc
      omega
  | c123 a =>
    cases b with
    | small b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le b
      omega
    | c23 b =>
      simp only [Shape.code] at hc
      omega
    | c123 b =>
      exact congrArg Shape.c123 (NF123.unique q hq a b ha hb he)
    | c14 b =>
      simp only [Shape.code] at hc
      omega
    | c24 b =>
      simp only [Shape.code] at hc
      omega
    | c124 b =>
      simp only [Shape.code] at hc
      omega
    | c134 b =>
      simp only [Shape.code] at hc
      omega
    | c234 b =>
      simp only [Shape.code] at hc
      omega
    | full b =>
      simp only [Shape.code] at hc
      omega
  | c14 a =>
    cases b with
    | small b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le b
      omega
    | c23 b =>
      simp only [Shape.code] at hc
      omega
    | c123 b =>
      simp only [Shape.code] at hc
      omega
    | c14 b =>
      exact congrArg Shape.c14 (NF14.unique q hq a b ha hb he)
    | c24 b =>
      simp only [Shape.code] at hc
      omega
    | c124 b =>
      simp only [Shape.code] at hc
      omega
    | c134 b =>
      simp only [Shape.code] at hc
      omega
    | c234 b =>
      simp only [Shape.code] at hc
      omega
    | full b =>
      simp only [Shape.code] at hc
      omega
  | c24 a =>
    cases b with
    | small b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le b
      omega
    | c23 b =>
      simp only [Shape.code] at hc
      omega
    | c123 b =>
      simp only [Shape.code] at hc
      omega
    | c14 b =>
      simp only [Shape.code] at hc
      omega
    | c24 b =>
      exact congrArg Shape.c24 (NF24.unique q hq a b he)
    | c124 b =>
      simp only [Shape.code] at hc
      omega
    | c134 b =>
      simp only [Shape.code] at hc
      omega
    | c234 b =>
      simp only [Shape.code] at hc
      omega
    | full b =>
      simp only [Shape.code] at hc
      omega
  | c124 a =>
    cases b with
    | small b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le b
      omega
    | c23 b =>
      simp only [Shape.code] at hc
      omega
    | c123 b =>
      simp only [Shape.code] at hc
      omega
    | c14 b =>
      simp only [Shape.code] at hc
      omega
    | c24 b =>
      simp only [Shape.code] at hc
      omega
    | c124 b =>
      exact congrArg Shape.c124 (NF124.unique q hq a b ha hb he)
    | c134 b =>
      simp only [Shape.code] at hc
      omega
    | c234 b =>
      simp only [Shape.code] at hc
      omega
    | full b =>
      simp only [Shape.code] at hc
      omega
  | c134 a =>
    cases b with
    | small b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le b
      omega
    | c23 b =>
      simp only [Shape.code] at hc
      omega
    | c123 b =>
      simp only [Shape.code] at hc
      omega
    | c14 b =>
      simp only [Shape.code] at hc
      omega
    | c24 b =>
      simp only [Shape.code] at hc
      omega
    | c124 b =>
      simp only [Shape.code] at hc
      omega
    | c134 b =>
      exact congrArg Shape.c134 (NF134.unique q hq a b ha hb he)
    | c234 b =>
      simp only [Shape.code] at hc
      omega
    | full b =>
      simp only [Shape.code] at hc
      omega
  | c234 a =>
    cases b with
    | small b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le b
      omega
    | c23 b =>
      simp only [Shape.code] at hc
      omega
    | c123 b =>
      simp only [Shape.code] at hc
      omega
    | c14 b =>
      simp only [Shape.code] at hc
      omega
    | c24 b =>
      simp only [Shape.code] at hc
      omega
    | c124 b =>
      simp only [Shape.code] at hc
      omega
    | c134 b =>
      simp only [Shape.code] at hc
      omega
    | c234 b =>
      exact congrArg Shape.c234 (NF234.unique q hq a b ha hb he)
    | full b =>
      simp only [Shape.code] at hc
      omega
  | full a =>
    cases b with
    | small b =>
      simp only [Shape.code] at hc
      have hl := small_tag_le b
      omega
    | c23 b =>
      simp only [Shape.code] at hc
      omega
    | c123 b =>
      simp only [Shape.code] at hc
      omega
    | c14 b =>
      simp only [Shape.code] at hc
      omega
    | c24 b =>
      simp only [Shape.code] at hc
      omega
    | c124 b =>
      simp only [Shape.code] at hc
      omega
    | c134 b =>
      simp only [Shape.code] at hc
      omega
    | c234 b =>
      simp only [Shape.code] at hc
      omega
    | full b =>
      exact congrArg Shape.full (NFFull.unique q hq a b ha hb he)
theorem domain_ids (q i a b : Nat) (hd : Domain q i a b) : i∈positiveIds := by
  unfold Domain at hd
  split at hd <;> simp_all [positiveIds]
theorem decode_valid (q i a b : Nat) (hq : 4≤q) (hd : Domain q i a b) : (decode q i a b).Valid q := by
  have hi := domain_ids q i a b hd
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85 ∨ i=86 ∨ i=87 ∨ i=88 ∨ i=89 ∨ i=90 ∨ i=91 := by simpa [positiveIds] using hi
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; exact p12_valid q a b hq hd
  · subst i; exact p13_valid q a b hq hd
  · subst i; exact p14_valid q a b hq hd
  · subst i; exact p15_valid q a b hq hd
  · subst i; exact p17_valid q a b hq hd
  · subst i; exact p18_valid q a b hq hd
  · subst i; exact p19_valid q a b hq hd
  · subst i; exact p20_valid q a b hq hd
  · subst i; exact p21_valid q a b hq hd
  · subst i; exact p22_valid q a b hq hd
  · subst i; exact p23_valid q a b hq hd
  · subst i; exact p24_valid q a b hq hd
  · subst i; exact p25_valid q a b hq hd
  · subst i; exact p26_valid q a b hq hd
  · subst i; exact p28_valid q a b hq hd
  · subst i; exact p29_valid q a b hq hd
  · subst i; exact p30_valid q a b hq hd
  · subst i; exact p31_valid q a b hq hd
  · subst i; exact p32_valid q a b hq hd
  · subst i; exact p33_valid q a b hq hd
  · subst i; exact p34_valid q a b hq hd
  · subst i; exact p35_valid q a b hq hd
  · subst i; exact p36_valid q a b hq hd
  · subst i; exact p37_valid q a b hq hd
  · subst i; exact p38_valid q a b hq hd
  · subst i; exact p39_valid q a b hq hd
  · subst i; exact p40_valid q a b hq hd
  · subst i; exact p41_valid q a b hq hd
  · subst i; exact p42_valid q a b hq hd
  · subst i; exact p43_valid q a b hq hd
  · subst i; exact p44_valid q a b hq hd
  · subst i; exact p45_valid q a b hq hd
  · subst i; exact p46_valid q a b hq hd
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; trivial
  · subst i; exact p53_valid q a b hq hd
  · subst i; exact p54_valid q a b hq hd
  · subst i; exact p55_valid q a b hq hd
  · subst i; exact p56_valid q a b hq hd
  · subst i; exact p57_valid q a b hq hd
  · subst i; exact p58_valid q a b hq hd
  · subst i; exact p59_valid q a b hq hd
  · subst i; exact p60_valid q a b hq hd
  · subst i; exact p61_valid q a b hq hd
  · subst i; exact p62_valid q a b hq hd
  · subst i; exact p63_valid q a b hq hd
  · subst i; exact p64_valid q a b hq hd
  · subst i; exact p65_valid q a b hq hd
  · subst i; exact p66_valid q a b hq hd
  · subst i; exact p67_valid q a b hq hd
  · subst i; exact p68_valid q a b hq hd
  · subst i; exact p69_valid q a b hq hd
  · subst i; exact p70_valid q a b hq hd
  · subst i; exact p71_valid q a b hq hd
  · subst i; exact p72_valid q a b hq hd
  · subst i; exact p73_valid q a b hq hd
  · subst i; exact p74_valid q a b hq hd
  · subst i; exact p75_valid q a b hq hd
  · subst i; exact p76_valid q a b hq hd
  · subst i; exact p77_valid q a b hq hd
  · subst i; exact p78_valid q a b hq hd
  · subst i; exact p79_valid q a b hq hd
  · subst i; exact p80_valid q a b hq hd
  · subst i; exact p81_valid q a b hq hd
  · subst i; exact p82_valid q a b hq hd
  · subst i; exact p83_valid q a b hq hd
  · subst i; exact p84_valid q a b hq hd
  · subst i; exact p85_valid q a b hq hd
  · subst i; exact p86_valid q a b hq hd
  · subst i; exact p87_valid q a b hq hd
  · subst i; exact p88_valid q a b hq hd
  · subst i; exact p89_valid q a b hq hd
  · subst i; exact p90_valid q a b hq hd
  · subst i; exact p91_valid q a b hq hd
theorem identify_decode (q i a b : Nat) (hq : 4≤q) (hd : Domain q i a b) : identify q (decode q i a b)=(i,a,b) := by
  have hi := domain_ids q i a b hd
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85 ∨ i=86 ∨ i=87 ∨ i=88 ∨ i=89 ∨ i=90 ∨ i=91 := by simpa [positiveIds] using hi
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst i; exact p0_identify q a b hq hd
  · subst i; exact p1_identify q a b hq hd
  · subst i; exact p2_identify q a b hq hd
  · subst i; exact p3_identify q a b hq hd
  · subst i; exact p4_identify q a b hq hd
  · subst i; exact p5_identify q a b hq hd
  · subst i; exact p6_identify q a b hq hd
  · subst i; exact p7_identify q a b hq hd
  · subst i; exact p8_identify q a b hq hd
  · subst i; exact p9_identify q a b hq hd
  · subst i; exact p10_identify q a b hq hd
  · subst i; exact p11_identify q a b hq hd
  · subst i; exact p12_identify q a b hq hd
  · subst i; exact p13_identify q a b hq hd
  · subst i; exact p14_identify q a b hq hd
  · subst i; exact p15_identify q a b hq hd
  · subst i; exact p17_identify q a b hq hd
  · subst i; exact p18_identify q a b hq hd
  · subst i; exact p19_identify q a b hq hd
  · subst i; exact p20_identify q a b hq hd
  · subst i; exact p21_identify q a b hq hd
  · subst i; exact p22_identify q a b hq hd
  · subst i; exact p23_identify q a b hq hd
  · subst i; exact p24_identify q a b hq hd
  · subst i; exact p25_identify q a b hq hd
  · subst i; exact p26_identify q a b hq hd
  · subst i; exact p28_identify q a b hq hd
  · subst i; exact p29_identify q a b hq hd
  · subst i; exact p30_identify q a b hq hd
  · subst i; exact p31_identify q a b hq hd
  · subst i; exact p32_identify q a b hq hd
  · subst i; exact p33_identify q a b hq hd
  · subst i; exact p34_identify q a b hq hd
  · subst i; exact p35_identify q a b hq hd
  · subst i; exact p36_identify q a b hq hd
  · subst i; exact p37_identify q a b hq hd
  · subst i; exact p38_identify q a b hq hd
  · subst i; exact p39_identify q a b hq hd
  · subst i; exact p40_identify q a b hq hd
  · subst i; exact p41_identify q a b hq hd
  · subst i; exact p42_identify q a b hq hd
  · subst i; exact p43_identify q a b hq hd
  · subst i; exact p44_identify q a b hq hd
  · subst i; exact p45_identify q a b hq hd
  · subst i; exact p46_identify q a b hq hd
  · subst i; exact p47_identify q a b hq hd
  · subst i; exact p48_identify q a b hq hd
  · subst i; exact p49_identify q a b hq hd
  · subst i; exact p50_identify q a b hq hd
  · subst i; exact p51_identify q a b hq hd
  · subst i; exact p52_identify q a b hq hd
  · subst i; exact p53_identify q a b hq hd
  · subst i; exact p54_identify q a b hq hd
  · subst i; exact p55_identify q a b hq hd
  · subst i; exact p56_identify q a b hq hd
  · subst i; exact p57_identify q a b hq hd
  · subst i; exact p58_identify q a b hq hd
  · subst i; exact p59_identify q a b hq hd
  · subst i; exact p60_identify q a b hq hd
  · subst i; exact p61_identify q a b hq hd
  · subst i; exact p62_identify q a b hq hd
  · subst i; exact p63_identify q a b hq hd
  · subst i; exact p64_identify q a b hq hd
  · subst i; exact p65_identify q a b hq hd
  · subst i; exact p66_identify q a b hq hd
  · subst i; exact p67_identify q a b hq hd
  · subst i; exact p68_identify q a b hq hd
  · subst i; exact p69_identify q a b hq hd
  · subst i; exact p70_identify q a b hq hd
  · subst i; exact p71_identify q a b hq hd
  · subst i; exact p72_identify q a b hq hd
  · subst i; exact p73_identify q a b hq hd
  · subst i; exact p74_identify q a b hq hd
  · subst i; exact p75_identify q a b hq hd
  · subst i; exact p76_identify q a b hq hd
  · subst i; exact p77_identify q a b hq hd
  · subst i; exact p78_identify q a b hq hd
  · subst i; exact p79_identify q a b hq hd
  · subst i; exact p80_identify q a b hq hd
  · subst i; exact p81_identify q a b hq hd
  · subst i; exact p82_identify q a b hq hd
  · subst i; exact p83_identify q a b hq hd
  · subst i; exact p84_identify q a b hq hd
  · subst i; exact p85_identify q a b hq hd
  · subst i; exact p86_identify q a b hq hd
  · subst i; exact p87_identify q a b hq hd
  · subst i; exact p88_identify q a b hq hd
  · subst i; exact p89_identify q a b hq hd
  · subst i; exact p90_identify q a b hq hd
  · subst i; exact p91_identify q a b hq hd
theorem decode_eval (q i a b : Nat) (hq : 4≤q) (hd : Domain q i a b) : ∀ e,(decode q i a b).eval q e↔pieceSet q i a b e := by
  have hi := domain_ids q i a b hd
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85 ∨ i=86 ∨ i=87 ∨ i=88 ∨ i=89 ∨ i=90 ∨ i=91 := by simpa [positiveIds] using hi
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst i; intro e; exact p0_eval q a b e hq hd
  · subst i; intro e; exact p1_eval q a b e hq hd
  · subst i; intro e; exact p2_eval q a b e hq hd
  · subst i; intro e; exact p3_eval q a b e hq hd
  · subst i; intro e; exact p4_eval q a b e hq hd
  · subst i; intro e; exact p5_eval q a b e hq hd
  · subst i; intro e; exact p6_eval q a b e hq hd
  · subst i; intro e; exact p7_eval q a b e hq hd
  · subst i; intro e; exact p8_eval q a b e hq hd
  · subst i; intro e; exact p9_eval q a b e hq hd
  · subst i; intro e; exact p10_eval q a b e hq hd
  · subst i; intro e; exact p11_eval q a b e hq hd
  · subst i; intro e; exact p12_eval q a b e hq hd
  · subst i; intro e; exact p13_eval q a b e hq hd
  · subst i; intro e; exact p14_eval q a b e hq hd
  · subst i; intro e; exact p15_eval q a b e hq hd
  · subst i; intro e; exact p17_eval q a b e hq hd
  · subst i; intro e; exact p18_eval q a b e hq hd
  · subst i; intro e; exact p19_eval q a b e hq hd
  · subst i; intro e; exact p20_eval q a b e hq hd
  · subst i; intro e; exact p21_eval q a b e hq hd
  · subst i; intro e; exact p22_eval q a b e hq hd
  · subst i; intro e; exact p23_eval q a b e hq hd
  · subst i; intro e; exact p24_eval q a b e hq hd
  · subst i; intro e; exact p25_eval q a b e hq hd
  · subst i; intro e; exact p26_eval q a b e hq hd
  · subst i; intro e; exact p28_eval q a b e hq hd
  · subst i; intro e; exact p29_eval q a b e hq hd
  · subst i; intro e; exact p30_eval q a b e hq hd
  · subst i; intro e; exact p31_eval q a b e hq hd
  · subst i; intro e; exact p32_eval q a b e hq hd
  · subst i; intro e; exact p33_eval q a b e hq hd
  · subst i; intro e; exact p34_eval q a b e hq hd
  · subst i; intro e; exact p35_eval q a b e hq hd
  · subst i; intro e; exact p36_eval q a b e hq hd
  · subst i; intro e; exact p37_eval q a b e hq hd
  · subst i; intro e; exact p38_eval q a b e hq hd
  · subst i; intro e; exact p39_eval q a b e hq hd
  · subst i; intro e; exact p40_eval q a b e hq hd
  · subst i; intro e; exact p41_eval q a b e hq hd
  · subst i; intro e; exact p42_eval q a b e hq hd
  · subst i; intro e; exact p43_eval q a b e hq hd
  · subst i; intro e; exact p44_eval q a b e hq hd
  · subst i; intro e; exact p45_eval q a b e hq hd
  · subst i; intro e; exact p46_eval q a b e hq hd
  · subst i; intro e; exact p47_eval q a b e hq hd
  · subst i; intro e; exact p48_eval q a b e hq hd
  · subst i; intro e; exact p49_eval q a b e hq hd
  · subst i; intro e; exact p50_eval q a b e hq hd
  · subst i; intro e; exact p51_eval q a b e hq hd
  · subst i; intro e; exact p52_eval q a b e hq hd
  · subst i; intro e; exact p53_eval q a b e hq hd
  · subst i; intro e; exact p54_eval q a b e hq hd
  · subst i; intro e; exact p55_eval q a b e hq hd
  · subst i; intro e; exact p56_eval q a b e hq hd
  · subst i; intro e; exact p57_eval q a b e hq hd
  · subst i; intro e; exact p58_eval q a b e hq hd
  · subst i; intro e; exact p59_eval q a b e hq hd
  · subst i; intro e; exact p60_eval q a b e hq hd
  · subst i; intro e; exact p61_eval q a b e hq hd
  · subst i; intro e; exact p62_eval q a b e hq hd
  · subst i; intro e; exact p63_eval q a b e hq hd
  · subst i; intro e; exact p64_eval q a b e hq hd
  · subst i; intro e; exact p65_eval q a b e hq hd
  · subst i; intro e; exact p66_eval q a b e hq hd
  · subst i; intro e; exact p67_eval q a b e hq hd
  · subst i; intro e; exact p68_eval q a b e hq hd
  · subst i; intro e; exact p69_eval q a b e hq hd
  · subst i; intro e; exact p70_eval q a b e hq hd
  · subst i; intro e; exact p71_eval q a b e hq hd
  · subst i; intro e; exact p72_eval q a b e hq hd
  · subst i; intro e; exact p73_eval q a b e hq hd
  · subst i; intro e; exact p74_eval q a b e hq hd
  · subst i; intro e; exact p75_eval q a b e hq hd
  · subst i; intro e; exact p76_eval q a b e hq hd
  · subst i; intro e; exact p77_eval q a b e hq hd
  · subst i; intro e; exact p78_eval q a b e hq hd
  · subst i; intro e; exact p79_eval q a b e hq hd
  · subst i; intro e; exact p80_eval q a b e hq hd
  · subst i; intro e; exact p81_eval q a b e hq hd
  · subst i; intro e; exact p82_eval q a b e hq hd
  · subst i; intro e; exact p83_eval q a b e hq hd
  · subst i; intro e; exact p84_eval q a b e hq hd
  · subst i; intro e; exact p85_eval q a b e hq hd
  · subst i; intro e; exact p86_eval q a b e hq hd
  · subst i; intro e; exact p87_eval q a b e hq hd
  · subst i; intro e; exact p88_eval q a b e hq hd
  · subst i; intro e; exact p89_eval q a b e hq hd
  · subst i; intro e; exact p90_eval q a b e hq hd
  · subst i; intro e; exact p91_eval q a b e hq hd
theorem shape_of_generated (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hg : Generated q R) :
    ∃ z : Shape,z.Valid q ∧ ∀ e,R e↔z.eval q e := by
  have hm := (closure_members_exact q hq R).mpr hg
  rw [closureMembers,List.mem_append] at hm
  rcases hm with hp | hf
  · obtain ⟨k,hk,hr⟩ := List.mem_flatMap.mp hp
    have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=13 ∨ k=14 := by simpa [partialCodes] using hk
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h
    · subst k
      obtain ⟨z,hz,heq⟩ := List.mem_map.mp hr
      refine ⟨.small z,True.intro,?_⟩
      intro e; exact (Iff.of_eq (congrFun heq e)).symm
    · subst k
      obtain ⟨z,hz,heq⟩ := List.mem_map.mp hr
      refine ⟨.small z,True.intro,?_⟩
      intro e; exact (Iff.of_eq (congrFun heq e)).symm
    · subst k
      obtain ⟨z,hz,heq⟩ := List.mem_map.mp hr
      refine ⟨.small z,True.intro,?_⟩
      intro e; exact (Iff.of_eq (congrFun heq e)).symm
    · subst k
      obtain ⟨z,hz,heq⟩ := List.mem_map.mp hr
      refine ⟨.small z,True.intro,?_⟩
      intro e; exact (Iff.of_eq (congrFun heq e)).symm
    · subst k
      obtain ⟨z,hz,heq⟩ := List.mem_map.mp hr
      refine ⟨.small z,True.intro,?_⟩
      intro e; exact (Iff.of_eq (congrFun heq e)).symm
    · subst k
      obtain ⟨z,hz,heq⟩ := List.mem_map.mp hr
      refine ⟨.small z,True.intro,?_⟩
      intro e; exact (Iff.of_eq (congrFun heq e)).symm
    · subst k
      obtain ⟨z,hz,heq⟩ := List.mem_map.mp hr
      refine ⟨.c23 z,(enum23_exact q hq z).mp hz,?_⟩
      intro e; exact (Iff.of_eq (congrFun heq e)).symm
    · subst k
      obtain ⟨z,hz,heq⟩ := List.mem_map.mp hr
      refine ⟨.c123 z,(enum123_exact q hq z).mp hz,?_⟩
      intro e; exact (Iff.of_eq (congrFun heq e)).symm
    · subst k
      obtain ⟨z,hz,heq⟩ := List.mem_map.mp hr
      refine ⟨.c14 z,(enum14_exact q hq z).mp hz,?_⟩
      intro e; exact (Iff.of_eq (congrFun heq e)).symm
    · subst k
      obtain ⟨z,hz,heq⟩ := List.mem_map.mp hr
      refine ⟨.c24 z,True.intro,?_⟩
      intro e; exact (Iff.of_eq (congrFun heq e)).symm
    · subst k
      obtain ⟨z,hz,heq⟩ := List.mem_map.mp hr
      refine ⟨.c124 z,(enum124_exact q hq z).mp hz,?_⟩
      intro e; exact (Iff.of_eq (congrFun heq e)).symm
    · subst k
      obtain ⟨z,hz,heq⟩ := List.mem_map.mp hr
      refine ⟨.c134 z,(enum134_exact q hq z).mp hz,?_⟩
      intro e; exact (Iff.of_eq (congrFun heq e)).symm
    · subst k
      obtain ⟨z,hz,heq⟩ := List.mem_map.mp hr
      refine ⟨.c234 z,(enum234_exact q hq z).mp hz,?_⟩
      intro e; exact (Iff.of_eq (congrFun heq e)).symm
  · obtain ⟨z,hz,heq⟩ := List.mem_map.mp hf
    refine ⟨.full z,(enumFull_exact q hq z).mp hz,?_⟩
    intro e; exact (Iff.of_eq (congrFun heq e)).symm
#print axioms Shape.code_eq
#print axioms Shape.generated
#print axioms Shape.unique
#print axioms domain_ids
#print axioms decode_valid
#print axioms identify_decode
#print axioms decode_eval
#print axioms shape_of_generated
end LuRazClosure.SourcePieces
