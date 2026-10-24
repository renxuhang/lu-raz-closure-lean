import LatticePiecePointsPart0
import LatticePiecePointsPart1
import LatticePiecePointsPart2
import LatticePiecePointsPart3
import LatticePiecePointsPart4
import LatticePiecePointsPart5
import LatticePiecePointsPart6
import LatticePiecePointsPart7
import LatticePiecePointsPart8
namespace LuRazClosure.SourcePieces
open LuRazLattice LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
noncomputable section
theorem piece_points_nonneg (q i : Nat) (hq : 4≤q) (hi : i∈positiveIds) (p : Int×Int) (hp : p∈piecePoints q i) : 0≤p.1 ∧ 0≤p.2 := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85 ∨ i=86 ∨ i=87 ∨ i=88 ∨ i=89 ∨ i=90 ∨ i=91 := by simpa [positiveIds] using hi
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst i; exact p0_points_nonneg q hq p hp
  · subst i; exact p1_points_nonneg q hq p hp
  · subst i; exact p2_points_nonneg q hq p hp
  · subst i; exact p3_points_nonneg q hq p hp
  · subst i; exact p4_points_nonneg q hq p hp
  · subst i; exact p5_points_nonneg q hq p hp
  · subst i; exact p6_points_nonneg q hq p hp
  · subst i; exact p7_points_nonneg q hq p hp
  · subst i; exact p8_points_nonneg q hq p hp
  · subst i; exact p9_points_nonneg q hq p hp
  · subst i; exact p10_points_nonneg q hq p hp
  · subst i; exact p11_points_nonneg q hq p hp
  · subst i; exact p12_points_nonneg q hq p hp
  · subst i; exact p13_points_nonneg q hq p hp
  · subst i; exact p14_points_nonneg q hq p hp
  · subst i; exact p15_points_nonneg q hq p hp
  · subst i; exact p17_points_nonneg q hq p hp
  · subst i; exact p18_points_nonneg q hq p hp
  · subst i; exact p19_points_nonneg q hq p hp
  · subst i; exact p20_points_nonneg q hq p hp
  · subst i; exact p21_points_nonneg q hq p hp
  · subst i; exact p22_points_nonneg q hq p hp
  · subst i; exact p23_points_nonneg q hq p hp
  · subst i; exact p24_points_nonneg q hq p hp
  · subst i; exact p25_points_nonneg q hq p hp
  · subst i; exact p26_points_nonneg q hq p hp
  · subst i; exact p28_points_nonneg q hq p hp
  · subst i; exact p29_points_nonneg q hq p hp
  · subst i; exact p30_points_nonneg q hq p hp
  · subst i; exact p31_points_nonneg q hq p hp
  · subst i; exact p32_points_nonneg q hq p hp
  · subst i; exact p33_points_nonneg q hq p hp
  · subst i; exact p34_points_nonneg q hq p hp
  · subst i; exact p35_points_nonneg q hq p hp
  · subst i; exact p36_points_nonneg q hq p hp
  · subst i; exact p37_points_nonneg q hq p hp
  · subst i; exact p38_points_nonneg q hq p hp
  · subst i; exact p39_points_nonneg q hq p hp
  · subst i; exact p40_points_nonneg q hq p hp
  · subst i; exact p41_points_nonneg q hq p hp
  · subst i; exact p42_points_nonneg q hq p hp
  · subst i; exact p43_points_nonneg q hq p hp
  · subst i; exact p44_points_nonneg q hq p hp
  · subst i; exact p45_points_nonneg q hq p hp
  · subst i; exact p46_points_nonneg q hq p hp
  · subst i; exact p47_points_nonneg q hq p hp
  · subst i; exact p48_points_nonneg q hq p hp
  · subst i; exact p49_points_nonneg q hq p hp
  · subst i; exact p50_points_nonneg q hq p hp
  · subst i; exact p51_points_nonneg q hq p hp
  · subst i; exact p52_points_nonneg q hq p hp
  · subst i; exact p53_points_nonneg q hq p hp
  · subst i; exact p54_points_nonneg q hq p hp
  · subst i; exact p55_points_nonneg q hq p hp
  · subst i; exact p56_points_nonneg q hq p hp
  · subst i; exact p57_points_nonneg q hq p hp
  · subst i; exact p58_points_nonneg q hq p hp
  · subst i; exact p59_points_nonneg q hq p hp
  · subst i; exact p60_points_nonneg q hq p hp
  · subst i; exact p61_points_nonneg q hq p hp
  · subst i; exact p62_points_nonneg q hq p hp
  · subst i; exact p63_points_nonneg q hq p hp
  · subst i; exact p64_points_nonneg q hq p hp
  · subst i; exact p65_points_nonneg q hq p hp
  · subst i; exact p66_points_nonneg q hq p hp
  · subst i; exact p67_points_nonneg q hq p hp
  · subst i; exact p68_points_nonneg q hq p hp
  · subst i; exact p69_points_nonneg q hq p hp
  · subst i; exact p70_points_nonneg q hq p hp
  · subst i; exact p71_points_nonneg q hq p hp
  · subst i; exact p72_points_nonneg q hq p hp
  · subst i; exact p73_points_nonneg q hq p hp
  · subst i; exact p74_points_nonneg q hq p hp
  · subst i; exact p75_points_nonneg q hq p hp
  · subst i; exact p76_points_nonneg q hq p hp
  · subst i; exact p77_points_nonneg q hq p hp
  · subst i; exact p78_points_nonneg q hq p hp
  · subst i; exact p79_points_nonneg q hq p hp
  · subst i; exact p80_points_nonneg q hq p hp
  · subst i; exact p81_points_nonneg q hq p hp
  · subst i; exact p82_points_nonneg q hq p hp
  · subst i; exact p83_points_nonneg q hq p hp
  · subst i; exact p84_points_nonneg q hq p hp
  · subst i; exact p85_points_nonneg q hq p hp
  · subst i; exact p86_points_nonneg q hq p hp
  · subst i; exact p87_points_nonneg q hq p hp
  · subst i; exact p88_points_nonneg q hq p hp
  · subst i; exact p89_points_nonneg q hq p hp
  · subst i; exact p90_points_nonneg q hq p hp
  · subst i; exact p91_points_nonneg q hq p hp
theorem piece_points_domain (q i : Nat) (hq : 4≤q) (hi : i∈positiveIds) (a b : Nat) : ((a:Int),(b:Int))∈piecePoints q i ↔ Domain q i a b := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 ∨ i=17 ∨ i=18 ∨ i=19 ∨ i=20 ∨ i=21 ∨ i=22 ∨ i=23 ∨ i=24 ∨ i=25 ∨ i=26 ∨ i=28 ∨ i=29 ∨ i=30 ∨ i=31 ∨ i=32 ∨ i=33 ∨ i=34 ∨ i=35 ∨ i=36 ∨ i=37 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=41 ∨ i=42 ∨ i=43 ∨ i=44 ∨ i=45 ∨ i=46 ∨ i=47 ∨ i=48 ∨ i=49 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=53 ∨ i=54 ∨ i=55 ∨ i=56 ∨ i=57 ∨ i=58 ∨ i=59 ∨ i=60 ∨ i=61 ∨ i=62 ∨ i=63 ∨ i=64 ∨ i=65 ∨ i=66 ∨ i=67 ∨ i=68 ∨ i=69 ∨ i=70 ∨ i=71 ∨ i=72 ∨ i=73 ∨ i=74 ∨ i=75 ∨ i=76 ∨ i=77 ∨ i=78 ∨ i=79 ∨ i=80 ∨ i=81 ∨ i=82 ∨ i=83 ∨ i=84 ∨ i=85 ∨ i=86 ∨ i=87 ∨ i=88 ∨ i=89 ∨ i=90 ∨ i=91 := by simpa [positiveIds] using hi
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst i; exact p0_points_domain q a b hq
  · subst i; exact p1_points_domain q a b hq
  · subst i; exact p2_points_domain q a b hq
  · subst i; exact p3_points_domain q a b hq
  · subst i; exact p4_points_domain q a b hq
  · subst i; exact p5_points_domain q a b hq
  · subst i; exact p6_points_domain q a b hq
  · subst i; exact p7_points_domain q a b hq
  · subst i; exact p8_points_domain q a b hq
  · subst i; exact p9_points_domain q a b hq
  · subst i; exact p10_points_domain q a b hq
  · subst i; exact p11_points_domain q a b hq
  · subst i; exact p12_points_domain q a b hq
  · subst i; exact p13_points_domain q a b hq
  · subst i; exact p14_points_domain q a b hq
  · subst i; exact p15_points_domain q a b hq
  · subst i; exact p17_points_domain q a b hq
  · subst i; exact p18_points_domain q a b hq
  · subst i; exact p19_points_domain q a b hq
  · subst i; exact p20_points_domain q a b hq
  · subst i; exact p21_points_domain q a b hq
  · subst i; exact p22_points_domain q a b hq
  · subst i; exact p23_points_domain q a b hq
  · subst i; exact p24_points_domain q a b hq
  · subst i; exact p25_points_domain q a b hq
  · subst i; exact p26_points_domain q a b hq
  · subst i; exact p28_points_domain q a b hq
  · subst i; exact p29_points_domain q a b hq
  · subst i; exact p30_points_domain q a b hq
  · subst i; exact p31_points_domain q a b hq
  · subst i; exact p32_points_domain q a b hq
  · subst i; exact p33_points_domain q a b hq
  · subst i; exact p34_points_domain q a b hq
  · subst i; exact p35_points_domain q a b hq
  · subst i; exact p36_points_domain q a b hq
  · subst i; exact p37_points_domain q a b hq
  · subst i; exact p38_points_domain q a b hq
  · subst i; exact p39_points_domain q a b hq
  · subst i; exact p40_points_domain q a b hq
  · subst i; exact p41_points_domain q a b hq
  · subst i; exact p42_points_domain q a b hq
  · subst i; exact p43_points_domain q a b hq
  · subst i; exact p44_points_domain q a b hq
  · subst i; exact p45_points_domain q a b hq
  · subst i; exact p46_points_domain q a b hq
  · subst i; exact p47_points_domain q a b hq
  · subst i; exact p48_points_domain q a b hq
  · subst i; exact p49_points_domain q a b hq
  · subst i; exact p50_points_domain q a b hq
  · subst i; exact p51_points_domain q a b hq
  · subst i; exact p52_points_domain q a b hq
  · subst i; exact p53_points_domain q a b hq
  · subst i; exact p54_points_domain q a b hq
  · subst i; exact p55_points_domain q a b hq
  · subst i; exact p56_points_domain q a b hq
  · subst i; exact p57_points_domain q a b hq
  · subst i; exact p58_points_domain q a b hq
  · subst i; exact p59_points_domain q a b hq
  · subst i; exact p60_points_domain q a b hq
  · subst i; exact p61_points_domain q a b hq
  · subst i; exact p62_points_domain q a b hq
  · subst i; exact p63_points_domain q a b hq
  · subst i; exact p64_points_domain q a b hq
  · subst i; exact p65_points_domain q a b hq
  · subst i; exact p66_points_domain q a b hq
  · subst i; exact p67_points_domain q a b hq
  · subst i; exact p68_points_domain q a b hq
  · subst i; exact p69_points_domain q a b hq
  · subst i; exact p70_points_domain q a b hq
  · subst i; exact p71_points_domain q a b hq
  · subst i; exact p72_points_domain q a b hq
  · subst i; exact p73_points_domain q a b hq
  · subst i; exact p74_points_domain q a b hq
  · subst i; exact p75_points_domain q a b hq
  · subst i; exact p76_points_domain q a b hq
  · subst i; exact p77_points_domain q a b hq
  · subst i; exact p78_points_domain q a b hq
  · subst i; exact p79_points_domain q a b hq
  · subst i; exact p80_points_domain q a b hq
  · subst i; exact p81_points_domain q a b hq
  · subst i; exact p82_points_domain q a b hq
  · subst i; exact p83_points_domain q a b hq
  · subst i; exact p84_points_domain q a b hq
  · subst i; exact p85_points_domain q a b hq
  · subst i; exact p86_points_domain q a b hq
  · subst i; exact p87_points_domain q a b hq
  · subst i; exact p88_points_domain q a b hq
  · subst i; exact p89_points_domain q a b hq
  · subst i; exact p90_points_domain q a b hq
  · subst i; exact p91_points_domain q a b hq
theorem piece_points_nodup (q i : Nat) : (piecePoints q i).Nodup := by
  unfold piecePoints
  split <;> first | exact orientedPoints_nodup _ _ _ _ _ _ | simp

theorem natPoints_mem (q i a b : Nat) (hq : 4≤q) (hi : i∈positiveIds) :
    (a,b)∈natPoints q i ↔ Domain q i a b := by
  constructor
  · intro h
    obtain ⟨p,hp,he⟩ := List.mem_map.mp h
    have hn := piece_points_nonneg q i hq hi p hp
    have he1 : p.1=(a:Int) := by have h := congrArg Prod.fst he; simp only [natPoint] at h; omega
    have he2 : p.2=(b:Int) := by have h := congrArg Prod.snd he; simp only [natPoint] at h; omega
    apply (piece_points_domain q i hq hi a b).mp
    have heq : p=((a:Int),(b:Int)) := Prod.ext he1 he2
    exact heq ▸ hp
  · intro h
    apply List.mem_map.mpr
    exact ⟨((a:Int),(b:Int)),(piece_points_domain q i hq hi a b).mpr h,by simp [natPoint]⟩

theorem natPoints_nodup (q i : Nat) (hq : 4≤q) (hi : i∈positiveIds) :
    (natPoints q i).Nodup := by
  apply nodup_map_on natPoint (piecePoints q i) (piece_points_nodup q i)
  intro p hp r hr he
  have hn := piece_points_nonneg q i hq hi p hp
  have hm := piece_points_nonneg q i hq hi r hr
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  simp only [natPoint] at h1 h2
  apply Prod.ext <;> omega
#print axioms piece_points_nonneg
#print axioms piece_points_domain
#print axioms natPoints_mem
#print axioms natPoints_nodup
end
end LuRazClosure.SourcePieces
