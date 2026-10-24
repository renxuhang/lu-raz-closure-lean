import LatticeSourcePieces_0_24
import LatticeSourcePieces_24_47
import LatticeSourcePieces_47_71
import LatticeSourcePieces_71_92
namespace LuRazClosure
namespace SourcePieces
set_option maxRecDepth 32768
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
inductive Shape where
  | small (z : NFSmall)
  | c23 (z : NF23)
  | c123 (z : NF123)
  | c14 (z : NF14)
  | c24 (z : NF24)
  | c124 (z : NF124)
  | c134 (z : NF134)
  | c234 (z : NF234)
  | full (z : NFFull)
  deriving DecidableEq
def Shape.eval (q : Nat) : Shape → Nat → Prop
  | .small z => z.eval q
  | .c23 z => z.eval q
  | .c123 z => z.eval q
  | .c14 z => z.eval q
  | .c24 z => z.eval q
  | .c124 z => z.eval q
  | .c134 z => z.eval q
  | .c234 z => z.eval q
  | .full z => z.eval q
def Shape.Valid (q : Nat) : Shape → Prop
  | .small z => True
  | .c23 z => z.Valid q
  | .c123 z => z.Valid q
  | .c14 z => z.Valid q
  | .c24 z => True
  | .c124 z => z.Valid q
  | .c134 z => z.Valid q
  | .c234 z => z.Valid q
  | .full z => z.Valid q
def Shape.code : Shape → Nat
  | .small z => z.tag
  | .c23 z => 6
  | .c123 z => 7
  | .c14 z => 9
  | .c24 z => 10
  | .c124 z => 11
  | .c134 z => 13
  | .c234 z => 14
  | .full z => 15
def invNFSmall (q : Nat) : NFSmall → Nat×Nat×Nat
  | .bOnly => (0,0,0)
  | .aOnly => (1,0,0)
  | .ab => (2,0,0)
  | .dOnly => (3,0,0)
  | .ad => (4,0,0)
  | .cOnly => (5,0,0)
  | .cb => (6,0,0)
  | .eOnly => (7,0,0)
  | .ae => (8,0,0)
  | .ce => (9,0,0)
  | .ac => (10,0,0)
  | .acb => (11,0,0)
def invNF23 (q : Nat) : NF23 → Nat×Nat×Nat
  | .lp t p => if p≤q+1 then (if t≤q+1 then (12,p,t) else (13,p,t)) else (if t≤q+1 then (14,p,t) else (15,p,t))
  | .filledM => (17,0,0)
  | .dgap p => if p≤q+1 then (18,p,0) else (19,p,0)
  | .full => (20,0,0)
  | .creg t => if t≤q+1 then (21,t,0) else (22,t,0)
  | .cexception => (23,0,0)
def invNF123 (q : Nat) : NF123 → Nat×Nat×Nat
  | .low t => (24,t,0)
  | .high t p => if t≤q+1 then (25,p,t) else (26,p,t)
  | .filled => (28,0,0)
  | .dg p => if p=q+2 then (29,0,0) else (30,p,0)
  | .full => (31,0,0)
  | .creg t => if t≤q+1 then (32,t,0) else (33,t,0)
  | .cex => (34,0,0)
  | .er p => if p=q+2 then (37,0,0) else (if p≤q+1 then (35,p,0) else (36,p,0))
  | .ed p => (38,p,0)
def invNF14 (q : Nat) : NF14 → Nat×Nat×Nat
  | .base a b => if a≤q+3 then (39,a,b) else (40,a,b)
  | .agap a b => (41,a,b)
  | .bgap a b => if a≤q+3 then (42,a,b) else (43,a,b)
  | .joined a => (44,a,0)
  | .doubleGap => (45,0,0)
  | .ajoined a => (46,a,0)
def invNF24 (q : Nat) : NF24 → Nat×Nat×Nat
  | .k1 => (47,0,0)
  | .k2 => (48,0,0)
  | .joinK => (49,0,0)
  | .fill1 => (50,0,0)
  | .fill2 => (51,0,0)
  | .dBig => (52,0,0)
def invNF124 (q : Nat) : NF124 → Nat×Nat×Nat
  | .interval a k => (53,a,4*q-2+k)
  | .agap a k => (54,a,4*q-2+k)
  | .ak z => match z with | .k1 => (55,0,0) | .k2 => (56,0,0) | .joinK => (57,0,0) | .fill1 => (58,0,0) | .fill2 => (59,0,0) | .dBig => (0,0,0)
def invNF134 (q : Nat) : NF134 → Nat×Nat×Nat
  | .ej a => (60,a,0)
  | .aej a => (61,a,0)
  | .cj b => if b≤3*q-1 then (62,b,0) else (63,b,0)
  | .zj b => (64,b,0)
  | .czj b => (65,b,0)
  | .zjb b => (66,b,0)
  | .cjb b => (67,b,0)
  | .extra k => if k=0 then (68,0,0) else (if k=1 then (69,0,0) else (70,0,0))
def invNF234 (q : Nat) : NF234 → Nat×Nat×Nat
  | .kr p k => if p≤q+1 then (71,p,2*q+2+k) else (72,p,2*q+2+k)
  | .dg p => if p≤q+1 then (73,p,0) else (74,p,0)
  | .km k => (75,2*q+2+k,0)
  | .ck k => (76,4*q-2+k,0)
  | .last => (77,0,0)
def invNFFull (q : Nat) : NFFull → Nat×Nat×Nat
  | .noNInterval k => (78,4*q-2+k,0)
  | .noNMJRight b => (79,b,0)
  | .noNMJLeft a => (80,a,0)
  | .noNMK k => (81,2*q+2+k,0)
  | .noNCMJ b => (82,b,0)
  | .noH1Short p k => (83,p,2*q+2+k)
  | .noH1ZL a => (84,a,0)
  | .noH1Exception => (85,0,0)
  | .noH2 a => (86,a,0)
  | .noFive a => (87,a,0)
  | .leftGap p a => (88,p,a)
  | .full => (89,0,0)
  | .rightGap b c => (90,b,c)
  | .isolatedR b c => (91,b,c)
def identify (q : Nat) : Shape → Nat×Nat×Nat
  | .small z => invNFSmall q z
  | .c23 z => invNF23 q z
  | .c123 z => invNF123 q z
  | .c14 z => invNF14 q z
  | .c24 z => invNF24 q z
  | .c124 z => invNF124 q z
  | .c134 z => invNF134 q z
  | .c234 z => invNF234 q z
  | .full z => invNFFull q z
def positiveIds : List Nat := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,17,18,19,20,21,22,23,24,25,26,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91]
def Domain (q : Nat) : Nat → Nat → Nat → Prop
  | 0,a,b => p0Domain q a b
  | 1,a,b => p1Domain q a b
  | 2,a,b => p2Domain q a b
  | 3,a,b => p3Domain q a b
  | 4,a,b => p4Domain q a b
  | 5,a,b => p5Domain q a b
  | 6,a,b => p6Domain q a b
  | 7,a,b => p7Domain q a b
  | 8,a,b => p8Domain q a b
  | 9,a,b => p9Domain q a b
  | 10,a,b => p10Domain q a b
  | 11,a,b => p11Domain q a b
  | 12,a,b => p12Domain q a b
  | 13,a,b => p13Domain q a b
  | 14,a,b => p14Domain q a b
  | 15,a,b => p15Domain q a b
  | 17,a,b => p17Domain q a b
  | 18,a,b => p18Domain q a b
  | 19,a,b => p19Domain q a b
  | 20,a,b => p20Domain q a b
  | 21,a,b => p21Domain q a b
  | 22,a,b => p22Domain q a b
  | 23,a,b => p23Domain q a b
  | 24,a,b => p24Domain q a b
  | 25,a,b => p25Domain q a b
  | 26,a,b => p26Domain q a b
  | 28,a,b => p28Domain q a b
  | 29,a,b => p29Domain q a b
  | 30,a,b => p30Domain q a b
  | 31,a,b => p31Domain q a b
  | 32,a,b => p32Domain q a b
  | 33,a,b => p33Domain q a b
  | 34,a,b => p34Domain q a b
  | 35,a,b => p35Domain q a b
  | 36,a,b => p36Domain q a b
  | 37,a,b => p37Domain q a b
  | 38,a,b => p38Domain q a b
  | 39,a,b => p39Domain q a b
  | 40,a,b => p40Domain q a b
  | 41,a,b => p41Domain q a b
  | 42,a,b => p42Domain q a b
  | 43,a,b => p43Domain q a b
  | 44,a,b => p44Domain q a b
  | 45,a,b => p45Domain q a b
  | 46,a,b => p46Domain q a b
  | 47,a,b => p47Domain q a b
  | 48,a,b => p48Domain q a b
  | 49,a,b => p49Domain q a b
  | 50,a,b => p50Domain q a b
  | 51,a,b => p51Domain q a b
  | 52,a,b => p52Domain q a b
  | 53,a,b => p53Domain q a b
  | 54,a,b => p54Domain q a b
  | 55,a,b => p55Domain q a b
  | 56,a,b => p56Domain q a b
  | 57,a,b => p57Domain q a b
  | 58,a,b => p58Domain q a b
  | 59,a,b => p59Domain q a b
  | 60,a,b => p60Domain q a b
  | 61,a,b => p61Domain q a b
  | 62,a,b => p62Domain q a b
  | 63,a,b => p63Domain q a b
  | 64,a,b => p64Domain q a b
  | 65,a,b => p65Domain q a b
  | 66,a,b => p66Domain q a b
  | 67,a,b => p67Domain q a b
  | 68,a,b => p68Domain q a b
  | 69,a,b => p69Domain q a b
  | 70,a,b => p70Domain q a b
  | 71,a,b => p71Domain q a b
  | 72,a,b => p72Domain q a b
  | 73,a,b => p73Domain q a b
  | 74,a,b => p74Domain q a b
  | 75,a,b => p75Domain q a b
  | 76,a,b => p76Domain q a b
  | 77,a,b => p77Domain q a b
  | 78,a,b => p78Domain q a b
  | 79,a,b => p79Domain q a b
  | 80,a,b => p80Domain q a b
  | 81,a,b => p81Domain q a b
  | 82,a,b => p82Domain q a b
  | 83,a,b => p83Domain q a b
  | 84,a,b => p84Domain q a b
  | 85,a,b => p85Domain q a b
  | 86,a,b => p86Domain q a b
  | 87,a,b => p87Domain q a b
  | 88,a,b => p88Domain q a b
  | 89,a,b => p89Domain q a b
  | 90,a,b => p90Domain q a b
  | 91,a,b => p91Domain q a b
  | _,_,_ => False
def decode (q : Nat) : Nat → Nat → Nat → Shape
  | 0,a,b => .small (p0NF q a b)
  | 1,a,b => .small (p1NF q a b)
  | 2,a,b => .small (p2NF q a b)
  | 3,a,b => .small (p3NF q a b)
  | 4,a,b => .small (p4NF q a b)
  | 5,a,b => .small (p5NF q a b)
  | 6,a,b => .small (p6NF q a b)
  | 7,a,b => .small (p7NF q a b)
  | 8,a,b => .small (p8NF q a b)
  | 9,a,b => .small (p9NF q a b)
  | 10,a,b => .small (p10NF q a b)
  | 11,a,b => .small (p11NF q a b)
  | 12,a,b => .c23 (p12NF q a b)
  | 13,a,b => .c23 (p13NF q a b)
  | 14,a,b => .c23 (p14NF q a b)
  | 15,a,b => .c23 (p15NF q a b)
  | 17,a,b => .c23 (p17NF q a b)
  | 18,a,b => .c23 (p18NF q a b)
  | 19,a,b => .c23 (p19NF q a b)
  | 20,a,b => .c23 (p20NF q a b)
  | 21,a,b => .c23 (p21NF q a b)
  | 22,a,b => .c23 (p22NF q a b)
  | 23,a,b => .c23 (p23NF q a b)
  | 24,a,b => .c123 (p24NF q a b)
  | 25,a,b => .c123 (p25NF q a b)
  | 26,a,b => .c123 (p26NF q a b)
  | 28,a,b => .c123 (p28NF q a b)
  | 29,a,b => .c123 (p29NF q a b)
  | 30,a,b => .c123 (p30NF q a b)
  | 31,a,b => .c123 (p31NF q a b)
  | 32,a,b => .c123 (p32NF q a b)
  | 33,a,b => .c123 (p33NF q a b)
  | 34,a,b => .c123 (p34NF q a b)
  | 35,a,b => .c123 (p35NF q a b)
  | 36,a,b => .c123 (p36NF q a b)
  | 37,a,b => .c123 (p37NF q a b)
  | 38,a,b => .c123 (p38NF q a b)
  | 39,a,b => .c14 (p39NF q a b)
  | 40,a,b => .c14 (p40NF q a b)
  | 41,a,b => .c14 (p41NF q a b)
  | 42,a,b => .c14 (p42NF q a b)
  | 43,a,b => .c14 (p43NF q a b)
  | 44,a,b => .c14 (p44NF q a b)
  | 45,a,b => .c14 (p45NF q a b)
  | 46,a,b => .c14 (p46NF q a b)
  | 47,a,b => .c24 (p47NF q a b)
  | 48,a,b => .c24 (p48NF q a b)
  | 49,a,b => .c24 (p49NF q a b)
  | 50,a,b => .c24 (p50NF q a b)
  | 51,a,b => .c24 (p51NF q a b)
  | 52,a,b => .c24 (p52NF q a b)
  | 53,a,b => .c124 (p53NF q a b)
  | 54,a,b => .c124 (p54NF q a b)
  | 55,a,b => .c124 (p55NF q a b)
  | 56,a,b => .c124 (p56NF q a b)
  | 57,a,b => .c124 (p57NF q a b)
  | 58,a,b => .c124 (p58NF q a b)
  | 59,a,b => .c124 (p59NF q a b)
  | 60,a,b => .c134 (p60NF q a b)
  | 61,a,b => .c134 (p61NF q a b)
  | 62,a,b => .c134 (p62NF q a b)
  | 63,a,b => .c134 (p63NF q a b)
  | 64,a,b => .c134 (p64NF q a b)
  | 65,a,b => .c134 (p65NF q a b)
  | 66,a,b => .c134 (p66NF q a b)
  | 67,a,b => .c134 (p67NF q a b)
  | 68,a,b => .c134 (p68NF q a b)
  | 69,a,b => .c134 (p69NF q a b)
  | 70,a,b => .c134 (p70NF q a b)
  | 71,a,b => .c234 (p71NF q a b)
  | 72,a,b => .c234 (p72NF q a b)
  | 73,a,b => .c234 (p73NF q a b)
  | 74,a,b => .c234 (p74NF q a b)
  | 75,a,b => .c234 (p75NF q a b)
  | 76,a,b => .c234 (p76NF q a b)
  | 77,a,b => .c234 (p77NF q a b)
  | 78,a,b => .full (p78NF q a b)
  | 79,a,b => .full (p79NF q a b)
  | 80,a,b => .full (p80NF q a b)
  | 81,a,b => .full (p81NF q a b)
  | 82,a,b => .full (p82NF q a b)
  | 83,a,b => .full (p83NF q a b)
  | 84,a,b => .full (p84NF q a b)
  | 85,a,b => .full (p85NF q a b)
  | 86,a,b => .full (p86NF q a b)
  | 87,a,b => .full (p87NF q a b)
  | 88,a,b => .full (p88NF q a b)
  | 89,a,b => .full (p89NF q a b)
  | 90,a,b => .full (p90NF q a b)
  | 91,a,b => .full (p91NF q a b)
  | _,_,_ => .small .bOnly
def pieceSet (q : Nat) : Nat → Nat → Nat → Nat → Prop
  | 0,a,b => p0Set q a b
  | 1,a,b => p1Set q a b
  | 2,a,b => p2Set q a b
  | 3,a,b => p3Set q a b
  | 4,a,b => p4Set q a b
  | 5,a,b => p5Set q a b
  | 6,a,b => p6Set q a b
  | 7,a,b => p7Set q a b
  | 8,a,b => p8Set q a b
  | 9,a,b => p9Set q a b
  | 10,a,b => p10Set q a b
  | 11,a,b => p11Set q a b
  | 12,a,b => p12Set q a b
  | 13,a,b => p13Set q a b
  | 14,a,b => p14Set q a b
  | 15,a,b => p15Set q a b
  | 17,a,b => p17Set q a b
  | 18,a,b => p18Set q a b
  | 19,a,b => p19Set q a b
  | 20,a,b => p20Set q a b
  | 21,a,b => p21Set q a b
  | 22,a,b => p22Set q a b
  | 23,a,b => p23Set q a b
  | 24,a,b => p24Set q a b
  | 25,a,b => p25Set q a b
  | 26,a,b => p26Set q a b
  | 28,a,b => p28Set q a b
  | 29,a,b => p29Set q a b
  | 30,a,b => p30Set q a b
  | 31,a,b => p31Set q a b
  | 32,a,b => p32Set q a b
  | 33,a,b => p33Set q a b
  | 34,a,b => p34Set q a b
  | 35,a,b => p35Set q a b
  | 36,a,b => p36Set q a b
  | 37,a,b => p37Set q a b
  | 38,a,b => p38Set q a b
  | 39,a,b => p39Set q a b
  | 40,a,b => p40Set q a b
  | 41,a,b => p41Set q a b
  | 42,a,b => p42Set q a b
  | 43,a,b => p43Set q a b
  | 44,a,b => p44Set q a b
  | 45,a,b => p45Set q a b
  | 46,a,b => p46Set q a b
  | 47,a,b => p47Set q a b
  | 48,a,b => p48Set q a b
  | 49,a,b => p49Set q a b
  | 50,a,b => p50Set q a b
  | 51,a,b => p51Set q a b
  | 52,a,b => p52Set q a b
  | 53,a,b => p53Set q a b
  | 54,a,b => p54Set q a b
  | 55,a,b => p55Set q a b
  | 56,a,b => p56Set q a b
  | 57,a,b => p57Set q a b
  | 58,a,b => p58Set q a b
  | 59,a,b => p59Set q a b
  | 60,a,b => p60Set q a b
  | 61,a,b => p61Set q a b
  | 62,a,b => p62Set q a b
  | 63,a,b => p63Set q a b
  | 64,a,b => p64Set q a b
  | 65,a,b => p65Set q a b
  | 66,a,b => p66Set q a b
  | 67,a,b => p67Set q a b
  | 68,a,b => p68Set q a b
  | 69,a,b => p69Set q a b
  | 70,a,b => p70Set q a b
  | 71,a,b => p71Set q a b
  | 72,a,b => p72Set q a b
  | 73,a,b => p73Set q a b
  | 74,a,b => p74Set q a b
  | 75,a,b => p75Set q a b
  | 76,a,b => p76Set q a b
  | 77,a,b => p77Set q a b
  | 78,a,b => p78Set q a b
  | 79,a,b => p79Set q a b
  | 80,a,b => p80Set q a b
  | 81,a,b => p81Set q a b
  | 82,a,b => p82Set q a b
  | 83,a,b => p83Set q a b
  | 84,a,b => p84Set q a b
  | 85,a,b => p85Set q a b
  | 86,a,b => p86Set q a b
  | 87,a,b => p87Set q a b
  | 88,a,b => p88Set q a b
  | 89,a,b => p89Set q a b
  | 90,a,b => p90Set q a b
  | 91,a,b => p91Set q a b
  | _,_,_ => fun _ => False

end SourcePieces
end LuRazClosure
