import VariantGlobalDifference
import VariantTailCountTools

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration LuRazCounting LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable
noncomputable section

theorem fixed_tail_mark (P Q : Prop) [Decidable Q] (h : P↔Q) :
    mark P=tailMark Q := by
  rw [mark_congr h]
  unfold mark tailMark
  by_cases hq : Q <;> simp [hq]

theorem count_three_tail (a b c : Nat → Prop) (e : Nat) (P Q R : Prop)
    [Decidable P] [Decidable Q] [Decidable R]
    (ha : a e↔P) (hb : b e↔Q) (hc : c e↔R) :
    CountAt [a,b,c] e=tailMark P+tailMark Q+tailMark R := by
  rw [count_at_cons,count_at_cons,count_at_singleton,
    fixed_tail_mark _ _ ha,fixed_tail_mark _ _ hb,fixed_tail_mark _ _ hc]
  omega

theorem count_four_tail (a b c d : Nat → Prop) (e : Nat) (P Q R S : Prop)
    [Decidable P] [Decidable Q] [Decidable R] [Decidable S]
    (ha : a e↔P) (hb : b e↔Q) (hc : c e↔R) (hd : d e↔S) :
    CountAt [a,b,c,d] e=tailMark P+tailMark Q+tailMark R+tailMark S := by
  rw [count_at_cons,count_at_cons,count_at_cons,count_at_singleton,
    fixed_tail_mark _ _ ha,fixed_tail_mark _ _ hb,fixed_tail_mark _ _ hc,fixed_tail_mark _ _ hd]
  omega

theorem removed5_tail_count (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt (removed5Members q) e=(removedTailGroups (q:Int) (e:Int)).getD 0 0 := by
  change CountAt [NFSmall.eval q .eOnly,NFSmall.eval q .ae,NFSmall.eval q .ce] e=
    tailMark (2*(q:Int)+3≤(e:Int) ∧ (e:Int)≤4*(q:Int)) +
      tailMark ((5≤(e:Int) ∧ (e:Int)≤(q:Int)+2) ∨
        (2*(q:Int)+3≤(e:Int) ∧ (e:Int)≤4*(q:Int))) +
      tailMark (5≤(e:Int) ∧ (e:Int)≤4*(q:Int))
  apply count_three_tail
  · unfold NFSmall.eval ERow I
    omega
  · unfold NFSmall.eval ARow ERow I
    omega
  · unfold NFSmall.eval CRow ERow I
    omega

theorem added5_tail_count (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt (added5Members q) e=(addedTailGroups (q:Int) (e:Int)).getD 0 0 := by
  change CountAt [NF5.eval q .z,NF5.eval q .zb,NF5.eval q .zc] e=
    tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨
      (4*(q:Int)-1≤(e:Int) ∧ (e:Int)≤4*(q:Int))) +
      tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨
        (3*(q:Int)+2≤(e:Int) ∧ (e:Int)≤4*(q:Int))) +
      tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+2) ∨ (e:Int)=3*(q:Int)+1 ∨
        (4*(q:Int)-1≤(e:Int) ∧ (e:Int)≤4*(q:Int)))
  apply count_three_tail
  · unfold NF5.eval ZPrime I
    omega
  · unfold NF5.eval ZPrime BRow I
    omega
  · unfold NF5.eval ZPrime CRow I
    omega

theorem fresh123_tail_count (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt (fresh123List.map (Fresh123.eval q)) e=
      (addedTailGroups (q:Int) (e:Int)).getD 1 0 := by
  change CountAt [Fresh123.eval q .e,Fresh123.eval q .ae,Fresh123.eval q .ce] e=
    tailMark ((2*(q:Int)+3≤(e:Int) ∧ (e:Int)≤4*(q:Int)-2) ∨ (e:Int)=4*(q:Int)) +
      tailMark ((5≤(e:Int) ∧ (e:Int)≤(q:Int)+2) ∨
        (2*(q:Int)+3≤(e:Int) ∧ (e:Int)≤4*(q:Int)-2) ∨ (e:Int)=4*(q:Int)) +
      tailMark ((5≤(e:Int) ∧ (e:Int)≤4*(q:Int)-2) ∨ (e:Int)=4*(q:Int))
  apply count_three_tail
  · unfold Fresh123.eval EPrime I
    omega
  · unfold Fresh123.eval EPrime ARow I
    omega
  · unfold Fresh123.eval EPrime CRow I
    omega

theorem members12_tail_count (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt (members12 q) e=(addedTailGroups (q:Int) (e:Int)).getD 2 0 := by
  change CountAt [eval12 q (false,false),eval12 q (false,true),
    eval12 q (true,false),eval12 q (true,true)] e=
    tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (e:Int)=4*(q:Int)) +
      tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨
        (3*(q:Int)+2≤(e:Int) ∧ (e:Int)≤4*(q:Int))) +
      tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+2) ∨
        (e:Int)=3*(q:Int)+1 ∨ (e:Int)=4*(q:Int)) +
      tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+2) ∨
        (3*(q:Int)+1≤(e:Int) ∧ (e:Int)≤4*(q:Int)))
  apply count_four_tail
  all_goals
    simp [eval12,Mix12,LPrime,CRow,BRow,I] <;> omega

#print axioms removed5_tail_count
#print axioms added5_tail_count
#print axioms fresh123_tail_count
#print axioms members12_tail_count
end
end LuRazThreeRow
