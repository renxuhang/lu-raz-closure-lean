import VariantGlobalDifference
import VariantTailCountTools

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration LuRazLattice LuRazCounting
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Common tail family after replacing the punctured rank index by its interval endpoint. -/
def BetaLine (q k a e : Nat) : Prop := I 5 k e ∨ I a (4*q) e

def BetaCLine (q a e : Nat) : Prop := I 5 (2*q+2) e ∨ e=3*q+1 ∨ I a (4*q) e

theorem removed23_count_reparameterized (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    CountAt ((removed23 q).map (NF23.eval q)) e =
      CountAt ((List.range' (2*q+4) (2*q-3)).map (BetaLine q (2*q+1))) e +
      mark (I 5 (2*q+2) e ∨ e=3*q+1 ∨ e=4*q) := by
  have hl := count_beta_line q (2*q-3)
    (fun a => NF23.eval q (.lp a (2*q+1))) (BetaLine q (2*q+1)) e hq (by
      intro a _
      simp only [NF23.eval,LRow,LNormal,BetaLine,I]
      split <;> omega)
  have hp : NF23.eval q (.creg (2*q+1)) e ↔
      I 5 (2*q+2) e ∨ e=3*q+1 ∨ e=4*q := by
    simp only [NF23.eval,I,beta]
    split <;> omega
  have hc := count_at_singleton (NF23.eval q (.creg (2*q+1))) e
  rw [removed23,List.map_append,count_at_append,List.map_map,List.map_cons,List.map_nil]
  change CountAt ((enumP q (2*q-3)).map (fun a => NF23.eval q (.lp a (2*q+1)))) e + _ = _
  rw [hl,hc]
  congr 1
  exact congrArg mark (propext hp)

theorem removed123_count_reparameterized (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    CountAt ((removed123 q).map (NF123.eval q)) e =
      CountAt ((List.range' (2*q+4) (2*q-3)).map (BetaLine q (2*q+1))) e +
      mark (I 5 (2*q+2) e ∨ e=3*q+1 ∨ e=4*q) +
      mark (I 5 (2*q+1) e ∨ I (2*q+3) (4*q) e) := by
  have hl := count_beta_line q (2*q-3)
    (fun a => NF123.eval q (.high a (2*q+1))) (BetaLine q (2*q+1)) e hq (by
      intro a _
      simp only [NF123.eval,NF123.body,LRow,LNormal,BetaLine,I]
      split <;> omega)
  have hp : NF123.eval q (.creg (2*q+1)) e ↔
      I 5 (2*q+2) e ∨ e=3*q+1 ∨ e=4*q := by
    simp only [NF123.eval,NF123.body,NF23.eval,I,beta]
    split <;> omega
  have hp2 : NF123.eval q (.er (2*q+1)) e ↔
      I 5 (2*q+1) e ∨ I (2*q+3) (4*q) e := by
    simp only [NF123.eval,NF123.body,TwoPiece,I]
    omega
  simp only [removed123,List.map_append,count_at_append,List.map_map,List.map_cons,List.map_nil,
    count_at_cons,count_at_singleton]
  change CountAt ((enumP q (2*q-3)).map (fun a => NF123.eval q (.high a (2*q+1)))) e + _ = _
  rw [hl]
  rw [propext hp,propext hp2]
  have hempty : CountAt [] e=0 := by simp [CountAt]
  rw [hempty]
  omega

theorem extra234_count_reparameterized (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    CountAt (extra234Members q) e =
      CountAt ((List.range' (2*q+4) (2*q-4)).map (BetaLine q (2*q+1))) e +
      CountAt ((List.range' (2*q+4) (2*q-4)).map (BetaCLine q)) e -
      mark (I 5 (2*q+2) e ∨ I (3*q+1) (4*q) e) := by
  have hl := count_beta_line q (2*q-4)
    (fun a => Four q (.lp a (2*q+1))) (BetaLine q (2*q+1)) e hq (by
      intro a _
      simp only [Four,NF23.eval,LRow,LNormal,BetaLine,I]
      split <;> omega)
  have hc := count_beta_line q (2*q-4)
    (fun a => Four q (.creg a)) (BetaCLine q) e hq (by
      intro a _
      simp only [Four,NF23.eval,BetaCLine,I]
      omega)
  have hx : q+3∈enumP q (2*q-4) :=
    (enumP_short_exact q hq (q+3)).mpr (by unfold P; omega)
  have hr := count_remove_index (enumP q (2*q-4)) (fun a => Four q (.creg a)) e (q+3)
    (enumP_nodup q (2*q-4)) hx
  have hp : Four q (.creg (q+3)) e ↔ I 5 (2*q+2) e ∨ I (3*q+1) (4*q) e := by
    simp only [Four,NF23.eval,I,beta]
    split <;> omega
  simp only [extra234Members,extra234List,List.map_append,List.map_map,count_at_append]
  change CountAt ((enumP q (2*q-4)).map (fun a => Four q (.lp a (2*q+1)))) e +
    CountAt (((enumP q (2*q-4)).filter (fun t => decide (t≠q+3))).map (fun a => Four q (.creg a))) e = _
  rw [hl,hr,hc,propext hp]
  omega


attribute [local instance] Classical.propDecidable

theorem beta_line_tail_count (q n k e : Nat) (hq : 4≤q) :
    CountAt ((List.range' (2*q+4) n).map (BetaLine q k)) e =
      tailLower (2*(q:Int)+4) (2*(q:Int)+(n:Int)+3) (4*(q:Int)) (e:Int)
        (5≤(e:Int) ∧ (e:Int)≤(k:Int)) := by
  have h := count_lower (2*q+4) n (BetaLine q k) e
    (5≤(e:Int) ∧ (e:Int)≤(k:Int)) (4*(q:Int)) (by
      intro a _
      unfold BetaLine I
      omega)
  have hs : ((2*q+4:Nat):Int)=2*(q:Int)+4 := by omega
  have ht : ((2*q+4:Nat):Int)+(n:Int)-1=2*(q:Int)+(n:Int)+3 := by omega
  rw [ht,hs] at h
  by_cases hp : 5≤(e:Int) ∧ (e:Int)≤(k:Int) <;>
    simp only [tailLower,hp,ite_true,ite_false] at h ⊢ <;> exact h

theorem beta_c_line_tail_count (q n e : Nat) (hq : 4≤q) :
    CountAt ((List.range' (2*q+4) n).map (BetaCLine q)) e =
      tailLower (2*(q:Int)+4) (2*(q:Int)+(n:Int)+3) (4*(q:Int)) (e:Int)
        ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+2) ∨ (e:Int)=3*(q:Int)+1) := by
  have h := count_lower (2*q+4) n (BetaCLine q) e
    ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+2) ∨ (e:Int)=3*(q:Int)+1) (4*(q:Int)) (by
      intro a _
      unfold BetaCLine I
      omega)
  have hs : ((2*q+4:Nat):Int)=2*(q:Int)+4 := by omega
  have ht : ((2*q+4:Nat):Int)+(n:Int)-1=2*(q:Int)+(n:Int)+3 := by omega
  rw [ht,hs] at h
  by_cases hp : (5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+2) ∨ (e:Int)=3*(q:Int)+1 <;>
    simp only [tailLower,hp,ite_true,ite_false] at h ⊢ <;> exact h

theorem removed23_tail_eq (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    CountAt ((removed23 q).map (NF23.eval q)) e =
      (removedTailGroups (q:Int) (e:Int)).getD 1 0 +
      (removedTailGroups (q:Int) (e:Int)).getD 2 0 := by
  rw [removed23_count_reparameterized q e hq he,beta_line_tail_count q (2*q-3) (2*q+1) e hq]
  have hk : ((2*q+1:Nat):Int)=2*(q:Int)+1 := by omega
  have ht : 2*(q:Int)+((2*q-3:Nat):Int)+3=4*(q:Int) := by omega
  rw [hk,ht]
  have hm := tail_mark_eq (I 5 (2*q+2) e ∨ e=3*q+1 ∨ e=4*q)
    ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+2) ∨ (e:Int)=3*(q:Int)+1 ∨ (e:Int)=4*(q:Int)) (by
      unfold I
      omega)
  rw [hm]
  simp only [removedTailGroups,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  by_cases hp : 5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1 <;>
    by_cases hp2 : (5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+2) ∨ (e:Int)=3*(q:Int)+1 ∨ (e:Int)=4*(q:Int) <;>
    simp [tailLower,tailMark,hp,hp2]

theorem removed123_tail_eq (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    CountAt ((removed123 q).map (NF123.eval q)) e =
      (removedTailGroups (q:Int) (e:Int)).getD 3 0 +
      (removedTailGroups (q:Int) (e:Int)).getD 4 0 := by
  rw [removed123_count_reparameterized q e hq he,beta_line_tail_count q (2*q-3) (2*q+1) e hq]
  have hk : ((2*q+1:Nat):Int)=2*(q:Int)+1 := by omega
  have ht : 2*(q:Int)+((2*q-3:Nat):Int)+3=4*(q:Int) := by omega
  rw [hk,ht]
  have hm := tail_mark_eq (I 5 (2*q+2) e ∨ e=3*q+1 ∨ e=4*q)
    ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+2) ∨ (e:Int)=3*(q:Int)+1 ∨ (e:Int)=4*(q:Int)) (by
      unfold I
      omega)
  have hm2 := tail_mark_eq (I 5 (2*q+1) e ∨ I (2*q+3) (4*q) e)
    ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (2*(q:Int)+3≤(e:Int) ∧ (e:Int)≤4*(q:Int))) (by
      unfold I
      omega)
  rw [hm,hm2]
  simp only [removedTailGroups,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  by_cases hp : 5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1 <;>
    by_cases hp2 : (5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+2) ∨ (e:Int)=3*(q:Int)+1 ∨ (e:Int)=4*(q:Int) <;>
    by_cases hp3 : (5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (2*(q:Int)+3≤(e:Int) ∧ (e:Int)≤4*(q:Int)) <;>
    simp [tailLower,tailMark,hp,hp2,hp3] <;> omega

theorem extra234_tail_eq (q e : Nat) (hq : 4≤q) (he : 5≤e) :
    CountAt (extra234Members q) e =
      (addedTailGroups (q:Int) (e:Int)).getD 6 0 +
      (addedTailGroups (q:Int) (e:Int)).getD 7 0 := by
  rw [extra234_count_reparameterized q e hq he,beta_line_tail_count q (2*q-4) (2*q+1) e hq,
    beta_c_line_tail_count q (2*q-4) e hq]
  have hk : ((2*q+1:Nat):Int)=2*(q:Int)+1 := by omega
  have ht : 2*(q:Int)+((2*q-4:Nat):Int)+3=4*(q:Int)-1 := by omega
  rw [hk,ht]
  have hm := tail_mark_eq (I 5 (2*q+2) e ∨ I (3*q+1) (4*q) e)
    ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+2) ∨ (3*(q:Int)+1≤(e:Int) ∧ (e:Int)≤4*(q:Int))) (by
      unfold I
      omega)
  rw [hm]
  simp only [addedTailGroups,List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  by_cases hp : 5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1 <;>
    by_cases hp2 : (5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+2) ∨ (e:Int)=3*(q:Int)+1 <;>
    by_cases hp3 : (5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+2) ∨ (3*(q:Int)+1≤(e:Int) ∧ (e:Int)≤4*(q:Int)) <;>
    simp [tailLower,tailMark,hp,hp2,hp3] <;> omega

end LuRazThreeRow
