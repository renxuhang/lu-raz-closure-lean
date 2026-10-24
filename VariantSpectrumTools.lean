import VariantCoreFrequency
import LuRazCompleteSpectrum
import LatticeTallyTools

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration LuRazCounting LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
noncomputable section

theorem count_at_congr {α : Type} (l : List α) (f g : α → Nat → Prop) (e : Nat)
    (h : ∀ a∈l, f a e ↔ g a e) : CountAt (l.map f) e=CountAt (l.map g) e := by
  change tally (l.map f) (fun R => R e)=tally (l.map g) (fun R => R e)
  rw [tally_map,tally_map]
  exact tally_congr l _ _ h

theorem count_at_singleton (R : Nat → Prop) (e : Nat) : CountAt [R] e=mark (R e) := by
  classical
  by_cases h : R e <;> simp [CountAt,mark,h]

theorem count_at_cons (R : Nat → Prop) (l : List (Nat → Prop)) (e : Nat) :
    CountAt (R::l) e=mark (R e)+CountAt l e := by
  have h := count_at_append [R] l e
  simpa only [List.singleton_append,count_at_singleton] using h

def lineTally (s n : Nat) (P G : Prop) (lo hi : Int) : Int :=
  by
    classical
    exact if P then (n:Int) else if G then max 0 (min ((s:Int)+(n:Int)-1) hi-max (s:Int) lo+1) else 0

theorem count_line (s n : Nat) (f : Nat → Nat → Prop) (e : Nat) (P G : Prop) (lo hi : Int)
    (h : ∀ a∈List.range' s n, f a e ↔ P ∨ (G ∧ lo≤(a:Int) ∧ (a:Int)≤hi)) :
    CountAt ((List.range' s n).map f) e=lineTally s n P G lo hi := by
  classical
  change tally ((List.range' s n).map f) (fun R => R e)=_
  rw [tally_map]
  have ht := tally_congr (List.range' s n) (fun a => f a e)
    (fun a => P ∨ (G ∧ lo≤(a:Int) ∧ (a:Int)≤hi)) h
  rw [ht]
  by_cases hp : P
  · have ht' := tally_congr (List.range' s n)
      (fun a => P ∨ (G ∧ lo≤(a:Int) ∧ (a:Int)≤hi)) (fun _ => True)
      (by intro a _; simp [hp])
    rw [ht',tally_true,List.length_range']
    simp [lineTally,hp]
  · by_cases hg : G
    · have ht' := tally_congr (List.range' s n)
        (fun a => P ∨ (G ∧ lo≤(a:Int) ∧ (a:Int)≤hi))
        (fun a => lo≤(a:Int) ∧ (a:Int)≤hi) (by intro a _; simp [hp,hg])
      rw [ht']
      have hcount := count_shifted_interval (s:Int) lo hi n
      rw [tally_eq_filter,List.range'_eq_map_range]
      simp only [List.filter_map,List.length_map,Function.comp_def,Int.natCast_add]
      rw [hcount]
      simp only [lineTally,hp,hg,ite_false,ite_true,intervalCount]
      omega
    · have ht' := tally_congr (List.range' s n)
        (fun a => P ∨ (G ∧ lo≤(a:Int) ∧ (a:Int)≤hi)) (fun _ => False)
        (by intro a _; simp [hp,hg])
      rw [ht',tally_false]
      simp [lineTally,hp,hg]

theorem beta_rank (q k : Nat) (hq : 4≤q) : beta q (rankP q k)=2*q+4+k := by
  unfold beta rankP
  repeat first | omega | split

theorem map_beta_enum (q n : Nat) (hq : 4≤q) :
    (enumP q n).map (beta q)=List.range' (2*q+4) n := by
  unfold enumP
  rw [List.map_map,List.range'_eq_map_range]
  apply List.map_congr_left
  intro k _
  exact beta_rank q k hq

theorem beta_inj_valid (q a b : Nat) (ha : P q a) (hb : P q b)
    (he : beta q a=beta q b) : a=b := by
  unfold P at ha hb
  unfold beta at he
  repeat first | omega | split at he

theorem map_beta_enum_filter (q n t : Nat) (hq : 4≤q)
    (hn : n≤2*q-3) (ht : P q t) :
    ((enumP q n).filter (fun a => decide (a≠t))).map (beta q)=
      (List.range' (2*q+4) n).filter (fun a => decide (a≠beta q t)) := by
  classical
  rw [←map_beta_enum q n hq,List.filter_map]
  congr 1
  apply List.filter_congr
  intro a ha
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  have hv := rankP_valid q k hq (by have := List.mem_range.mp hk; omega)
  have he : (rankP q k≠t) ↔ (beta q (rankP q k)≠beta q t) := by
    constructor
    · intro h he
      exact h (beta_inj_valid q _ _ hv ht he)
    · intro h he
      exact h (congrArg (beta q) he)
  simp only [Function.comp_def]
  by_cases ha : rankP q k=t
  · simp [ha]
  · have hb := he.mp ha
    simp [ha,hb]

theorem count_beta_line (q n : Nat) (f g : Nat → Nat → Prop) (e : Nat) (hq : 4≤q)
    (h : ∀ a∈enumP q n, f a e ↔ g (beta q a) e) :
    CountAt ((enumP q n).map f) e=CountAt ((List.range' (2*q+4) n).map g) e := by
  rw [count_at_congr (enumP q n) f (fun a => g (beta q a)) e h]
  have hm : (enumP q n).map (fun a => g (beta q a))=(List.range' (2*q+4) n).map g := by
    rw [←map_beta_enum q n hq,List.map_map]
    rfl
  rw [hm]

theorem count_remove_index (l : List Nat) (f : Nat → Nat → Prop) (e x : Nat)
    (hn : l.Nodup) (hx : x∈l) :
    CountAt ((l.filter (fun a => decide (a≠x))).map f) e=
      CountAt (l.map f) e-mark (f x e) := by
  classical
  have hfn : (l.filter (fun a => decide (a≠x))).Nodup :=
    List.Nodup.sublist List.filter_sublist hn
  have hpn : ((l.filter (fun a => decide (a≠x)))++[x]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hfn,by simp,?_⟩
    intro a ha b hb he
    have hb' : b=x := by simpa using hb
    have hne := of_decide_eq_true (List.mem_filter.mp ha).2
    exact hne (he.trans hb')
  have hp : ((l.filter (fun a => decide (a≠x)))++[x]).Perm l := by
    apply (List.perm_ext_iff_of_nodup hpn hn).mpr
    intro a
    simp only [List.mem_append,List.mem_filter,decide_eq_true_eq,List.mem_singleton]
    by_cases he : a=x
    · subst a; simp [hx]
    · simp [he]
  have h := count_at_perm _ _ (hp.map f) e
  simp only [List.map_append,List.map_cons,List.map_nil,count_at_append,count_at_singleton] at h
  omega

end
end LuRazThreeRow
