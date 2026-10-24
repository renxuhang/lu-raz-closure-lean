import ThreeRowCore234
import ThreeRowCore23Count

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def extra234List (q : Nat) : List NF23 :=
  ((enumP q (2*q-4)).map (fun t => NF23.lp t (2*q+1))) ++
  (((enumP q (2*q-4)).filter (fun t => decide (t≠q+3))).map NF23.creg)

theorem extra234_list_exact (q : Nat) (hq : 4≤q) (z : NF23) :
    z∈extra234List q ↔ Extra234 q z := by
  cases z <;> simp only [extra234List,List.mem_append,List.mem_map,Extra234]
  case lp t p =>
    constructor
    · rintro (⟨a,ha,he⟩ | ⟨a,_,he⟩)
      · have hh := NF23.lp.inj he
        have hp := (enumP_short_exact q hq a).mp ha
        exact ⟨by simpa only [hh.1] using hp.1,by omega,by omega⟩
      · cases he
    · rintro ⟨ht,htl,hp⟩
      exact Or.inl ⟨t,(enumP_short_exact q hq t).mpr ⟨ht,htl⟩,by rw [hp]⟩
  case creg t =>
    constructor
    · rintro (⟨a,_,he⟩ | ⟨a,ha,he⟩)
      · cases he
      · have hat := NF23.creg.inj he
        subst a
        have hf := List.mem_filter.mp ha
        have hp := (enumP_short_exact q hq t).mp hf.1
        exact ⟨hp.1,hp.2,of_decide_eq_true hf.2⟩
    · rintro ⟨ht,htl,hte⟩
      exact Or.inr ⟨t,List.mem_filter.mpr
        ⟨(enumP_short_exact q hq t).mpr ⟨ht,htl⟩,decide_eq_true hte⟩,rfl⟩
  all_goals simp

theorem extra234_list_nodup (q : Nat) : (extra234List q).Nodup := by
  rw [extra234List,List.nodup_append]
  refine ⟨?_,?_,?_⟩
  · exact nodup_map_injective (fun t => NF23.lp t (2*q+1)) (fun _ _ h => (NF23.lp.inj h).1)
      _ (enumP_nodup q (2*q-4))
  · apply nodup_map_injective NF23.creg (fun _ _ h => NF23.creg.inj h)
    exact List.Nodup.sublist List.filter_sublist (enumP_nodup q (2*q-4))
  · intro z hz w hw he
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hw
    cases he

theorem extra234_list_length (q : Nat) (hq : 4≤q) :
    ((extra234List q).length : Int)=4*(q:Int)-9 := by
  have hm := (enumP_short_exact q hq (q+3)).mpr (by unfold P; omega)
  have h := filter_ne_length (enumP q (2*q-4)) (enumP_nodup q (2*q-4)) (q+3) hm
  simp only [extra234List,List.length_append,List.length_map,Int.natCast_add]
  have hl : (enumP q (2*q-4)).length=2*q-4 := by simp [enumP]
  rw [hl] at h ⊢
  omega

theorem four_injective (q : Nat) (hq : 4≤q) (a b : NF23)
    (ha : Extra234 q a) (hb : Extra234 q b) (he : Four q a=Four q b) : a=b := by
  have hva := extra234_old_valid q hq a ha
  have hvb := extra234_old_valid q hq b hb
  have hca := NF23.core q hq a hva
  have hcb := NF23.core q hq b hvb
  apply NF23.unique q hq a b hva hvb
  intro e
  by_cases he4 : e=4
  · subst e
    exact iff_of_false hca.2.2.2 hcb.2.2.2
  · have h := Iff.of_eq (congrFun he e)
    simpa only [Four,he4,false_or] using h

def extra234Members (q : Nat) : List (Nat → Prop) := (extra234List q).map (Four q)

theorem extra234_members_nodup (q : Nat) (hq : 4≤q) : (extra234Members q).Nodup := by
  apply nodup_map_on _ _ (extra234_list_nodup q)
  intro a ha b hb he
  exact four_injective q hq a b ((extra234_list_exact q hq a).mp ha) ((extra234_list_exact q hq b).mp hb) he

def new234Members (q : Nat) : List (Nat → Prop) := core234Members q ++ extra234Members q

theorem new234_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈new234Members q ↔ Generated q R ∧ Core234 R := by
  rw [new234Members,List.mem_append,core234_members_exact q hq R,core234_exact q hq R]
  apply or_congr Iff.rfl
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := List.mem_map.mp h
    exact ⟨z,(extra234_list_exact q hq z).mp hz,fun e => Iff.of_eq (congrFun he.symm e)⟩
  · rintro ⟨z,hz,he⟩
    exact List.mem_map.mpr ⟨z,(extra234_list_exact q hq z).mpr hz,funext (fun e => propext (he e).symm)⟩

theorem new234_members_nodup (q : Nat) (hq : 4≤q) : (new234Members q).Nodup := by
  rw [new234Members,List.nodup_append]
  refine ⟨core234_members_nodup q hq,extra234_members_nodup q hq,?_⟩
  intro R hR T hT he
  have h := (core234_members_exact q hq R).mp hR
  have hm := old234_mid q hq R h.1 h.2
  obtain ⟨z,hz,hzT⟩ := List.mem_map.mp hT
  have hn := extra234_no_mid q hq z ((extra234_list_exact q hq z).mp hz)
  have hRT : R=Four q z := he.trans hzT.symm
  rw [hRT] at hm
  exact hn hm

theorem core234_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ Core234 R) ∧
      (l.length : Int)=10*(q:Int)-15 := by
  refine ⟨new234Members q,new234_members_nodup q hq,new234_members_exact q hq,?_⟩
  have h := extra234_list_length q hq
  have ho := LuRazClosure.core234_cardinality q hq
  have hlen : ((core234Members q).length : Int)=6*(q:Int)-6 := by
    simpa only [core234Members,List.length_map] using enum234_length q hq
  simp only [new234Members,List.length_append,Int.natCast_add,extra234Members,List.length_map]
  omega

end LuRazThreeRow
