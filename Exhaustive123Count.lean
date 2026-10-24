import Exhaustive123Exact

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def removed123 (q : Nat) : List NF123 :=
  ((enumP q (2*q-3)).map (fun t => NF123.high t (2*q+1))) ++
  [.creg (2*q+1),.er (2*q+1)]

theorem removed123_exact (q : Nat) (hq : 4≤q) (z : NF123) :
    z∈removed123 q ↔ z.Valid q ∧ ¬Cut123 q z := by
  cases z <;> simp [removed123,List.mem_map,exists_fixed,enumP_exact q hq,NF123.Valid,Cut123,P] <;> omega

theorem removed123_nodup (q : Nat) : (removed123 q).Nodup := by
  rw [removed123,List.nodup_append]
  refine ⟨nodup_map_injective (fun t => NF123.high t (2*q+1))
    (fun _ _ h => (NF123.high.inj h).1) _ (enumP_nodup q (2*q-3)),by simp,?_⟩
  intro z hz w hw he
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl <;> cases he

noncomputable def keep123 (q : Nat) : List NF123 := by
  classical
  exact (enum123 q).filter (fun z => decide (Cut123 q z))

theorem keep123_exact (q : Nat) (hq : 4≤q) (z : NF123) : z∈keep123 q ↔ Valid123 q z := by
  classical
  simp only [keep123,List.mem_filter,decide_eq_true_eq,enum123_exact q hq z,Valid123]

theorem keep123_nodup (q : Nat) : (keep123 q).Nodup := by
  classical
  exact List.Nodup.sublist List.filter_sublist (enum123_nodup q)

theorem keep123_length (q : Nat) (hq : 4≤q) :
    2*((keep123 q).length : Int)=3*(q:Int)*(q:Int)+3*(q:Int)-12 := by
  classical
  have hn : (keep123 q ++ removed123 q).Nodup := by
    rw [List.nodup_append]
    refine ⟨keep123_nodup q,removed123_nodup q,?_⟩
    intro a ha b hb he
    subst b
    exact ((removed123_exact q hq a).mp hb).2 ((keep123_exact q hq a).mp ha).2
  have hp : (keep123 q ++ removed123 q).Perm (enum123 q) := by
    apply (List.perm_ext_iff_of_nodup hn (enum123_nodup q)).mpr
    intro z
    rw [List.mem_append,keep123_exact q hq z,removed123_exact q hq z,enum123_exact q hq z]
    unfold Valid123
    by_cases hc : Cut123 q z <;> simp [hc]
  have hl := hp.length_eq
  have hr : (removed123 q).length=2*q-1 := by simp [removed123,enumP]; omega
  rw [List.length_append,hr] at hl
  have ho := enum123_length q hq
  omega

def fresh123List : List Fresh123 := [.e,.ae,.ce]
noncomputable def new123Members (q : Nat) : List (Nat → Prop) :=
  ((keep123 q).map (NF123.eval q)) ++ (fresh123List.map (Fresh123.eval q))

theorem fresh123_mem (z : Fresh123) : z∈fresh123List := by cases z <;> simp [fresh123List]

theorem new123_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈new123Members q ↔ Generated q R ∧ Core123 R := by
  rw [core123_exhaustive q hq R,new123Members,List.mem_append]
  constructor
  · rintro (h | h)
    · obtain ⟨z,hz,he⟩ := List.mem_map.mp h
      exact Or.inl ⟨z,(keep123_exact q hq z).mp hz,fun e => Iff.of_eq (congrFun he.symm e)⟩
    · obtain ⟨z,_,he⟩ := List.mem_map.mp h
      exact Or.inr ⟨z,fun e => Iff.of_eq (congrFun he.symm e)⟩
  · rintro (⟨z,hz,he⟩ | ⟨z,he⟩)
    · exact Or.inl (List.mem_map.mpr ⟨z,(keep123_exact q hq z).mpr hz,funext (fun e => propext (he e).symm)⟩)
    · exact Or.inr (List.mem_map.mpr ⟨z,fresh123_mem z,funext (fun e => propext (he e).symm)⟩)

theorem new123_members_nodup (q : Nat) (hq : 4≤q) : (new123Members q).Nodup := by
  rw [new123Members,List.nodup_append]
  refine ⟨?_,?_,?_⟩
  · apply nodup_map_on _ _ (keep123_nodup q)
    intro a ha b hb he
    exact NF123.unique q hq a b ((keep123_exact q hq a).mp ha).1 ((keep123_exact q hq b).mp hb).1
      (fun e => Iff.of_eq (congrFun he e))
  · apply nodup_map_on _ _ (by decide : fresh123List.Nodup)
    intro a _ b _ he
    exact fresh123_unique q hq a b (fun e => Iff.of_eq (congrFun he e))
  · intro R hR T hT he
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hR
    obtain ⟨w,_,hw⟩ := List.mem_map.mp hT
    exact retained_fresh123_disjoint q hq z ((keep123_exact q hq z).mp hz) w
      (fun e => Iff.of_eq (congrFun (he.trans hw.symm) e))

theorem core123_new_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ Core123 R) ∧
      2*(l.length : Int)=3*(q:Int)*(q:Int)+3*(q:Int)-6 := by
  refine ⟨new123Members q,new123_members_nodup q hq,new123_members_exact q hq,?_⟩
  have h := keep123_length q hq
  simp only [new123Members,List.length_append,List.length_map,Int.natCast_add]
  have hf : fresh123List.length=3 := rfl
  rw [hf]
  omega

end LuRazThreeRow
