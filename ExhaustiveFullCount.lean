import ExhaustiveFullExact

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

noncomputable def keepFull (q : Nat) : List NFFull := by
  classical
  exact (enumFull q).filter (fun z => decide (¬LostFull q z))

theorem keep_full_exact (q : Nat) (hq : 4≤q) (z : NFFull) :
    z∈keepFull q ↔ z.Valid q ∧ ¬LostFull q z := by
  classical
  simp only [keepFull,List.mem_filter,decide_eq_true_eq,enumFull_exact q hq z]

theorem keep_full_nodup (q : Nat) : (keepFull q).Nodup := by
  classical
  exact List.Nodup.sublist List.filter_sublist (enumFull_nodup q)

theorem keep_full_length (q : Nat) (hq : 4≤q) :
    ((keepFull q).length : Int)=5*(q:Int)*(q:Int)-10*(q:Int)+9 := by
  classical
  have hn : (keepFull q ++ lossList q).Nodup := by
    rw [List.nodup_append]
    refine ⟨keep_full_nodup q,loss_list_nodup q hq,?_⟩
    intro a ha b hb he
    subst b
    exact ((keep_full_exact q hq a).mp ha).2 ((loss_list_exact q hq a).mp hb).2
  have hp : (keepFull q ++ lossList q).Perm (enumFull q) := by
    apply (List.perm_ext_iff_of_nodup hn (enumFull_nodup q)).mpr
    intro z
    rw [List.mem_append,keep_full_exact q hq z,loss_list_exact q hq z,enumFull_exact q hq z]
    by_cases hl : LostFull q z <;> simp [hl]
  have hl := hp.length_eq
  rw [List.length_append] at hl
  have ho := enumFull_length q hq
  have hdel := loss_list_length q hq
  omega

noncomputable def newFullMembers (q : Nat) : List (Nat → Prop) :=
  ((keepFull q).map (NFFull.eval q)) ++ addFullMembers q

theorem new_full_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈newFullMembers q ↔ Generated q R ∧ CoreFull R := by
  rw [full_new_exhaustive q hq R,newFullMembers,List.mem_append]
  constructor
  · rintro (h | h)
    · obtain ⟨z,hz,he⟩ := List.mem_map.mp h
      exact ⟨.old z,(keep_full_exact q hq z).mp hz,fun e => Iff.of_eq (congrFun he.symm e)⟩
    · obtain ⟨z,hz,he⟩ := List.mem_map.mp h
      exact ⟨.fresh z,(add_full_list_exact q hq z).mp hz,fun e => Iff.of_eq (congrFun he.symm e)⟩
  · rintro ⟨z,hz,he⟩
    cases z with
    | old z => exact Or.inl (List.mem_map.mpr ⟨z,(keep_full_exact q hq z).mpr hz,
        funext (fun e => propext (he e).symm)⟩)
    | fresh z => exact Or.inr (List.mem_map.mpr ⟨z,(add_full_list_exact q hq z).mpr hz,
        funext (fun e => propext (he e).symm)⟩)

theorem new_full_members_nodup (q : Nat) (hq : 4≤q) : (newFullMembers q).Nodup := by
  rw [newFullMembers,List.nodup_append]
  refine ⟨?_,add_full_members_nodup q hq,?_⟩
  · apply nodup_map_on _ _ (keep_full_nodup q)
    intro a ha b hb he
    exact NFFull.unique q hq a b ((keep_full_exact q hq a).mp ha).1 ((keep_full_exact q hq b).mp hb).1
      (fun e => Iff.of_eq (congrFun he e))
  · intro R hR T hT he
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hR
    obtain ⟨w,hw,hwe⟩ := List.mem_map.mp hT
    exact add_full_not_old q hq w ((add_full_list_exact q hq w).mp hw)
      (LuRazClosure.generated_congr q (NFFull.generated q hq z ((keep_full_exact q hq z).mp hz).1)
        (fun e => Iff.of_eq (congrFun (he.trans hwe.symm) e)))

theorem full_new_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ CoreFull R) ∧
      (l.length : Int)=5*(q:Int)*(q:Int)-7*(q:Int)+6 := by
  refine ⟨newFullMembers q,new_full_members_nodup q hq,new_full_members_exact q hq,?_⟩
  have h := keep_full_length q hq
  have ha := add_full_list_length q hq
  simp only [newFullMembers,List.length_append,List.length_map,Int.natCast_add,addFullMembers,List.length_map]
  omega

end LuRazThreeRow
