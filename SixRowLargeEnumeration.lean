import SixRow7Unique
namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
noncomputable def enum6 (q : Nat) : List NF6 := by
  classical
  let r := List.range (2*q+2)
  exact (((r.flatMap (fun t=>r.map (NF6.lp t))) ++ [NF6.filled,NF6.cex] ++
    r.map NF6.creg ++ r.map NF6.er).filter (fun z : NF6=>decide (z.Valid q))).eraseDups
noncomputable def enum7 (q : Nat) : List NF7 := by
  classical
  let r := List.range (4*q+1)
  exact (((enum123 q).map NF7.old ++ r.map NF7.creg ++ [NF7.cex,NF7.rex,NF7.point] ++
    r.map NF7.right).filter (fun z : NF7=>decide (z.Valid q))).eraseDups

theorem enum6_exact (q : Nat) (hq : 4≤q) (z : NF6) : z∈enum6 q ↔ z.Valid q := by
  classical
  simp only [enum6,List.mem_eraseDups,List.mem_filter,decide_eq_true_eq]
  constructor
  · exact fun h=>h.2
  · intro hz
    refine ⟨?_,hz⟩
    cases z <;> simp only [NF6.Valid,P] at hz <;>
      simp only [List.mem_append,List.mem_flatMap,List.mem_map,List.mem_range,List.mem_cons,List.not_mem_nil,or_false]
    · exact Or.inl (Or.inl (Or.inl ⟨_,by omega,_,by omega,rfl⟩))
    · exact Or.inl (Or.inl (Or.inr (Or.inl True.intro)))
    · exact Or.inl (Or.inr ⟨_,by omega,rfl⟩)
    · exact Or.inl (Or.inl (Or.inr (Or.inr True.intro)))
    · exact Or.inr ⟨_,by omega,rfl⟩

theorem enum7_exact (q : Nat) (hq : 4≤q) (z : NF7) : z∈enum7 q ↔ z.Valid q := by
  classical
  simp only [enum7,List.mem_eraseDups,List.mem_filter,decide_eq_true_eq]
  constructor
  · exact fun h=>h.2
  · intro hz
    refine ⟨?_,hz⟩
    cases z <;> simp only [NF7.Valid,P] at hz <;>
      simp only [List.mem_append,List.mem_flatMap,List.mem_map,List.mem_range,List.mem_cons,List.not_mem_nil,or_false]
    · exact Or.inl (Or.inl (Or.inl ⟨_,(enum123_exact q hq _).mpr hz.1,rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨_,by omega,rfl⟩))
    · exact Or.inl (Or.inr (Or.inl True.intro))
    · exact Or.inr ⟨_,by omega,rfl⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inl True.intro)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr True.intro)))

theorem large_erase_nodup {α : Type} [BEq α] [LawfulBEq α] (l : List α) : l.eraseDups.Nodup := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    refine ⟨?_,large_erase_nodup (l.filter (fun b=> !b == a))⟩
    intro h
    have hm := List.mem_eraseDups.mp h
    simp only [List.mem_filter] at hm
    simp at hm
termination_by l.length
decreasing_by
  have hh := List.length_filter_le (fun b=> !b == a) l
  simp only [List.length_cons]
  omega

theorem enum6_nodup (q : Nat) : (enum6 q).Nodup := by
  classical
  apply large_erase_nodup
theorem enum7_nodup (q : Nat) : (enum7 q).Nodup := by
  classical
  apply large_erase_nodup
noncomputable def members6 (q : Nat) := (enum6 q).map (NF6.eval q)
noncomputable def members7 (q : Nat) := (enum7 q).map (NF7.eval q)
theorem members6_nodup (q : Nat) (hq : 4≤q) : (members6 q).Nodup := by
  apply nodup_map_on _ _ (enum6_nodup q)
  intro z hz w hw he
  exact NF6.unique q hq z w ((enum6_exact q hq z).mp hz) ((enum6_exact q hq w).mp hw)
    (fun e=>iff_of_eq (congrFun he e))
theorem members7_nodup (q : Nat) (hq : 4≤q) : (members7 q).Nodup := by
  apply nodup_map_on _ _ (enum7_nodup q)
  intro z hz w hw he
  exact NF7.unique q hq z w ((enum7_exact q hq z).mp hz) ((enum7_exact q hq w).mp hw)
    (fun e=>iff_of_eq (congrFun he e))
theorem members6_exact (q : Nat) (hq : 4≤q) (R : Nat→Prop) :
    R∈members6 q ↔ Generated q R ∧ Core23 R := by
  rw [core6_exhaustive q hq R]
  constructor
  · rintro h
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
    exact ⟨z,(enum6_exact q hq z).mp hz,fun _=>Iff.rfl⟩
  · rintro ⟨z,hz,he⟩
    exact List.mem_map.mpr ⟨z,(enum6_exact q hq z).mpr hz,funext (fun e=>propext (he e).symm)⟩
theorem members7_exact (q : Nat) (hq : 4≤q) (R : Nat→Prop) :
    R∈members7 q ↔ Generated q R ∧ Core123 R := by
  rw [core7_exhaustive q hq R]
  constructor
  · rintro h
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
    exact ⟨z,(enum7_exact q hq z).mp hz,fun _=>Iff.rfl⟩
  · rintro ⟨z,hz,he⟩
    exact List.mem_map.mpr ⟨z,(enum7_exact q hq z).mpr hz,funext (fun e=>propext (he e).symm)⟩
end LuRazSixRowClosure
