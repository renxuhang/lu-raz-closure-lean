import VariantCoreFrequencyParts

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Transfer a disjoint exhaustive partition of canonical forms into a permutation. -/
theorem canonical_split_perm {α : Type} (old keep removed : List α)
    (Valid Cut : α → Prop) (hnold : old.Nodup) (hnkeep : keep.Nodup)
    (hnremoved : removed.Nodup)
    (ho : ∀ z, z∈old ↔ Valid z)
    (hk : ∀ z, z∈keep ↔ Valid z ∧ Cut z)
    (hr : ∀ z, z∈removed ↔ Valid z ∧ ¬Cut z) :
    (keep++removed).Perm old := by
  classical
  have hn : (keep++removed).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnkeep,hnremoved,?_⟩
    intro a ha b hb he
    subst b
    exact ((hr a).mp hb).2 ((hk a).mp ha).2
  apply (List.perm_ext_iff_of_nodup hn hnold).mpr
  intro z
  rw [List.mem_append,hk,hr,ho]
  by_cases h : Cut z <;> simp [h]

def removed23 (q : Nat) : List NF23 :=
  ((enumP q (2*q-3)).map (fun t => NF23.lp t (2*q+1))) ++ [.creg (2*q+1)]

theorem removed23_exact (q : Nat) (hq : 4≤q) (z : NF23) :
    z∈removed23 q ↔ z.Valid q ∧ ¬Avoid23 q z := by
  cases z <;> simp [removed23,List.mem_map,exists_fixed,enumP_exact q hq,NF23.Valid,Avoid23,P] <;> omega

theorem removed23_nodup (q : Nat) : (removed23 q).Nodup := by
  rw [removed23,List.nodup_append]
  refine ⟨nodup_map_injective (fun t => NF23.lp t (2*q+1))
    (fun _ _ h => (NF23.lp.inj h).1) _ (enumP_nodup q (2*q-3)),by simp,?_⟩
  intro z hz w hw he
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hz
  have hw' : w=NF23.creg (2*q+1) := by simpa using hw
  subst w
  cases hw'

theorem split23_perm (q : Nat) (hq : 4≤q) :
    (new23 q ++ removed23 q).Perm (enum23 q) :=
  canonical_split_perm _ _ _ (NF23.Valid q) (Avoid23 q)
    (enum23_nodup q) (new23_nodup q) (removed23_nodup q)
    (enum23_exact q hq) (new23_exact q hq) (removed23_exact q hq)

theorem split123_perm (q : Nat) (hq : 4≤q) :
    (keep123 q ++ removed123 q).Perm (enum123 q) :=
  canonical_split_perm _ _ _ (NF123.Valid q) (Cut123 q)
    (enum123_nodup q) (keep123_nodup q) (removed123_nodup q)
    (enum123_exact q hq) (keep123_exact q hq) (removed123_exact q hq)

theorem split_full_perm (q : Nat) (hq : 4≤q) :
    (keepFull q ++ lossList q).Perm (enumFull q) := by
  apply canonical_split_perm _ _ _ (NFFull.Valid q) (fun z => ¬LostFull q z)
    (enumFull_nodup q) (keep_full_nodup q) (loss_list_nodup q hq)
    (enumFull_exact q hq) (keep_full_exact q hq)
  intro z
  simpa using loss_list_exact q hq z

noncomputable def keep134 (q : Nat) : List NF134 := by
  classical
  exact (enum134 q).filter (fun z => decide (Cut134 z))

theorem keep134_exact (q : Nat) (hq : 4≤q) (z : NF134) :
    z∈keep134 q ↔ Valid134 q z := by
  classical
  simp only [keep134,List.mem_filter,decide_eq_true_eq,enum134_exact q hq z,Valid134]

theorem keep134_nodup (q : Nat) : (keep134 q).Nodup := by
  classical
  exact List.Nodup.sublist List.filter_sublist (enum134_nodup q)

def removed134Group (q : Nat) : Nat → List NF134
  | 0 => (List.range' 6 (2*q-4)).map NF134.ej
  | 1 => (List.range' (q+4) (q-2)).map NF134.aej
  | 2 => (List.range 3).map NF134.extra
  | _ => []

def removed134 (q : Nat) : List NF134 := (List.range 3).flatMap (removed134Group q)

def removed134Tag : NF134 → Nat
  | .ej _ => 0 | .aej _ => 1 | .extra _ => 2 | _ => 3

theorem removed134_group_exact (q : Nat) (hq : 4≤q) (k : Nat) (hk : k<3) (z : NF134) :
    z∈removed134Group q k ↔ z.Valid q ∧ ¬Cut134 z ∧ removed134Tag z=k := by
  have hc : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hc with rfl | rfl | rfl
  all_goals cases z <;> simp [removed134Group,List.mem_map,range_mem,NF134.Valid,Cut134,removed134Tag] <;> omega

theorem removed134_exact (q : Nat) (hq : 4≤q) (z : NF134) :
    z∈removed134 q ↔ z.Valid q ∧ ¬Cut134 z := by
  constructor
  · intro h
    obtain ⟨k,hk,hz⟩ := List.mem_flatMap.mp h
    have hh := (removed134_group_exact q hq k (List.mem_range.mp hk) z).mp hz
    exact ⟨hh.1,hh.2.1⟩
  · intro h
    have ht : removed134Tag z<3 := by cases z <;> simp_all [Cut134,removed134Tag]
    exact List.mem_flatMap.mpr ⟨removed134Tag z,List.mem_range.mpr ht,
      (removed134_group_exact q hq _ ht z).mpr ⟨h.1,h.2,rfl⟩⟩

theorem removed134_group_nodup (q k : Nat) (hk : k<3) : (removed134Group q k).Nodup := by
  have hc : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases hc with rfl | rfl | rfl
  · exact nodup_map_injective NF134.ej (fun _ _ h => NF134.ej.inj h) _ List.nodup_range'
  · exact nodup_map_injective NF134.aej (fun _ _ h => NF134.aej.inj h) _ List.nodup_range'
  · exact nodup_map_injective NF134.extra (fun _ _ h => NF134.extra.inj h) _ List.nodup_range

theorem removed134_nodup (q : Nat) (hq : 4≤q) : (removed134 q).Nodup := by
  apply nodup_flatMap_separated _ _ List.nodup_range
  · intro k hk
    exact removed134_group_nodup q k (List.mem_range.mp hk)
  · intro k hk j hj z hz w hw he
    have hzk := ((removed134_group_exact q hq k (List.mem_range.mp hk) z).mp hz).2.2
    have hwj := ((removed134_group_exact q hq j (List.mem_range.mp hj) w).mp hw).2.2
    subst w
    omega

theorem split134_perm (q : Nat) (hq : 4≤q) :
    (keep134 q ++ removed134 q).Perm (enum134 q) :=
  canonical_split_perm _ _ _ (NF134.Valid q) Cut134
    (enum134_nodup q) (keep134_nodup q) (removed134_nodup q hq)
    (enum134_exact q hq) (keep134_exact q hq) (removed134_exact q hq)

def fresh134List (q : Nat) : List Fresh134 :=
  [.lp,.lb] ++ ((List.range' (2*q+1) (2*q-3)).map Fresh134.zz) ++
  ((List.range' (2*q+2) (q-2)).map Fresh134.cz)

theorem fresh134_list_exact (q : Nat) (hq : 4≤q) (z : Fresh134) :
    z∈fresh134List q ↔ z.Valid q := by
  cases z <;> simp [fresh134List,List.mem_map,range_mem,Fresh134.Valid] <;> omega

theorem fresh134_list_nodup (q : Nat) : (fresh134List q).Nodup := by
  simp only [fresh134List,List.nodup_append]
  refine ⟨⟨by simp,?_,?_⟩,?_,?_⟩
  · exact nodup_map_injective Fresh134.zz (fun _ _ h => Fresh134.zz.inj h) _ List.nodup_range'
  · intro a ha b hb he
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl <;> cases he
  · exact nodup_map_injective Fresh134.cz (fun _ _ h => Fresh134.cz.inj h) _ List.nodup_range'
  · intro a ha b hb he
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hb
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl <;> cases he
    · obtain ⟨t,_,rfl⟩ := List.mem_map.mp ha
      cases he

theorem new134_split_perm (q : Nat) (hq : 4≤q) :
    (new134Members q).Perm
      ((keep134 q).map (NF134.eval q) ++ (fresh134List q).map (Fresh134.eval q)) := by
  apply (List.perm_ext_iff_of_nodup (new134_members_nodup q hq) ?_).mpr
  · intro R
    rw [new134_members_exact q hq R,core134_exhaustive q hq R,List.mem_append]
    constructor
    · rintro ⟨z,hz,he⟩
      cases z with
      | old z => exact Or.inl (List.mem_map.mpr ⟨z,(keep134_exact q hq z).mpr hz,
          funext (fun e => propext (he e).symm)⟩)
      | fresh z => exact Or.inr (List.mem_map.mpr ⟨z,(fresh134_list_exact q hq z).mpr hz,
          funext (fun e => propext (he e).symm)⟩)
    · rintro (h | h)
      · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
        exact ⟨.old z,(keep134_exact q hq z).mp hz,fun _ => Iff.rfl⟩
      · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp h
        exact ⟨.fresh z,(fresh134_list_exact q hq z).mp hz,fun _ => Iff.rfl⟩
  · rw [List.nodup_append]
    refine ⟨?_,?_,?_⟩
    · apply nodup_map_on _ _ (keep134_nodup q)
      intro a ha b hb he
      exact NF134.unique q hq a b ((keep134_exact q hq a).mp ha).1
        ((keep134_exact q hq b).mp hb).1 (fun e => Iff.of_eq (congrFun he e))
    · apply nodup_map_on _ _ (fresh134_list_nodup q)
      intro a ha b hb he
      exact fresh134_unique q hq a b ((fresh134_list_exact q hq a).mp ha)
        ((fresh134_list_exact q hq b).mp hb) (fun e => Iff.of_eq (congrFun he e))
    · intro R hR T hT he
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hR
      obtain ⟨w,hw,hwe⟩ := List.mem_map.mp hT
      exact fresh134_not_old q hq w ((fresh134_list_exact q hq w).mp hw)
        (LuRazClosure.generated_congr q (NF134.generated q hq z ((keep134_exact q hq z).mp hz).1)
          (fun e => Iff.of_eq (congrFun (he.trans hwe.symm) e)))

theorem count_delta23 (q e : Nat) (hq : 4≤q) :
    CountAt (new23Members q) e = CountAt (core23Members q) e -
      CountAt ((removed23 q).map (NF23.eval q)) e := by
  have h := count_at_perm _ _ ((split23_perm q hq).map (NF23.eval q)) e
  simp only [List.map_append,count_at_append] at h
  change CountAt (new23Members q) e + _ = CountAt (core23Members q) e at h
  omega

theorem count_delta123 (q e : Nat) (hq : 4≤q) :
    CountAt (new123Members q) e = CountAt (core123Members q) e -
      CountAt ((removed123 q).map (NF123.eval q)) e +
      CountAt (fresh123List.map (Fresh123.eval q)) e := by
  have h := count_at_perm _ _ ((split123_perm q hq).map (NF123.eval q)) e
  simp only [List.map_append,count_at_append] at h
  simp only [new123Members,count_at_append]
  change _ + _ = CountAt (core123Members q) e at h
  omega

theorem count_delta134 (q e : Nat) (hq : 4≤q) :
    CountAt (new134Members q) e = CountAt (core134Members q) e -
      CountAt ((removed134 q).map (NF134.eval q)) e +
      CountAt ((fresh134List q).map (Fresh134.eval q)) e := by
  have h := count_at_perm _ _ ((split134_perm q hq).map (NF134.eval q)) e
  have hn := count_at_perm _ _ (new134_split_perm q hq) e
  simp only [List.map_append,count_at_append] at h hn
  change _ + _ = CountAt (core134Members q) e at h
  omega

theorem count_delta_full (q e : Nat) (hq : 4≤q) :
    CountAt (newFullMembers q) e = CountAt (fullMembers q) e -
      CountAt ((lossList q).map (NFFull.eval q)) e + CountAt (addFullMembers q) e := by
  have h := count_at_perm _ _ ((split_full_perm q hq).map (NFFull.eval q)) e
  simp only [List.map_append,count_at_append] at h
  simp only [newFullMembers,count_at_append]
  change _ + _ = CountAt (fullMembers q) e at h
  omega

end LuRazThreeRow


