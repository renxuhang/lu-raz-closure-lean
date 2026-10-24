import SixRowFullRetained

namespace LuRazSixRowClosure
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem full_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ CoreFull R ↔
    ∃ z : NFFull, FullKeep q z ∧ ∀ e, R e ↔ z.eval q e := by
  constructor
  · exact fun h => full_generated_normal q hq h.1 h.2
  · rintro ⟨z,hz,he⟩
    refine ⟨generated_congr q (full_retained_generated q hq z hz) (fun e => (he e).symm),?_⟩
    have hc := NFFull.core q hq z hz.1
    unfold CoreFull at *
    simpa only [he] using hc

theorem full_unique (q : Nat) (hq : 4≤q) (z w : NFFull)
    (hz : FullKeep q z) (hw : FullKeep q w)
    (he : ∀ e, z.eval q e ↔ w.eval q e) : z=w :=
  NFFull.unique q hq z w hz.1 hw.1 he

noncomputable def fullForms (q : Nat) : List NFFull := by
  classical
  exact (enumFull q).filter (fun z => decide (FullKeep q z))

theorem full_forms_exact (q : Nat) (hq : 4≤q) (z : NFFull) :
    z∈fullForms q ↔ FullKeep q z := by
  classical
  simp only [fullForms,List.mem_filter,decide_eq_true_eq,enumFull_exact q hq z]
  exact and_iff_right_of_imp (fun h => h.1)

theorem full_forms_nodup (q : Nat) : (fullForms q).Nodup := by
  classical
  exact List.Nodup.sublist List.filter_sublist (enumFull_nodup q)

noncomputable def fullMembers (q : Nat) : List (Nat → Prop) :=
  (fullForms q).map (NFFull.eval q)

theorem full_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈fullMembers q ↔ Generated q R ∧ CoreFull R := by
  rw [full_exact q hq R,fullMembers]
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := List.mem_map.mp h
    exact ⟨z,(full_forms_exact q hq z).mp hz,fun e => Iff.of_eq (congrFun he.symm e)⟩
  · rintro ⟨z,hz,he⟩
    exact List.mem_map.mpr ⟨z,(full_forms_exact q hq z).mpr hz,
      funext (fun e => propext (he e).symm)⟩

theorem full_members_nodup (q : Nat) (hq : 4≤q) : (fullMembers q).Nodup := by
  apply nodup_map_on _ _ (full_forms_nodup q)
  intro z hz w hw he
  exact full_unique q hq z w ((full_forms_exact q hq z).mp hz)
    ((full_forms_exact q hq w).mp hw) (fun e => Iff.of_eq (congrFun he e))

end LuRazSixRowClosure
