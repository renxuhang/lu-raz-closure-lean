import VariantDifferenceBridge
import LatticeSourceTally

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def removed5Members (q : Nat) : List (Nat → Prop) :=
  [NFSmall.eOnly,NFSmall.ae,NFSmall.ce].map (NFSmall.eval q)

def added5Members (q : Nat) : List (Nat → Prop) :=
  [NF5.z,NF5.zb,NF5.zc].map (NF5.eval q)

def common5Members (q : Nat) : List (Nat → Prop) :=
  [NFSmall.ac,NFSmall.acb].map (NFSmall.eval q)

theorem split5_old (q : Nat) : smallMembers q 5 = removed5Members q ++ common5Members q := by
  rfl

theorem split5_new (q : Nat) : members5 q = added5Members q ++ common5Members q := by
  rfl

theorem count_delta5 (q e : Nat) :
    CountAt (members5 q) e = CountAt (smallMembers q 5) e -
      CountAt (removed5Members q) e + CountAt (added5Members q) e := by
  rw [split5_old,split5_new,count_at_append,count_at_append]
  omega

theorem count_delta234 (q e : Nat) :
    CountAt (new234Members q) e = CountAt (core234Members q) e +
      CountAt (extra234Members q) e := by
  exact count_at_append _ _ e

/-- The explicit small deleted families; all unaffected canonical forms cancel. -/
noncomputable def VariantRemovedMembers (q : Nat) : List (Nat → Prop) :=
  removed5Members q ++ ((removed23 q).map (NF23.eval q)) ++
  ((removed123 q).map (NF123.eval q)) ++ ((removed134 q).map (NF134.eval q)) ++ lossMembers q

/-- The explicit small added families; all unaffected canonical forms cancel. -/
def VariantAddedMembers (q : Nat) : List (Nat → Prop) :=
  added5Members q ++ (fresh123List.map (Fresh123.eval q)) ++ members12 q ++
  ((fresh134List q).map (Fresh134.eval q)) ++ extra234Members q ++ addFullMembers q

noncomputable def DeltaRaw (q e : Nat) : Int :=
  CountAt (VariantAddedMembers q) e - CountAt (VariantRemovedMembers q) e

noncomputable def OldChangedMembers (q : Nat) : List (Nat → Prop) :=
  smallMembers q 5 ++ core23Members q ++ core123Members q ++ [] ++
  core134Members q ++ core234Members q ++ fullMembers q

noncomputable def NewChangedMembers (q : Nat) : List (Nat → Prop) :=
  members5 q ++ new23Members q ++ new123Members q ++ members12 q ++
  new134Members q ++ new234Members q ++ newFullMembers q

theorem old_changed_members_enumeration (q : Nat) (hq : 4≤q) :
    (OldChangedMembers q).Nodup ∧
    (∀ R,R∈OldChangedMembers q ↔ LuRazClosure.Generated q R ∧ Changed R) := by
  have hs : ∀ R,R∈smallMembers q 5 ↔ LuRazClosure.Generated q R ∧ Core5 R := by
    intro R
    simpa [CoreSmallAt,Core5] using small_members_exact q 5 hq R
  have he : ∀ R,R∈([] : List (Nat → Prop)) ↔ LuRazClosure.Generated q R ∧ Core12 R := by
    intro R
    simp [old_core12_empty q hq R]
  exact seven_enumerations (LuRazClosure.Generated q)
    (smallMembers q 5) (small_members_nodup q 5 hq) hs
    (core23Members q) (core23_members_nodup q hq) (core23_members_exact q hq)
    (core123Members q) (core123_members_nodup q hq) (core123_members_exact q hq)
    [] List.nodup_nil he
    (core134Members q) (core134_members_nodup q hq) (core134_members_exact q hq)
    (core234Members q) (core234_members_nodup q hq) (core234_members_exact q hq)
    (fullMembers q) (full_members_nodup q hq) (full_members_exact q hq)

theorem new_changed_members_enumeration (q : Nat) (hq : 4≤q) :
    (NewChangedMembers q).Nodup ∧
    (∀ R,R∈NewChangedMembers q ↔ Generated q R ∧ Changed R) := by
  exact seven_enumerations (Generated q)
    (members5 q) (members5_nodup q hq) (members5_exact q hq)
    (new23Members q) (new23_members_nodup q hq) (new23_members_exact q hq)
    (new123Members q) (new123_members_nodup q hq) (new123_members_exact q hq)
    (members12 q) (members12_nodup q hq) (members12_exact q hq)
    (new134Members q) (new134_members_nodup q hq) (new134_members_exact q hq)
    (new234Members q) (new234_members_nodup q hq) (new234_members_exact q hq)
    (newFullMembers q) (new_full_members_nodup q hq) (new_full_members_exact q hq)

theorem changed_count_delta (q e : Nat) (hq : 4≤q) :
    CountAt (NewChangedMembers q) e = CountAt (OldChangedMembers q) e + DeltaRaw q e := by
  have h5 := count_delta5 q e
  have h6 := count_delta23 q e hq
  have h7 := count_delta123 q e hq
  have h13 := count_delta134 q e hq
  have h14 := count_delta234 q e
  have h15 := count_delta_full q e hq
  simp only [NewChangedMembers,OldChangedMembers,DeltaRaw,VariantAddedMembers,
    VariantRemovedMembers,count_at_append]
  have hempty : CountAt [] e=0 := by simp [CountAt]
  rw [hempty]
  change _ = _ + (_ - (_ + _ + _ + _ + CountAt ((lossList q).map (NFFull.eval q)) e))
  omega

noncomputable def UnchangedMembers (q : Nat) : List (Nat → Prop) := by
  classical
  exact (closureMembers q).filter (fun R => decide (¬Changed R))

noncomputable def VariantClosureMembers (q : Nat) : List (Nat → Prop) :=
  UnchangedMembers q ++ NewChangedMembers q

theorem unchanged_members_old (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈UnchangedMembers q ↔ LuRazClosure.Generated q R ∧ ¬Changed R := by
  classical
  simp only [UnchangedMembers,List.mem_filter,decide_eq_true_eq,closure_members_exact q hq R]

theorem unchanged_members_new (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈UnchangedMembers q ↔ Generated q R ∧ ¬Changed R := by
  rw [unchanged_members_old q hq R]
  classical
  by_cases hc : Changed R
  · simp [hc]
  · rw [unchanged_outside_changed q hq R hc]

theorem unchanged_members_nodup (q : Nat) (hq : 4≤q) : (UnchangedMembers q).Nodup := by
  classical
  exact List.Nodup.sublist List.filter_sublist (closure_members_nodup q hq)

theorem old_global_split_perm (q : Nat) (hq : 4≤q) :
    (UnchangedMembers q ++ OldChangedMembers q).Perm (closureMembers q) := by
  have h := append_enumerations (LuRazClosure.Generated q) (fun R => ¬Changed R) Changed
    (UnchangedMembers q) (OldChangedMembers q)
    (unchanged_members_nodup q hq) (old_changed_members_enumeration q hq).1
    (unchanged_members_old q hq) (old_changed_members_enumeration q hq).2
    (fun R h h' => h h')
  apply (List.perm_ext_iff_of_nodup h.1 (closure_members_nodup q hq)).mpr
  intro R
  rw [h.2 R,closure_members_exact q hq R]
  classical
  by_cases hc : Changed R <;> simp [hc]

theorem variant_closure_members_nodup (q : Nat) (hq : 4≤q) :
    (VariantClosureMembers q).Nodup := by
  exact (append_enumerations (Generated q) (fun R => ¬Changed R) Changed
    (UnchangedMembers q) (NewChangedMembers q)
    (unchanged_members_nodup q hq) (new_changed_members_enumeration q hq).1
    (unchanged_members_new q hq) (new_changed_members_enumeration q hq).2
    (fun R h h' => h h')).1

theorem variant_closure_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈VariantClosureMembers q ↔ Generated q R := by
  rw [VariantClosureMembers,List.mem_append,unchanged_members_new q hq R,
    (new_changed_members_enumeration q hq).2 R]
  classical
  by_cases hc : Changed R <;> simp [hc]

theorem variant_closure_count_delta (q e : Nat) (hq : 4≤q) :
    CountAt (VariantClosureMembers q) e =
      SourcePieces.elementFrequency q e + DeltaRaw q e := by
  have ho := count_at_perm _ _ (old_global_split_perm q hq) e
  rw [count_at_append] at ho
  have hd := changed_count_delta q e hq
  change CountAt (UnchangedMembers q ++ NewChangedMembers q) e = _
  rw [count_at_append]
  have hs : SourcePieces.elementFrequency q e=CountAt (closureMembers q) e := rfl
  rw [hs]
  omega

/-- A single duplicate-free enumeration gives every coordinate frequency simultaneously. -/
theorem variant_global_frequency_bridge (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧ (∀ R,R∈l ↔ Generated q R) ∧
      (∀ e,CountAt l e = SourcePieces.elementFrequency q e + DeltaRaw q e) :=
  ⟨VariantClosureMembers q,variant_closure_members_nodup q hq,
    variant_closure_members_exact q hq,fun e => variant_closure_count_delta q e hq⟩

end LuRazThreeRow
