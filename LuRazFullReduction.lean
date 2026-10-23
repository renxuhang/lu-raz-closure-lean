import LuRazNonFullResults
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

theorem nonTop_one_excludes_two (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2) (hn : i≠0)
    (h1 : LuRazParametric.Row q i 1) : ¬LuRazParametric.Row q i 2 := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
      (5≤i ∧ i≤q+2) ∨ (q+3≤i ∧ i≤2*q) ∨ i=2*q+1 ∨ i=2*q+2 ∨ i=2*q+3 ∨
      (2*q+4≤i ∧ i≤3*q) ∨ i=3*q+1 ∨ (3*q+2≤i ∧ i+1≤4*q) ∨
      i=4*q ∨ i=4*q+1 ∨ i=4*q+2 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact False.elim (hn h)
  · intro h2
    have hh1 := (LuRazParametric.row_case_1 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_1 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_2 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_2 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_3 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_3 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_4 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_4 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_5 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_5 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_6 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_6 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_7 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_7 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_8 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_8 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_9 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_9 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_10 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_10 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_11 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_11 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_12 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_12 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_13 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_13 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_14 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_14 q i 2 (by omega) h).mp h2
    omega
  · intro h2
    have hh1 := (LuRazParametric.row_case_15 q i 1 (by omega) h).mp h1
    have hh2 := (LuRazParametric.row_case_15 q i 2 (by omega) h).mp h2
    omega

theorem full_closure_split (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : CoreFull R) :
    (∀ e, R e ↔ 1≤e ∧ e≤4*q) ∨
    ∃ U V : Nat → Prop, Generated q U ∧ Generated q V ∧
      ¬U 1 ∧ U 2 ∧ V 1 ∧ ¬V 2 ∧ ∀ e, R e ↔ U e ∨ V e := by
  classical
  have hs := generated_supported q hq R hg
  obtain ⟨l,_,hv,he⟩ := hg
  by_cases h0 : 0∈l
  · left
    intro e
    constructor
    · exact hs e
    · intro hb
      exact (he e).mp ⟨0,h0,(LuRazParametric.row_case_0 q 0 e (by omega) rfl).mpr hb⟩
  · let lu := l.filter (fun i => decide (¬LuRazParametric.Row q i 1))
    let lv := l.filter (fun i => decide (LuRazParametric.Row q i 1))
    let U := ListUnion (LuRazParametric.Row q) lu
    let V := ListUnion (LuRazParametric.Row q) lv
    have hu1 : ¬U 1 := by
      rintro ⟨i,hi,hi1⟩
      have hf := List.mem_filter.mp hi
      exact (of_decide_eq_true hf.2) hi1
    have hv2 : ¬V 2 := by
      rintro ⟨i,hi,hi2⟩
      have hf := List.mem_filter.mp hi
      exact nonTop_one_excludes_two q i hq (hv i hf.1) (fun h => h0 (h ▸ hf.1)) (of_decide_eq_true hf.2) hi2
    have hu2 : U 2 := by
      obtain ⟨i,hi,hi2⟩ := (he 2).mpr hc.2.1
      have hn1 : ¬LuRazParametric.Row q i 1 := by
        intro hi1
        exact nonTop_one_excludes_two q i hq (hv i hi) (fun h => h0 (h ▸ hi)) hi1 hi2
      exact ⟨i,List.mem_filter.mpr ⟨hi,decide_eq_true hn1⟩,hi2⟩
    have hv1 : V 1 := by
      obtain ⟨i,hi,hi1⟩ := (he 1).mpr hc.1
      exact ⟨i,List.mem_filter.mpr ⟨hi,decide_eq_true hi1⟩,hi1⟩
    have hgu : Generated q U := by
      refine ⟨lu,?_,?_,fun _ => Iff.rfl⟩
      · intro hnil
        obtain ⟨i,hi,_⟩ := hu2
        rw [hnil] at hi
        exact List.not_mem_nil hi
      · intro i hi
        exact hv i (List.mem_filter.mp hi).1
    have hgv : Generated q V := by
      refine ⟨lv,?_,?_,fun _ => Iff.rfl⟩
      · intro hnil
        obtain ⟨i,hi,_⟩ := hv1
        rw [hnil] at hi
        exact List.not_mem_nil hi
      · intro i hi
        exact hv i (List.mem_filter.mp hi).1
    refine Or.inr ⟨U,V,hgu,hgv,hu1,hu2,hv1,hv2,?_⟩
    intro e
    constructor
    · intro hr
      obtain ⟨i,hi,hie⟩ := (he e).mpr hr
      by_cases hi1 : LuRazParametric.Row q i 1
      · exact Or.inr ⟨i,List.mem_filter.mpr ⟨hi,decide_eq_true hi1⟩,hie⟩
      · exact Or.inl ⟨i,List.mem_filter.mpr ⟨hi,decide_eq_true hi1⟩,hie⟩
    · rintro (⟨i,hi,hie⟩ | ⟨i,hi,hie⟩)
      · exact (he e).mp ⟨i,(List.mem_filter.mp hi).1,hie⟩
      · exact (he e).mp ⟨i,(List.mem_filter.mp hi).1,hie⟩

theorem full_closure_split_enumerated (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : CoreFull R) :
    (∀ e, R e ↔ 1≤e ∧ e≤4*q) ∨
    ∃ U∈partialMembers q, ∃ V∈partialMembers q,
      ¬U 1 ∧ U 2 ∧ V 1 ∧ ¬V 2 ∧ ∀ e, R e ↔ U e ∨ V e := by
  rcases full_closure_split q hq R hg hc with h | ⟨U,V,hU,hV,hu1,hu2,hv1,hv2,he⟩
  · exact Or.inl h
  · refine Or.inr ⟨U,?_,V,?_,hu1,hu2,hv1,hv2,he⟩
    · exact (partialMembers_exact q hq U).mpr ⟨hU,fun hh => hu1 hh.1⟩
    · exact (partialMembers_exact q hq V).mpr ⟨hV,fun hh => hv2 hh.2.1⟩

def fullPairCodes : List (Nat × Nat) :=
  [(2,13),(6,9),(6,13),(10,5),(10,13),
   (14,1),(14,5),(14,9),(14,13)]

theorem full_pair_code (U V : Nat → Prop) (hu1 : ¬U 1) (hu2 : U 2)
    (hv1 : V 1) (hv2 : ¬V 2) (h3 : U 3 ∨ V 3) (h4 : U 4 ∨ V 4) :
    (coreCode U,coreCode V)∈fullPairCodes := by
  classical
  by_cases hu3 : U 3 <;> by_cases hu4 : U 4 <;>
    by_cases hv3 : V 3 <;> by_cases hv4 : V 4 <;>
    simp_all [coreCode,fullPairCodes]

theorem full_closure_nine_cases (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : CoreFull R) :
    (∀ e, R e ↔ 1≤e ∧ e≤4*q) ∨
    ∃ U∈partialMembers q, ∃ V∈partialMembers q,
      (coreCode U,coreCode V)∈fullPairCodes ∧ ∀ e, R e ↔ U e ∨ V e := by
  rcases full_closure_split_enumerated q hq R hg hc with h | ⟨U,hU,V,hV,hu1,hu2,hv1,hv2,he⟩
  · exact Or.inl h
  · exact Or.inr ⟨U,hU,V,hV,full_pair_code U V hu1 hu2 hv1 hv2 ((he 3).mp hc.2.2.1) ((he 4).mp hc.2.2.2),he⟩
end LuRazClosure

