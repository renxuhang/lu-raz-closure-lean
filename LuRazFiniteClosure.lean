import LuRazCore14Results
import LuRazCore23Results

namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def Supported (q : Nat) (R : Nat → Prop) : Prop := ∀ e, R e → 1≤e ∧ e≤4*q
def Restrict (q : Nat) (R : Nat → Prop) (e : Fin (4*q)) : Prop := R (e.val+1)
def Lift (q : Nat) (T : Fin (4*q) → Prop) (e : Nat) : Prop :=
  ∃ h : 1≤e ∧ e≤4*q, T ⟨e-1,by omega⟩

/-- Ordinary nonempty predicate unions of the actual Fin-indexed source family S. -/
def FinGenerated (q : Nat) (T : Fin (4*q) → Prop) : Prop :=
  ∃ l : List (Fin (4*q+3)), l≠[] ∧
    ∀ e, (∃ i, i∈l ∧ LuRazParametric.S q i e) ↔ T e

theorem row_supported (q i e : Nat) (hq : 4≤q) (h : LuRazParametric.Row q i e) :
    1≤e ∧ e≤4*q := by
  unfold LuRazParametric.Row at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

theorem generated_supported (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hg : Generated q R) : Supported q R := by
  obtain ⟨l,_,_,heq⟩ := hg
  intro e he
  obtain ⟨i,_,hi⟩ := (heq e).mpr he
  exact row_supported q i e hq hi

theorem lift_supported (q : Nat) (T : Fin (4*q) → Prop) : Supported q (Lift q T) := by
  rintro e ⟨h,_⟩
  exact h

theorem restrict_lift (q : Nat) (T : Fin (4*q) → Prop) : Restrict q (Lift q T)=T := by
  funext e
  apply propext
  have heq : (⟨e.val+1-1,by omega⟩ : Fin (4*q))=e := by apply Fin.ext; simp only [Fin.val_mk]; omega
  constructor
  · rintro ⟨_,h⟩
    simpa only [heq] using h
  · intro h
    refine ⟨by omega,?_⟩
    simpa only [heq] using h

theorem lift_restrict (q : Nat) (R : Nat → Prop) (hs : Supported q R) : Lift q (Restrict q R)=R := by
  funext e
  apply propext
  constructor
  · rintro ⟨h,he⟩
    change R (e-1+1) at he
    have hn : e-1+1=e := by omega
    simpa only [hn] using he
  · intro he
    have h := hs e he
    refine ⟨h,?_⟩
    change R (e-1+1)
    have hn : e-1+1=e := by omega
    simpa only [hn] using he

theorem restrict_injective (q : Nat) (R T : Nat → Prop)
    (hR : Supported q R) (hT : Supported q T) (heq : Restrict q R=Restrict q T) : R=T := by
  have h := congrArg (Lift q) heq
  simpa only [lift_restrict q R hR,lift_restrict q T hT] using h

theorem generated_to_fin (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hg : Generated q R) :
    FinGenerated q (Restrict q R) := by
  obtain ⟨l,hne,hvalid,hR⟩ := hg
  let selected := (List.finRange (4*q+3)).filter (fun i => decide (i.val∈l))
  refine ⟨selected,?_,?_⟩
  · obtain ⟨j,hj⟩ := list_nonempty_witness l hne
    let jf : Fin (4*q+3) := ⟨j,by have := hvalid j hj; omega⟩
    have hm : jf∈selected := List.mem_filter.mpr ⟨List.mem_finRange jf,decide_eq_true hj⟩
    exact List.ne_nil_of_mem hm
  · intro e
    constructor
    · rintro ⟨i,hi,he⟩
      have hil : i.val∈l := of_decide_eq_true (List.mem_filter.mp hi).2
      exact (hR (e.val+1)).mp ⟨i.val,hil,he⟩
    · intro he
      obtain ⟨j,hj,hje⟩ := (hR (e.val+1)).mpr he
      let jf : Fin (4*q+3) := ⟨j,by have := hvalid j hj; omega⟩
      exact ⟨jf,List.mem_filter.mpr ⟨List.mem_finRange jf,decide_eq_true hj⟩,hje⟩

theorem fin_to_generated (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hs : Supported q R)
    (hg : FinGenerated q (Restrict q R)) : Generated q R := by
  obtain ⟨l,hne,hR⟩ := hg
  refine ⟨l.map Fin.val,?_,?_,?_⟩
  · intro h
    exact hne (List.map_eq_nil_iff.mp h)
  · intro i hi
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
    have := j.isLt
    omega
  · intro e
    by_cases hb : 1≤e ∧ e≤4*q
    · let ef : Fin (4*q) := ⟨e-1,by omega⟩
      have hn : e-1+1=e := by omega
      constructor
      · rintro ⟨i,hi,hie⟩
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
        have hjef : LuRazParametric.S q j ef := by
          change LuRazParametric.Row q j.val (e-1+1)
          simpa only [hn] using hie
        have hout := (hR ef).mp ⟨j,hj,hjef⟩
        change R (e-1+1) at hout
        simpa only [hn] using hout
      · intro he
        have href : Restrict q R ef := by
          change R (e-1+1)
          simpa only [hn] using he
        obtain ⟨j,hj,hje⟩ := (hR ef).mpr href
        refine ⟨j.val,List.mem_map.mpr ⟨j,hj,rfl⟩,?_⟩
        change LuRazParametric.Row q j.val (e-1+1) at hje
        simpa only [hn] using hje
    · constructor
      · rintro ⟨i,_,hie⟩
        exact False.elim (hb (row_supported q i e hq hie))
      · intro he
        exact False.elim (hb (hs e he))

theorem generated_fin_iff (q : Nat) (hq : 4≤q) (R : Nat → Prop) (hs : Supported q R) :
    Generated q R ↔ FinGenerated q (Restrict q R) :=
  ⟨generated_to_fin q hq R,fin_to_generated q hq R hs⟩

theorem generated_lift_iff (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) :
    Generated q (Lift q T) ↔ FinGenerated q T := by
  have h := generated_fin_iff q hq (Lift q T) (lift_supported q T)
  rw [restrict_lift q T] at h
  exact h

/-- Transfers a genuine set enumeration and its length to the original finite source. -/
theorem transfer_enumeration (q : Nat) (hq : 4≤q) (P : (Nat → Prop) → Prop)
    (l : List (Nat → Prop)) (hn : l.Nodup)
    (he : ∀ R, R∈l ↔ Generated q R ∧ P R) :
    (l.map (Restrict q)).Nodup ∧
      (∀ T, T∈l.map (Restrict q) ↔ FinGenerated q T ∧ P (Lift q T)) ∧
      (l.map (Restrict q)).length=l.length := by
  refine ⟨?_,?_,List.length_map (Restrict q)⟩
  · apply nodup_map_on _ _ hn
    intro R hR T hT heq
    exact restrict_injective q R T (generated_supported q hq R ((he R).mp hR).1)
      (generated_supported q hq T ((he T).mp hT).1) heq
  · intro T
    constructor
    · intro hT
      obtain ⟨R,hR,hRT⟩ := List.mem_map.mp hT
      have hr := (he R).mp hR
      have hfg := generated_to_fin q hq R hr.1
      rw [hRT] at hfg
      have hLift : Lift q T=R := by rw [←hRT]; exact lift_restrict q R (generated_supported q hq R hr.1)
      exact ⟨hfg,by rw [hLift]; exact hr.2⟩
    · rintro ⟨hgen,hP⟩
      have hg := (generated_lift_iff q hq T).mpr hgen
      exact List.mem_map.mpr ⟨Lift q T,(he (Lift q T)).mpr ⟨hg,hP⟩,restrict_lift q T⟩

end LuRazClosure
