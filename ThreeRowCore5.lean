import ThreeRowUnchanged
import ThreeRowCore23

namespace LuRazThreeRow
open LuRazClosure LuRazParametric LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def Core5 (R : Nat → Prop) : Prop := R 1 ∧ ¬R 2 ∧ R 3 ∧ ¬R 4
def ZPrime (q e : Nat) : Prop := e=1 ∨ e=3 ∨ I 5 (2*q) e ∨ I (4*q-1) (4*q) e

theorem z_source (q e : Nat) (hq : 4≤q) : VRow q 2 e ↔ ZPrime q e := by
  rw [row_two q e hq]
  unfold ZPrime I
  omega

theorem a_source (q e : Nat) (hq : 4≤q) : VRow q (4*q+2) e ↔ ARow q e := by
  rw [unchanged_row q (4*q+2) e (by unfold Special; omega)]
  exact A_source q e hq

theorem core5_row (q i : Nat) (hq : 4≤q) (hi : i≤4*q+2)
    (h2 : ¬VRow q i 2) (h4 : ¬VRow q i 4) :
    i=2 ∨ i=4*q ∨ i=4*q+1 ∨ i=4*q+2 := by
  by_cases hs : Special q i
  · rcases hs with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim (h2 ((row_four q 2 hq).mpr (by omega)))
    · exact False.elim (h4 ((row_last q 4 hq).mpr (by omega)))
  have ho2 : ¬Row q i 2 := by rwa [unchanged_row q i 2 hs] at h2
  have ho4 : ¬Row q i 4 := by rwa [unchanged_row q i 4 hs] at h4
  have hr := row_fixed_small q i hq hi ho4 (fun h => ho2 h.1)
  rcases hr with h | h | h | h | h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact False.elim (ho2 ((row_case_1 q i 2 (by omega) h).mpr (by omega)))
  · exact False.elim (hs (Or.inr (Or.inl h)))

def Mix5 (q : Nat) (a b c z : Prop) (e : Nat) : Prop :=
  (a ∧ ARow q e) ∨ (b ∧ BRow q e) ∨ (c ∧ CRow q e) ∨ (z ∧ ZPrime q e)

theorem core5_mix (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core5 R) :
    ∃ a b c z : Prop, (a∨z) ∧ (c∨z) ∧ ∀ e, R e ↔ Mix5 q a b c z e := by
  obtain ⟨l,hn,hv,hR⟩ := hg
  have hr : ∀ i∈l, i=2 ∨ i=4*q ∨ i=4*q+1 ∨ i=4*q+2 := by
    intro i hi
    exact core5_row q i hq (hv i hi)
      (fun h => hc.2.1 ((hR 2).mp ⟨i,hi,h⟩))
      (fun h => hc.2.2.2 ((hR 4).mp ⟨i,hi,h⟩))
  have he : ∀ e, R e ↔ Mix5 q (4*q+2∈l) (4*q+1∈l) (4*q∈l) (2∈l) e := by
    intro e
    rw [←hR e]
    constructor
    · rintro ⟨i,hi,hie⟩
      rcases hr i hi with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inr ⟨hi,(z_source q e hq).mp hie⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hi,(c_source q e hq).mp hie⟩))
      · exact Or.inr (Or.inl ⟨hi,(b_source q e hq).mp hie⟩)
      · exact Or.inl ⟨hi,(a_source q e hq).mp hie⟩
    · intro h
      rcases h with ⟨hi,h⟩ | ⟨hi,h⟩ | ⟨hi,h⟩ | ⟨hi,h⟩
      · exact ⟨4*q+2,hi,(a_source q e hq).mpr h⟩
      · exact ⟨4*q+1,hi,(b_source q e hq).mpr h⟩
      · exact ⟨4*q,hi,(c_source q e hq).mpr h⟩
      · exact ⟨2,hi,(z_source q e hq).mpr h⟩
  refine ⟨4*q+2∈l,4*q+1∈l,4*q∈l,2∈l,?_,?_,he⟩
  · have h := (he 1).mp hc.1
    rcases h with ⟨h,_⟩ | ⟨_,h⟩ | ⟨_,h⟩ | ⟨h,_⟩
    · exact Or.inl h
    · unfold BRow I at h; omega
    · unfold CRow I at h; omega
    · exact Or.inr h
  · have h := (he 3).mp hc.2.2.1
    rcases h with ⟨_,h⟩ | ⟨_,h⟩ | ⟨h,_⟩ | ⟨h,_⟩
    · unfold ARow I at h; omega
    · unfold BRow I at h; omega
    · exact Or.inl h
    · exact Or.inr h

inductive NF5 where
  | z | zb | zc | ac | acb
  deriving DecidableEq, Repr

def NF5.eval (q : Nat) : NF5 → Nat → Prop
  | .z => ZPrime q
  | .zb => fun e => ZPrime q e ∨ BRow q e
  | .zc => fun e => ZPrime q e ∨ CRow q e
  | .ac => fun e => ARow q e ∨ CRow q e
  | .acb => fun e => ARow q e ∨ CRow q e ∨ BRow q e

theorem mix5_normal (q : Nat) (hq : 4≤q) (a b c z : Prop) (ha : a∨z) (hc : c∨z) :
    ∃ w : NF5, ∀ e, Mix5 q a b c z e ↔ w.eval q e := by
  classical
  by_cases hz : z
  · by_cases hb : b
    · by_cases hc' : c
      · refine ⟨.acb,?_⟩
        intro e
        simp only [Mix5,NF5.eval,hz,hb,hc',true_and,ARow,BRow,CRow,ZPrime,I]
        by_cases ha' : a <;> simp only [ha',true_and,false_and,false_or] <;> omega
      · refine ⟨.zb,?_⟩
        intro e
        simp only [Mix5,NF5.eval,hz,hb,hc',true_and,false_and,false_or,ARow,BRow,ZPrime,I]
        by_cases ha' : a <;> simp only [ha',true_and,false_and,false_or] <;> omega
    · by_cases hc' : c
      · refine ⟨.zc,?_⟩
        intro e
        simp only [Mix5,NF5.eval,hz,hb,hc',true_and,false_and,false_or,ARow,CRow,ZPrime,I]
        by_cases ha' : a <;> simp only [ha',true_and,false_and,false_or] <;> omega
      · refine ⟨.z,?_⟩
        intro e
        simp only [Mix5,NF5.eval,hz,hb,hc',true_and,false_and,false_or,ARow,ZPrime,I]
        by_cases ha' : a <;> simp only [ha',true_and,false_and,false_or] <;> omega
  · have ha' : a := ha.resolve_right hz
    have hc' : c := hc.resolve_right hz
    by_cases hb : b
    · refine ⟨.acb,?_⟩
      intro e
      simp only [Mix5,NF5.eval,hz,hb,ha',hc',true_and,false_and,or_false]
      exact or_congr Iff.rfl or_comm
    · refine ⟨.ac,?_⟩
      intro e
      simp only [Mix5,NF5.eval,hz,hb,ha',hc',true_and,false_and,false_or,or_false]

theorem nf5_generated (q : Nat) (hq : 4≤q) (z : NF5) : Generated q (z.eval q) := by
  have hz := generated_congr q (generated_row q 2 (by omega)) (fun e => z_source q e hq)
  have ha := generated_congr q (generated_row q (4*q+2) (by omega)) (fun e => a_source q e hq)
  have hb := generated_b q hq
  have hc := generated_c q hq
  cases z with
  | z => exact hz
  | zb => exact generated_join q hz hb
  | zc => exact generated_join q hz hc
  | ac => exact generated_join q ha hc
  | acb =>
    apply generated_congr q (generated_join q (generated_join q ha hc) hb)
    intro e
    exact or_assoc

theorem nf5_core (q : Nat) (hq : 4≤q) (z : NF5) : Core5 (z.eval q) := by
  cases z <;> unfold Core5 NF5.eval ARow BRow CRow ZPrime I <;> simp_all <;> omega

theorem core5_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ Core5 R ↔ ∃ z : NF5, ∀ e, R e ↔ z.eval q e := by
  constructor
  · intro h
    obtain ⟨a,b,c,z,ha,hc,he⟩ := core5_mix q hq R h.1 h.2
    obtain ⟨w,hw⟩ := mix5_normal q hq a b c z ha hc
    exact ⟨w,fun e => (he e).trans (hw e)⟩
  · rintro ⟨z,he⟩
    refine ⟨generated_congr q (nf5_generated q hq z) (fun e => (he e).symm),?_⟩
    have hc := nf5_core q hq z
    unfold Core5 at *
    rw [he 1,he 2,he 3,he 4]
    exact hc

theorem nf5_unique (q : Nat) (hq : 4≤q) (a b : NF5)
    (he : ∀ e, a.eval q e ↔ b.eval q e) : a=b := by
  have h1 := he (2*q+1)
  have h2 := he (4*q-1)
  have h3 := he (3*q+2)
  cases a <;> cases b <;>
    simp only [NF5.eval,ZPrime,ARow,BRow,CRow,I] at h1 h2 h3 <;> simp_all <;> omega

def members5 (q : Nat) : List (Nat → Prop) :=
  ([NF5.z,NF5.zb,NF5.zc,NF5.ac,NF5.acb]).map (NF5.eval q)

theorem members5_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈members5 q ↔ Generated q R ∧ Core5 R := by
  rw [core5_exact q hq R]
  constructor
  · intro h
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp h
    exact ⟨z,fun _ => Iff.rfl⟩
  · rintro ⟨z,he⟩
    have hm : z∈[NF5.z,NF5.zb,NF5.zc,NF5.ac,NF5.acb] := by cases z <;> simp
    exact List.mem_map.mpr ⟨z,hm,funext (fun e => propext (he e).symm)⟩

theorem members5_nodup (q : Nat) (hq : 4≤q) : (members5 q).Nodup := by
  apply nodup_map_on _ _ (by decide)
  intro a _ b _ he
  exact nf5_unique q hq a b (fun e => Iff.of_eq (congrFun he e))

theorem core5_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ Core5 R) ∧ l.length=5 :=
  ⟨members5 q,members5_nodup q hq,members5_exact q hq,by simp [members5]⟩

end LuRazThreeRow
