import SixRowCore13Parts

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

inductive NF13 where
  | full | plain (b : Nat) | last (b : Nat) | isolated (b : Nat)
  | double (b : Nat) | doubleIsolated (b : Nat) | withB (b : Nat) | withC (b : Nat)
  deriving DecidableEq, Repr

def NF13.Valid (q : Nat) : NF13 → Prop
  | .full => True
  | .plain b | .double b => 2*q+2≤b ∧ b≤4*q-3
  | .last b => 3*q+1≤b ∧ b≤4*q-3
  | .isolated b | .doubleIsolated b | .withC b => 2*q+2≤b ∧ b≤3*q-1
  | .withB b => 2*q+2≤b ∧ b≤3*q

def NF13.eval (q : Nat) : NF13 → Nat → Prop
  | .full => fun e => T134 e ∨ I 5 (4*q) e
  | .plain b => fun e => T134 e ∨ I 5 b e
  | .last b => fun e => T134 e ∨ I 5 b e ∨ e=4*q-1
  | .isolated b => fun e => T134 e ∨ I 5 b e ∨ e=3*q+1 ∨ e=4*q-1
  | .double b => fun e => T134 e ∨ I 5 b e ∨ I (4*q-1) (4*q) e
  | .doubleIsolated b => fun e => T134 e ∨ I 5 b e ∨ e=3*q+1 ∨ I (4*q-1) (4*q) e
  | .withB b => fun e => T134 e ∨ I 5 b e ∨ I (3*q+2) (4*q) e
  | .withC b => fun e => T134 e ∨ I 5 b e ∨ I (3*q+1) (4*q) e

def Raw13 (q b : Nat) (v d z : Prop) (e : Nat) : Prop :=
  T134 e ∨ I 5 b e ∨ (v∧LuRazClosure.BRow q e) ∨ (d∧e=3*q+1) ∨
    ((d∨z)∧e=4*q-1) ∨ (z∧e=4*q)

theorem mixed13_raw (q a b : Nat) (hq : 4≤q) (hab : JReachable q a b)
    (u v d l z : Prop) (hg : d∨l∨z) (e : Nat) :
    Mixed13 q a b u v d l z e ↔ Raw13 q b v d z e := by
  unfold JReachable at hab
  by_cases hu : u <;> by_cases hv : v <;> by_cases hd : d <;> by_cases hl : l <;> by_cases hz : z
  all_goals simp_all [Mixed13,Fixed13,Raw13,JRow,T134,ARow,LuRazClosure.BRow,CPrime,LNew,LuRazThreeRow.ZPrime,I] <;> omega

theorem raw13_normal (q b : Nat) (hq : 4≤q) (hb : 2*q+2≤b ∧ b≤4*q-3)
    (v d z : Prop) : ∃ w : NF13,w.Valid q ∧ ∀ e,Raw13 q b v d z e ↔ w.eval q e := by
  classical
  by_cases hv : v
  · by_cases hbr : 3*q+1≤b
    · refine ⟨.full,True.intro,?_⟩
      intro e
      by_cases hd : d <;> by_cases hz : z <;>
        simp_all [Raw13,NF13.eval,T134,LuRazClosure.BRow,I] <;> omega
    · by_cases hd : d
      · by_cases hbe : b=3*q
        · refine ⟨.full,True.intro,?_⟩
          intro e
          by_cases hz : z <;> simp_all [Raw13,NF13.eval,T134,LuRazClosure.BRow,I] <;> omega
        · refine ⟨.withC b,by unfold NF13.Valid; omega,?_⟩
          intro e
          by_cases hz : z <;> simp_all [Raw13,NF13.eval,T134,LuRazClosure.BRow,I] <;> omega
      · refine ⟨.withB b,by unfold NF13.Valid; omega,?_⟩
        intro e
        by_cases hz : z <;> simp_all [Raw13,NF13.eval,T134,LuRazClosure.BRow,I] <;> omega
  · by_cases hz : z
    · by_cases hd : d
      · by_cases hbr : 3*q≤b
        · refine ⟨.double (max b (3*q+1)),by unfold NF13.Valid; omega,?_⟩
          intro e
          simp_all [Raw13,NF13.eval,T134,LuRazClosure.BRow,I] <;> omega
        · refine ⟨.doubleIsolated b,by unfold NF13.Valid; omega,?_⟩
          intro e
          simp_all [Raw13,NF13.eval,T134,LuRazClosure.BRow,I] <;> omega
      · refine ⟨.double b,hb,?_⟩
        intro e
        simp_all [Raw13,NF13.eval,T134,LuRazClosure.BRow,I] <;> omega
    · by_cases hd : d
      · by_cases hbr : 3*q≤b
        · refine ⟨.last (max b (3*q+1)),by unfold NF13.Valid; omega,?_⟩
          intro e
          simp_all [Raw13,NF13.eval,T134,LuRazClosure.BRow,I] <;> omega
        · refine ⟨.isolated b,by unfold NF13.Valid; omega,?_⟩
          intro e
          simp_all [Raw13,NF13.eval,T134,LuRazClosure.BRow,I] <;> omega
      · refine ⟨.plain b,hb,?_⟩
        intro e
        simp_all [Raw13,NF13.eval,T134,LuRazClosure.BRow,I] <;> omega

theorem core13_normal (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : Core134 R) :
    ∃ w : NF13,w.Valid q ∧ ∀ e,R e ↔ w.eval q e := by
  obtain ⟨a,b,hab,u,v,d,l,z,hg,he⟩ := core13_parts q hq R hg hc
  obtain ⟨w,hw,hew⟩ := raw13_normal q b hq ⟨hab.2.2.1,hab.2.2.2.1⟩ v d z
  exact ⟨w,hw,fun e => (he e).trans ((mixed13_raw q a b hq hab u v d l z hg e).trans (hew e))⟩

theorem generated_j (q a b : Nat) (hq : 4≤q) (hab : JReachable q a b) : Generated q (JRow a b) := by
  obtain ⟨l,hn,hv,he⟩ := J_source_attainable q a b hq hab
  refine ⟨l.map JIndex,fun h => hn (List.map_eq_nil_iff.mp h),?_,?_⟩
  · intro i hi
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi
    have h := hv t ht
    unfold JIndex
    split <;> omega
  · intro e
    constructor
    · rintro ⟨i,hi,hie⟩
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi
      exact (he e).mp ⟨t,ht,(J_is_source_row q t e hq (hv t ht)).mpr ((j_source q t e hq (hv t ht)).mp hie)⟩
    · intro h
      obtain ⟨t,ht,hte⟩ := (he e).mpr h
      exact ⟨JIndex t,List.mem_map.mpr ⟨t,ht,rfl⟩,
        (j_source q t e hq (hv t ht)).mpr ((J_is_source_row q t e hq (hv t ht)).mp hte)⟩

theorem raw13_generated (q b : Nat) (hq : 4≤q) (hb : 2*q+2≤b ∧ b≤4*q-3)
    (v d z : Prop) : Generated q (Raw13 q b v d z) := by
  have hj : JReachable q 5 b := by unfold JReachable g; split <;> omega
  have h := generated_optional q (generated_j q 5 b hq hj)
    (generated_congr q (generated_row q (4*q+1) (by omega)) (fun e => b_source q e hq)) v
  have h := generated_optional q h
    (generated_congr q (generated_row q (4*q) (by omega)) (fun e => c_source q e hq)) d
  have h := generated_join q h
    (generated_congr q (generated_row q (4*q-1) (by omega)) (fun e => last_source q e hq))
  have h := generated_optional q h
    (generated_congr q (generated_row q 2 (by omega)) (fun e => z_source q e hq)) z
  apply generated_congr q h
  intro e
  have hm := mixed13_raw q 5 b hq hj False v d True z (Or.inr (Or.inl True.intro)) e
  simpa only [Mixed13,Fixed13,false_and,false_or,true_and,or_assoc] using hm

theorem NF13.generated (q : Nat) (hq : 4≤q) (w : NF13) (hw : w.Valid q) : Generated q (w.eval q) := by
  cases w with
  | full =>
    apply generated_congr q (raw13_generated q (4*q-3) hq (by omega) True False False)
    intro e
    simp only [Raw13,NF13.eval,true_and,false_and,false_or,or_false,T134,LuRazClosure.BRow,I]
    omega
  | plain b =>
    simp only [NF13.Valid] at hw
    apply generated_congr q (raw13_generated q b hq hw False False False)
    intro e
    simp [Raw13,NF13.eval]
  | last b =>
    simp only [NF13.Valid] at hw
    apply generated_congr q (raw13_generated q b hq (by omega) False True False)
    intro e
    simp [Raw13,NF13.eval,T134,I] <;> omega
  | isolated b =>
    simp only [NF13.Valid] at hw
    apply generated_congr q (raw13_generated q b hq (by omega) False True False)
    intro e
    simp [Raw13,NF13.eval,T134,I] <;> omega
  | double b =>
    simp only [NF13.Valid] at hw
    apply generated_congr q (raw13_generated q b hq hw False False True)
    intro e
    simp [Raw13,NF13.eval,T134,I] <;> omega
  | doubleIsolated b =>
    simp only [NF13.Valid] at hw
    apply generated_congr q (raw13_generated q b hq (by omega) False True True)
    intro e
    simp [Raw13,NF13.eval,T134,I] <;> omega
  | withB b =>
    simp only [NF13.Valid] at hw
    apply generated_congr q (raw13_generated q b hq (by omega) True False False)
    intro e
    simp [Raw13,NF13.eval,T134,LuRazClosure.BRow,I] <;> omega
  | withC b =>
    simp only [NF13.Valid] at hw
    apply generated_congr q (raw13_generated q b hq (by omega) True True False)
    intro e
    simp [Raw13,NF13.eval,T134,LuRazClosure.BRow,I] <;> omega

theorem NF13.core (q : Nat) (hq : 4≤q) (w : NF13) (hw : w.Valid q) : Core134 (w.eval q) := by
  cases w <;> unfold NF13.Valid at hw <;>
    simp [NF13.eval,Core134,T134,I] <;> omega

theorem core13_exhaustive (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    Generated q R ∧ Core134 R ↔ ∃ w : NF13,w.Valid q ∧ ∀ e,R e ↔ w.eval q e := by
  constructor
  · exact fun h => core13_normal q hq R h.1 h.2
  · rintro ⟨w,hw,he⟩
    refine ⟨generated_congr q (NF13.generated q hq w hw) (fun e => (he e).symm),?_⟩
    have hc := NF13.core q hq w hw
    unfold Core134 at *
    rw [he 1,he 2,he 3,he 4]
    exact hc

end LuRazSixRowClosure
