import SixRowFullNormal

namespace LuRazSixRowClosure
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def FullLast (q e : Nat) : Prop := e=1 ∨ e=3 ∨ I 5 (2*q+2) e
def FullC (q e : Nat) : Prop := e=3 ∨ I 5 (2*q+1) e ∨ e=3*q+1 ∨ e=4*q-1
def FullE (q e : Nat) : Prop := e=2 ∨ e=3 ∨ I (2*q+3) (4*q) e
def FullM (q e : Nat) : Prop := e=2 ∨ e=4 ∨ I (2*q+3) (4*q-2) e ∨ e=4*q

theorem full_gen_A (q : Nat) (hq : 4≤q) : Generated q (ARow q) := by
  apply generated_congr q (generated_row q (4*q+2) (by omega))
  intro e
  rw [full_unchanged q _ e (by unfold FullChanged; omega),A_source q e hq]

theorem full_gen_B (q : Nat) (hq : 4≤q) : Generated q (LuRazClosure.BRow q) := by
  apply generated_congr q (generated_row q (4*q+1) (by omega))
  intro e
  rw [full_unchanged q _ e (by unfold FullChanged; omega),B_source q e hq]

theorem full_gen_Last (q : Nat) (hq : 4≤q) : Generated q (FullLast q) :=
  generated_congr q (generated_row q (4*q-1) (by omega)) (fun e => LuRazSixRow.row_last q e hq)

theorem full_gen_C (q : Nat) (hq : 4≤q) : Generated q (FullC q) :=
  generated_congr q (generated_row q (4*q) (by omega)) (fun e => LuRazSixRow.row_n q e hq)

theorem full_gen_E (q : Nat) (hq : 4≤q) : Generated q (FullE q) :=
  generated_congr q (generated_row q 4 (by omega)) (fun e => full_row_four q e hq)

theorem full_gen_M (q : Nat) (hq : 4≤q) : Generated q (FullM q) :=
  generated_congr q (generated_row q (2*q+2) (by omega)) (fun e => LuRazSixRow.row_middle q e hq)

theorem full_gen_K1 (q : Nat) (hq : 4≤q) : Generated q (K1Row q) := by
  apply generated_congr q (generated_row q (2*q+1) (by omega))
  intro e
  rw [full_unchanged q _ e (by unfold FullChanged; omega),row_case_7 q _ e (by omega) rfl]
  unfold K1Row I
  omega

theorem full_l_source (q p e : Nat) (hq : 4≤q) (hp : P q p) (hpl : p≤2*q) :
    LuRazSixRow.BRow q (LIndex q p) e ↔ LRow q p p e := by
  rw [full_unchanged q (LIndex q p) e ?_]
  · exact LRow_source q p e hq hp
  · unfold FullChanged LIndex beta
    unfold P at hp
    split <;> omega

theorem full_gen_L (q t p : Nat) (hq : 4≤q) (ht : P q t) (hp : P q p)
    (htp : t≤p) (hpl : p≤2*q) : Generated q (LRow q t p) := by
  have hbt := beta_bounds q t hq ht
  have hbp := beta_bounds q p hq hp
  have hT := generated_congr q (generated_row q (LIndex q t) (by unfold LIndex; omega))
    (fun e => full_l_source q t e hq ht (by omega))
  have hP := generated_congr q (generated_row q (LIndex q p) (by unfold LIndex; omega))
    (fun e => full_l_source q p e hq hp hpl)
  apply generated_congr q (generated_join q hT hP)
  intro e
  have h := LRow_join q t t p p e hq ht ht hp hp (by omega) (by omega)
  simpa only [Nat.min_eq_left htp,Nat.max_eq_right htp] using h

theorem full_gen_J (q a b : Nat) (hq : 4≤q) (hab : JReachable q a b) :
    Generated q (JRow a b) := by
  obtain ⟨l,hn,hv,he⟩ := J_source_attainable q a b hq hab
  have hs (a : Nat) (ha : 5≤a ∧ a≤2*q+1) : ¬FullChanged q (JIndex a) := by
    unfold FullChanged JIndex
    split <;> omega
  refine ⟨l.map JIndex,fun h => hn (List.map_eq_nil_iff.mp h),?_,?_⟩
  · intro i hi
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
    have ha' := hv a ha
    unfold JIndex
    split <;> omega
  · intro e
    constructor
    · rintro ⟨i,hi,hie⟩
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
      exact (he e).mp ⟨a,ha,(full_unchanged q _ e (hs a (hv a ha))).mp hie⟩
    · intro h
      obtain ⟨a,ha,hae⟩ := (he e).mpr h
      exact ⟨JIndex a,List.mem_map.mpr ⟨a,ha,rfl⟩,
        (full_unchanged q _ e (hs a (hv a ha))).mpr hae⟩

theorem full_gen_Jfive (q b : Nat) (hq : 4≤q) (hb : 2*q+2≤b ∧ b≤4*q-3) :
    Generated q (JRow 5 b) := by
  apply full_gen_J q 5 b hq
  unfold JReachable g
  split <;> omega

end LuRazSixRowClosure
