import LuRazCore24
namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem NF24.unique (q : Nat) (hq : 4≤q) (z w : NF24)
    (heq : ∀ e, z.eval q e ↔ w.eval q e) : z=w := by
  cases z with
  | k1 =>
    cases w with
    | k1 =>
      rfl
    | k2 =>
      have h := heq (2*q+2)
      change (K1Row q (2*q+2)) ↔ (K2Row q (2*q+2)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | joinK =>
      have h := heq (4*q-1)
      change (K1Row q (4*q-1)) ↔ (K1Row q (4*q-1) ∨ K2Row q (4*q-1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | fill1 =>
      have h := heq (4*q-1)
      change (K1Row q (4*q-1)) ↔ (K1Row q (4*q-1) ∨ BRow q (4*q-1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | fill2 =>
      have h := heq (2*q+2)
      change (K1Row q (2*q+2)) ↔ (K2Row q (2*q+2) ∨ BRow q (2*q+2)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | dBig =>
      have h := heq (2*q+1)
      change (K1Row q (2*q+1)) ↔ (K1Row q (2*q+1) ∨ DRow q (2*q+1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
  | k2 =>
    cases w with
    | k1 =>
      have h := heq (2*q+2)
      change (K2Row q (2*q+2)) ↔ (K1Row q (2*q+2)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | k2 =>
      rfl
    | joinK =>
      have h := heq (2*q+2)
      change (K2Row q (2*q+2)) ↔ (K1Row q (2*q+2) ∨ K2Row q (2*q+2)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | fill1 =>
      have h := heq (2*q+2)
      change (K2Row q (2*q+2)) ↔ (K1Row q (2*q+2) ∨ BRow q (2*q+2)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | fill2 =>
      have h := heq (4*q)
      change (K2Row q (4*q)) ↔ (K2Row q (4*q) ∨ BRow q (4*q)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | dBig =>
      have h := heq (2*q+1)
      change (K2Row q (2*q+1)) ↔ (K1Row q (2*q+1) ∨ DRow q (2*q+1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
  | joinK =>
    cases w with
    | k1 =>
      have h := heq (4*q-1)
      change (K1Row q (4*q-1) ∨ K2Row q (4*q-1)) ↔ (K1Row q (4*q-1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | k2 =>
      have h := heq (2*q+2)
      change (K1Row q (2*q+2) ∨ K2Row q (2*q+2)) ↔ (K2Row q (2*q+2)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | joinK =>
      rfl
    | fill1 =>
      have h := heq (4*q)
      change (K1Row q (4*q) ∨ K2Row q (4*q)) ↔ (K1Row q (4*q) ∨ BRow q (4*q)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | fill2 =>
      have h := heq (2*q+2)
      change (K1Row q (2*q+2) ∨ K2Row q (2*q+2)) ↔ (K2Row q (2*q+2) ∨ BRow q (2*q+2)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | dBig =>
      have h := heq (2*q+1)
      change (K1Row q (2*q+1) ∨ K2Row q (2*q+1)) ↔ (K1Row q (2*q+1) ∨ DRow q (2*q+1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
  | fill1 =>
    cases w with
    | k1 =>
      have h := heq (4*q-1)
      change (K1Row q (4*q-1) ∨ BRow q (4*q-1)) ↔ (K1Row q (4*q-1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | k2 =>
      have h := heq (2*q+2)
      change (K1Row q (2*q+2) ∨ BRow q (2*q+2)) ↔ (K2Row q (2*q+2)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | joinK =>
      have h := heq (4*q)
      change (K1Row q (4*q) ∨ BRow q (4*q)) ↔ (K1Row q (4*q) ∨ K2Row q (4*q)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | fill1 =>
      rfl
    | fill2 =>
      have h := heq (2*q+2)
      change (K1Row q (2*q+2) ∨ BRow q (2*q+2)) ↔ (K2Row q (2*q+2) ∨ BRow q (2*q+2)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | dBig =>
      have h := heq (2*q+1)
      change (K1Row q (2*q+1) ∨ BRow q (2*q+1)) ↔ (K1Row q (2*q+1) ∨ DRow q (2*q+1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
  | fill2 =>
    cases w with
    | k1 =>
      have h := heq (2*q+2)
      change (K2Row q (2*q+2) ∨ BRow q (2*q+2)) ↔ (K1Row q (2*q+2)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | k2 =>
      have h := heq (4*q)
      change (K2Row q (4*q) ∨ BRow q (4*q)) ↔ (K2Row q (4*q)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | joinK =>
      have h := heq (2*q+2)
      change (K2Row q (2*q+2) ∨ BRow q (2*q+2)) ↔ (K1Row q (2*q+2) ∨ K2Row q (2*q+2)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | fill1 =>
      have h := heq (2*q+2)
      change (K2Row q (2*q+2) ∨ BRow q (2*q+2)) ↔ (K1Row q (2*q+2) ∨ BRow q (2*q+2)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | fill2 =>
      rfl
    | dBig =>
      have h := heq (2*q+1)
      change (K2Row q (2*q+1) ∨ BRow q (2*q+1)) ↔ (K1Row q (2*q+1) ∨ DRow q (2*q+1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
  | dBig =>
    cases w with
    | k1 =>
      have h := heq (2*q+1)
      change (K1Row q (2*q+1) ∨ DRow q (2*q+1)) ↔ (K1Row q (2*q+1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | k2 =>
      have h := heq (2*q+1)
      change (K1Row q (2*q+1) ∨ DRow q (2*q+1)) ↔ (K2Row q (2*q+1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | joinK =>
      have h := heq (2*q+1)
      change (K1Row q (2*q+1) ∨ DRow q (2*q+1)) ↔ (K1Row q (2*q+1) ∨ K2Row q (2*q+1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | fill1 =>
      have h := heq (2*q+1)
      change (K1Row q (2*q+1) ∨ DRow q (2*q+1)) ↔ (K1Row q (2*q+1) ∨ BRow q (2*q+1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | fill2 =>
      have h := heq (2*q+1)
      change (K1Row q (2*q+1) ∨ DRow q (2*q+1)) ↔ (K2Row q (2*q+1) ∨ BRow q (2*q+1)) at h
      exfalso
      simp only [K1Row,K2Row,DRow,BRow,I] at h
      simp_all <;> omega
    | dBig =>
      rfl

def all24 : List NF24 := [.k1,.k2,.joinK,.fill1,.fill2,.dBig]
def members24 (q : Nat) : List (Nat → Prop) := all24.map (NF24.eval q)

theorem all24_nodup : all24.Nodup := by decide
theorem all24_mem (z : NF24) : z∈all24 := by cases z <;> simp [all24]

theorem members24_nodup (q : Nat) (hq : 4≤q) : (members24 q).Nodup := by
  apply nodup_map_on _ _ all24_nodup
  intro a _ b _ heq
  exact NF24.unique q hq a b (fun e => Iff.of_eq (congrFun heq e))

theorem members24_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈members24 q ↔ Generated q R ∧ Core24 R := by
  constructor
  · intro hR
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hR
    exact ⟨NF24.generated q hq z,NF24.core q hq z⟩
  · intro hR
    obtain ⟨z,heq⟩ := (core24_closure_exact q hq R).mp hR
    refine List.mem_map.mpr ⟨z,all24_mem z,?_⟩
    funext e
    exact propext (heq e).symm

theorem core24_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ Core24 R) ∧ l.length=6 := by
  exact ⟨members24 q,members24_nodup q hq,members24_exact q hq,by simp [members24,all24]⟩

def FinCore24 (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) : Prop :=
  ¬T ⟨0,by omega⟩ ∧ T ⟨1,by omega⟩ ∧ ¬T ⟨2,by omega⟩ ∧ T ⟨3,by omega⟩

theorem fin_core24_iff (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) :
    Core24 (Lift q T) ↔ FinCore24 q hq T := by
  unfold Core24 FinCore24
  rw [lift_at q T 1 (by omega),lift_at q T 2 (by omega),
      lift_at q T 3 (by omega),lift_at q T 4 (by omega)]

theorem core24_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ FinCore24 q hq T) ∧ l.length=6 := by
  obtain ⟨l,hn,he,hl⟩ := core24_cardinality q hq
  have ht := transfer_enumeration q hq Core24 l hn he
  refine ⟨l.map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (fin_core24_iff q hq T))
  · rw [List.length_map]
    exact hl

end LuRazClosure
