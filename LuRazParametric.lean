import LuRazFollowup
import RazReimerPredicates

/-!
An explicit completed definition of the Lu--Raz 2024 construction.
q=x+1, n=4q, x>=2 means q>=3. All coordinates are one-based.
The source omits row 2q+1; we DEFINE it here as {2,4} union [2q+2,4q-2].
No inference about the author's intended row is an assumption of a theorem.
-/
namespace LuRazParametric

def Row (q i e : Nat) : Prop :=
  (i = 0 ∧ 1 ≤ e ∧ e ≤ 4*q) ∨
  (i = 1 ∧ (e = 2 ∨ (2*q+1 ≤ e ∧ e ≤ 4*q))) ∨
  (i = 2 ∧ (e = 1 ∨ (3 ≤ e ∧ e ≤ 2*q) ∨ e = 4*q)) ∨
  (i = 3 ∧ (e = 1 ∨ (4 ≤ e ∧ e ≤ 2*q+2))) ∨
  (i = 4 ∧ (e = 1 ∨ e = 3 ∨ (2*q+3 ≤ e ∧ e ≤ 4*q))) ∨
  (5 ≤ i ∧ i ≤ q+2 ∧ (e = 1 ∨ e = 4 ∨ (i+1 ≤ e ∧ e+2 ≤ 2*q+i))) ∨
  (q+3 ≤ i ∧ i ≤ 2*q ∧ (e = 1 ∨ e = 4 ∨ (i+1 ≤ e ∧ e+3 ≤ 2*q+i))) ∨
  (i = 2*q+1 ∧ (e = 2 ∨ e = 4 ∨ (2*q+2 ≤ e ∧ e+2 ≤ 4*q))) ∨
  (i = 2*q+2 ∧ (e = 2 ∨ e = 4 ∨ (2*q+3 ≤ e ∧ e+1 ≤ 4*q))) ∨
  (i = 2*q+3 ∧ (e = 2 ∨ e = 3 ∨ (2*q+4 ≤ e ∧ e ≤ 4*q))) ∨
  (2*q+4 ≤ i ∧ i ≤ 3*q ∧
    (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e+2*q ≤ i+1) ∨ (i+1 ≤ e ∧ e ≤ 4*q))) ∨
  (i = 3*q+1 ∧ (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e ≤ q+3) ∨
    (3*q+2 ≤ e ∧ e+1 ≤ 4*q))) ∨
  (3*q+2 ≤ i ∧ i+1 ≤ 4*q ∧
    (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e+2*q ≤ i+2) ∨ (i+1 ≤ e ∧ e ≤ 4*q))) ∨
  (i = 4*q ∧ (e = 3 ∨ (5 ≤ e ∧ e ≤ 2*q+2) ∨ e = 3*q+1)) ∨
  (i = 4*q+1 ∧ 3*q+2 ≤ e ∧ e ≤ 4*q) ∨
  (i = 4*q+2 ∧ (e = 1 ∨ (5 ≤ e ∧ e ≤ q+2)))

def FilterRow (q i e : Nat) : Prop :=
  i = 0 ∨ (1 ≤ i ∧ i ≤ 4*q ∧ e ≠ i) ∨
  (i = 4*q+1 ∧ e ≠ 1 ∧ e ≠ 2) ∨
  (i = 4*q+2 ∧ e ≠ 3 ∧ e ≠ 4)

def S (q : Nat) (i : Fin (4*q+3)) (e : Fin (4*q)) : Prop :=
  Row q i.val (e.val+1)
def F (q : Nat) (i : Fin (4*q+3)) (e : Fin (4*q)) : Prop :=
  FilterRow q i.val (e.val+1)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem row_case_0 (q i e : Nat) (hq : 3 ≤ q)
    (hc : i = 0) : Row q i e ↔ (1 ≤ e ∧ e ≤ 4*q) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inl ⟨hc,h⟩

theorem row_case_1 (q i e : Nat) (hq : 3 ≤ q)
    (hc : i = 1) : Row q i e ↔ (e = 2 ∨ (2*q+1 ≤ e ∧ e ≤ 4*q)) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inl ⟨hc,h⟩)

theorem row_case_2 (q i e : Nat) (hq : 3 ≤ q)
    (hc : i = 2) : Row q i e ↔ (e = 1 ∨ (3 ≤ e ∧ e ≤ 2*q) ∨ e = 4*q) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inl ⟨hc,h⟩))

theorem row_case_3 (q i e : Nat) (hq : 3 ≤ q)
    (hc : i = 3) : Row q i e ↔ (e = 1 ∨ (4 ≤ e ∧ e ≤ 2*q+2)) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hc,h⟩)))

theorem row_case_4 (q i e : Nat) (hq : 3 ≤ q)
    (hc : i = 4) : Row q i e ↔ (e = 1 ∨ e = 3 ∨ (2*q+3 ≤ e ∧ e ≤ 4*q)) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc,h⟩))))

theorem row_case_5 (q i e : Nat) (hq : 3 ≤ q)
    (hc : 5 ≤ i ∧ i ≤ q+2) : Row q i e ↔ (e = 1 ∨ e = 4 ∨ (i+1 ≤ e ∧ e+2 ≤ 2*q+i)) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc.1,hc.2,h⟩)))))

theorem row_case_6 (q i e : Nat) (hq : 3 ≤ q)
    (hc : q+3 ≤ i ∧ i ≤ 2*q) : Row q i e ↔ (e = 1 ∨ e = 4 ∨ (i+1 ≤ e ∧ e+3 ≤ 2*q+i)) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc.1,hc.2,h⟩))))))

theorem row_case_7 (q i e : Nat) (hq : 3 ≤ q)
    (hc : i = 2*q+1) : Row q i e ↔ (e = 2 ∨ e = 4 ∨ (2*q+2 ≤ e ∧ e+2 ≤ 4*q)) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc,h⟩)))))))

theorem row_case_8 (q i e : Nat) (hq : 3 ≤ q)
    (hc : i = 2*q+2) : Row q i e ↔ (e = 2 ∨ e = 4 ∨ (2*q+3 ≤ e ∧ e+1 ≤ 4*q)) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc,h⟩))))))))

theorem row_case_9 (q i e : Nat) (hq : 3 ≤ q)
    (hc : i = 2*q+3) : Row q i e ↔ (e = 2 ∨ e = 3 ∨ (2*q+4 ≤ e ∧ e ≤ 4*q)) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc,h⟩)))))))))

theorem row_case_10 (q i e : Nat) (hq : 3 ≤ q)
    (hc : 2*q+4 ≤ i ∧ i ≤ 3*q) : Row q i e ↔ (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e+2*q ≤ i+1) ∨ (i+1 ≤ e ∧ e ≤ 4*q)) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc.1,hc.2,h⟩))))))))))

theorem row_case_11 (q i e : Nat) (hq : 3 ≤ q)
    (hc : i = 3*q+1) : Row q i e ↔ (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e ≤ q+3) ∨ (3*q+2 ≤ e ∧ e+1 ≤ 4*q)) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc,h⟩)))))))))))

theorem row_case_12 (q i e : Nat) (hq : 3 ≤ q)
    (hc : 3*q+2 ≤ i ∧ i+1 ≤ 4*q) : Row q i e ↔ (e = 2 ∨ e = 3 ∨ (5 ≤ e ∧ e+2*q ≤ i+2) ∨ (i+1 ≤ e ∧ e ≤ 4*q)) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc.1,hc.2,h⟩))))))))))))

theorem row_case_13 (q i e : Nat) (hq : 3 ≤ q)
    (hc : i = 4*q) : Row q i e ↔ (e = 3 ∨ (5 ≤ e ∧ e ≤ 2*q+2) ∨ e = 3*q+1) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc,h⟩)))))))))))))

theorem row_case_14 (q i e : Nat) (hq : 3 ≤ q)
    (hc : i = 4*q+1) : Row q i e ↔ (3*q+2 ≤ e ∧ e ≤ 4*q) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hc,h⟩))))))))))))))

theorem row_case_15 (q i e : Nat) (hq : 3 ≤ q)
    (hc : i = 4*q+2) : Row q i e ↔ (e = 1 ∨ (5 ≤ e ∧ e ≤ q+2)) := by
  unfold Row
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  · intro h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hc,h⟩)))))))))))))))

theorem coatom_partition (q i : Nat) (hq : 3 ≤ q)
    (hlo : 1 ≤ i) (hhi : i ≤ 4*q) : (i = 1) ∨ (i = 2) ∨ (i = 3) ∨ (i = 4) ∨ (5 ≤ i ∧ i ≤ q+2) ∨ (q+3 ≤ i ∧ i ≤ 2*q) ∨ (i = 2*q+1) ∨ (i = 2*q+2) ∨ (i = 2*q+3) ∨ (2*q+4 ≤ i ∧ i ≤ 3*q) ∨ (i = 3*q+1) ∨ (3*q+2 ≤ i ∧ i+1 ≤ 4*q) ∨ (i = 4*q) := by omega

theorem row_in_filter (q : Nat) (hq : 3 ≤ q) (i e : Nat)
    (hi : i < 4*q+3) (he1 : 1 ≤ e) (he2 : e ≤ 4*q)
    (h : Row q i e) : FilterRow q i e := by
  unfold Row at h
  unfold FilterRow
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

theorem coatoms_separated (q : Nat) (hq : 3 ≤ q) (i j : Nat)
    (hi1 : 1 ≤ i) (hi2 : i ≤ 4*q) (hj1 : 1 ≤ j) (hj2 : j ≤ 4*q)
    (hne : i ≠ j) : Row q i j ∨ Row q j i := by
  rcases coatom_partition q i hq hi1 hi2 with hi1 | hi2 | hi3 | hi4 | hi5 | hi6 | hi7 | hi8 | hi9 | hi10 | hi11 | hi12 | hi13
  · rw [row_case_1 q i j hq hi1]
    rcases coatom_partition q j hq hj1 hj2 with hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7 | hj8 | hj9 | hj10 | hj11 | hj12 | hj13
    · rw [row_case_1 q j i hq hj1]
      omega
    · rw [row_case_2 q j i hq hj2]
      omega
    · rw [row_case_3 q j i hq hj3]
      omega
    · rw [row_case_4 q j i hq hj4]
      omega
    · rw [row_case_5 q j i hq hj5]
      omega
    · rw [row_case_6 q j i hq hj6]
      omega
    · rw [row_case_7 q j i hq hj7]
      omega
    · rw [row_case_8 q j i hq hj8]
      omega
    · rw [row_case_9 q j i hq hj9]
      omega
    · rw [row_case_10 q j i hq hj10]
      omega
    · rw [row_case_11 q j i hq hj11]
      omega
    · rw [row_case_12 q j i hq hj12]
      omega
    · rw [row_case_13 q j i hq hj13]
      omega
  · rw [row_case_2 q i j hq hi2]
    rcases coatom_partition q j hq hj1 hj2 with hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7 | hj8 | hj9 | hj10 | hj11 | hj12 | hj13
    · rw [row_case_1 q j i hq hj1]
      omega
    · rw [row_case_2 q j i hq hj2]
      omega
    · rw [row_case_3 q j i hq hj3]
      omega
    · rw [row_case_4 q j i hq hj4]
      omega
    · rw [row_case_5 q j i hq hj5]
      omega
    · rw [row_case_6 q j i hq hj6]
      omega
    · rw [row_case_7 q j i hq hj7]
      omega
    · rw [row_case_8 q j i hq hj8]
      omega
    · rw [row_case_9 q j i hq hj9]
      omega
    · rw [row_case_10 q j i hq hj10]
      omega
    · rw [row_case_11 q j i hq hj11]
      omega
    · rw [row_case_12 q j i hq hj12]
      omega
    · rw [row_case_13 q j i hq hj13]
      omega
  · rw [row_case_3 q i j hq hi3]
    rcases coatom_partition q j hq hj1 hj2 with hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7 | hj8 | hj9 | hj10 | hj11 | hj12 | hj13
    · rw [row_case_1 q j i hq hj1]
      omega
    · rw [row_case_2 q j i hq hj2]
      omega
    · rw [row_case_3 q j i hq hj3]
      omega
    · rw [row_case_4 q j i hq hj4]
      omega
    · rw [row_case_5 q j i hq hj5]
      omega
    · rw [row_case_6 q j i hq hj6]
      omega
    · rw [row_case_7 q j i hq hj7]
      omega
    · rw [row_case_8 q j i hq hj8]
      omega
    · rw [row_case_9 q j i hq hj9]
      omega
    · rw [row_case_10 q j i hq hj10]
      omega
    · rw [row_case_11 q j i hq hj11]
      omega
    · rw [row_case_12 q j i hq hj12]
      omega
    · rw [row_case_13 q j i hq hj13]
      omega
  · rw [row_case_4 q i j hq hi4]
    rcases coatom_partition q j hq hj1 hj2 with hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7 | hj8 | hj9 | hj10 | hj11 | hj12 | hj13
    · rw [row_case_1 q j i hq hj1]
      omega
    · rw [row_case_2 q j i hq hj2]
      omega
    · rw [row_case_3 q j i hq hj3]
      omega
    · rw [row_case_4 q j i hq hj4]
      omega
    · rw [row_case_5 q j i hq hj5]
      omega
    · rw [row_case_6 q j i hq hj6]
      omega
    · rw [row_case_7 q j i hq hj7]
      omega
    · rw [row_case_8 q j i hq hj8]
      omega
    · rw [row_case_9 q j i hq hj9]
      omega
    · rw [row_case_10 q j i hq hj10]
      omega
    · rw [row_case_11 q j i hq hj11]
      omega
    · rw [row_case_12 q j i hq hj12]
      omega
    · rw [row_case_13 q j i hq hj13]
      omega
  · rw [row_case_5 q i j hq hi5]
    rcases coatom_partition q j hq hj1 hj2 with hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7 | hj8 | hj9 | hj10 | hj11 | hj12 | hj13
    · rw [row_case_1 q j i hq hj1]
      omega
    · rw [row_case_2 q j i hq hj2]
      omega
    · rw [row_case_3 q j i hq hj3]
      omega
    · rw [row_case_4 q j i hq hj4]
      omega
    · rw [row_case_5 q j i hq hj5]
      omega
    · rw [row_case_6 q j i hq hj6]
      omega
    · rw [row_case_7 q j i hq hj7]
      omega
    · rw [row_case_8 q j i hq hj8]
      omega
    · rw [row_case_9 q j i hq hj9]
      omega
    · rw [row_case_10 q j i hq hj10]
      omega
    · rw [row_case_11 q j i hq hj11]
      omega
    · rw [row_case_12 q j i hq hj12]
      omega
    · rw [row_case_13 q j i hq hj13]
      omega
  · rw [row_case_6 q i j hq hi6]
    rcases coatom_partition q j hq hj1 hj2 with hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7 | hj8 | hj9 | hj10 | hj11 | hj12 | hj13
    · rw [row_case_1 q j i hq hj1]
      omega
    · rw [row_case_2 q j i hq hj2]
      omega
    · rw [row_case_3 q j i hq hj3]
      omega
    · rw [row_case_4 q j i hq hj4]
      omega
    · rw [row_case_5 q j i hq hj5]
      omega
    · rw [row_case_6 q j i hq hj6]
      omega
    · rw [row_case_7 q j i hq hj7]
      omega
    · rw [row_case_8 q j i hq hj8]
      omega
    · rw [row_case_9 q j i hq hj9]
      omega
    · rw [row_case_10 q j i hq hj10]
      omega
    · rw [row_case_11 q j i hq hj11]
      omega
    · rw [row_case_12 q j i hq hj12]
      omega
    · rw [row_case_13 q j i hq hj13]
      omega
  · rw [row_case_7 q i j hq hi7]
    rcases coatom_partition q j hq hj1 hj2 with hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7 | hj8 | hj9 | hj10 | hj11 | hj12 | hj13
    · rw [row_case_1 q j i hq hj1]
      omega
    · rw [row_case_2 q j i hq hj2]
      omega
    · rw [row_case_3 q j i hq hj3]
      omega
    · rw [row_case_4 q j i hq hj4]
      omega
    · rw [row_case_5 q j i hq hj5]
      omega
    · rw [row_case_6 q j i hq hj6]
      omega
    · rw [row_case_7 q j i hq hj7]
      omega
    · rw [row_case_8 q j i hq hj8]
      omega
    · rw [row_case_9 q j i hq hj9]
      omega
    · rw [row_case_10 q j i hq hj10]
      omega
    · rw [row_case_11 q j i hq hj11]
      omega
    · rw [row_case_12 q j i hq hj12]
      omega
    · rw [row_case_13 q j i hq hj13]
      omega
  · rw [row_case_8 q i j hq hi8]
    rcases coatom_partition q j hq hj1 hj2 with hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7 | hj8 | hj9 | hj10 | hj11 | hj12 | hj13
    · rw [row_case_1 q j i hq hj1]
      omega
    · rw [row_case_2 q j i hq hj2]
      omega
    · rw [row_case_3 q j i hq hj3]
      omega
    · rw [row_case_4 q j i hq hj4]
      omega
    · rw [row_case_5 q j i hq hj5]
      omega
    · rw [row_case_6 q j i hq hj6]
      omega
    · rw [row_case_7 q j i hq hj7]
      omega
    · rw [row_case_8 q j i hq hj8]
      omega
    · rw [row_case_9 q j i hq hj9]
      omega
    · rw [row_case_10 q j i hq hj10]
      omega
    · rw [row_case_11 q j i hq hj11]
      omega
    · rw [row_case_12 q j i hq hj12]
      omega
    · rw [row_case_13 q j i hq hj13]
      omega
  · rw [row_case_9 q i j hq hi9]
    rcases coatom_partition q j hq hj1 hj2 with hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7 | hj8 | hj9 | hj10 | hj11 | hj12 | hj13
    · rw [row_case_1 q j i hq hj1]
      omega
    · rw [row_case_2 q j i hq hj2]
      omega
    · rw [row_case_3 q j i hq hj3]
      omega
    · rw [row_case_4 q j i hq hj4]
      omega
    · rw [row_case_5 q j i hq hj5]
      omega
    · rw [row_case_6 q j i hq hj6]
      omega
    · rw [row_case_7 q j i hq hj7]
      omega
    · rw [row_case_8 q j i hq hj8]
      omega
    · rw [row_case_9 q j i hq hj9]
      omega
    · rw [row_case_10 q j i hq hj10]
      omega
    · rw [row_case_11 q j i hq hj11]
      omega
    · rw [row_case_12 q j i hq hj12]
      omega
    · rw [row_case_13 q j i hq hj13]
      omega
  · rw [row_case_10 q i j hq hi10]
    rcases coatom_partition q j hq hj1 hj2 with hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7 | hj8 | hj9 | hj10 | hj11 | hj12 | hj13
    · rw [row_case_1 q j i hq hj1]
      omega
    · rw [row_case_2 q j i hq hj2]
      omega
    · rw [row_case_3 q j i hq hj3]
      omega
    · rw [row_case_4 q j i hq hj4]
      omega
    · rw [row_case_5 q j i hq hj5]
      omega
    · rw [row_case_6 q j i hq hj6]
      omega
    · rw [row_case_7 q j i hq hj7]
      omega
    · rw [row_case_8 q j i hq hj8]
      omega
    · rw [row_case_9 q j i hq hj9]
      omega
    · rw [row_case_10 q j i hq hj10]
      omega
    · rw [row_case_11 q j i hq hj11]
      omega
    · rw [row_case_12 q j i hq hj12]
      omega
    · rw [row_case_13 q j i hq hj13]
      omega
  · rw [row_case_11 q i j hq hi11]
    rcases coatom_partition q j hq hj1 hj2 with hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7 | hj8 | hj9 | hj10 | hj11 | hj12 | hj13
    · rw [row_case_1 q j i hq hj1]
      omega
    · rw [row_case_2 q j i hq hj2]
      omega
    · rw [row_case_3 q j i hq hj3]
      omega
    · rw [row_case_4 q j i hq hj4]
      omega
    · rw [row_case_5 q j i hq hj5]
      omega
    · rw [row_case_6 q j i hq hj6]
      omega
    · rw [row_case_7 q j i hq hj7]
      omega
    · rw [row_case_8 q j i hq hj8]
      omega
    · rw [row_case_9 q j i hq hj9]
      omega
    · rw [row_case_10 q j i hq hj10]
      omega
    · rw [row_case_11 q j i hq hj11]
      omega
    · rw [row_case_12 q j i hq hj12]
      omega
    · rw [row_case_13 q j i hq hj13]
      omega
  · rw [row_case_12 q i j hq hi12]
    rcases coatom_partition q j hq hj1 hj2 with hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7 | hj8 | hj9 | hj10 | hj11 | hj12 | hj13
    · rw [row_case_1 q j i hq hj1]
      omega
    · rw [row_case_2 q j i hq hj2]
      omega
    · rw [row_case_3 q j i hq hj3]
      omega
    · rw [row_case_4 q j i hq hj4]
      omega
    · rw [row_case_5 q j i hq hj5]
      omega
    · rw [row_case_6 q j i hq hj6]
      omega
    · rw [row_case_7 q j i hq hj7]
      omega
    · rw [row_case_8 q j i hq hj8]
      omega
    · rw [row_case_9 q j i hq hj9]
      omega
    · rw [row_case_10 q j i hq hj10]
      omega
    · rw [row_case_11 q j i hq hj11]
      omega
    · rw [row_case_12 q j i hq hj12]
      omega
    · rw [row_case_13 q j i hq hj13]
      omega
  · rw [row_case_13 q i j hq hi13]
    rcases coatom_partition q j hq hj1 hj2 with hj1 | hj2 | hj3 | hj4 | hj5 | hj6 | hj7 | hj8 | hj9 | hj10 | hj11 | hj12 | hj13
    · rw [row_case_1 q j i hq hj1]
      omega
    · rw [row_case_2 q j i hq hj2]
      omega
    · rw [row_case_3 q j i hq hj3]
      omega
    · rw [row_case_4 q j i hq hj4]
      omega
    · rw [row_case_5 q j i hq hj5]
      omega
    · rw [row_case_6 q j i hq hj6]
      omega
    · rw [row_case_7 q j i hq hj7]
      omega
    · rw [row_case_8 q j i hq hj8]
      omega
    · rw [row_case_9 q j i hq hj9]
      omega
    · rw [row_case_10 q j i hq hj10]
      omega
    · rw [row_case_11 q j i hq hj11]
      omega
    · rw [row_case_12 q j i hq hj12]
      omega
    · rw [row_case_13 q j i hq hj13]
      omega

theorem first_double_hole_separated (q : Nat) (hq : 3 ≤ q) (i : Nat)
    (hi1 : 1 ≤ i) (hi2 : i ≤ 4*q) :
    Row q i 1 ∨ Row q i 2 ∨ Row q (4*q+1) i := by
  rw [row_case_14 q (4*q+1) i hq rfl]
  rcases coatom_partition q i hq hi1 hi2 with hi1 | hi2 | hi3 | hi4 | hi5 | hi6 | hi7 | hi8 | hi9 | hi10 | hi11 | hi12 | hi13
  · rw [row_case_1 q i 1 hq hi1,row_case_1 q i 2 hq hi1]
    omega
  · rw [row_case_2 q i 1 hq hi2,row_case_2 q i 2 hq hi2]
    omega
  · rw [row_case_3 q i 1 hq hi3,row_case_3 q i 2 hq hi3]
    omega
  · rw [row_case_4 q i 1 hq hi4,row_case_4 q i 2 hq hi4]
    omega
  · rw [row_case_5 q i 1 hq hi5,row_case_5 q i 2 hq hi5]
    omega
  · rw [row_case_6 q i 1 hq hi6,row_case_6 q i 2 hq hi6]
    omega
  · rw [row_case_7 q i 1 hq hi7,row_case_7 q i 2 hq hi7]
    omega
  · rw [row_case_8 q i 1 hq hi8,row_case_8 q i 2 hq hi8]
    omega
  · rw [row_case_9 q i 1 hq hi9,row_case_9 q i 2 hq hi9]
    omega
  · rw [row_case_10 q i 1 hq hi10,row_case_10 q i 2 hq hi10]
    omega
  · rw [row_case_11 q i 1 hq hi11,row_case_11 q i 2 hq hi11]
    omega
  · rw [row_case_12 q i 1 hq hi12,row_case_12 q i 2 hq hi12]
    omega
  · rw [row_case_13 q i 1 hq hi13,row_case_13 q i 2 hq hi13]
    omega
theorem second_double_hole_separated (q : Nat) (hq : 3 ≤ q) (i : Nat)
    (hi1 : 1 ≤ i) (hi2 : i ≤ 4*q) :
    Row q i 3 ∨ Row q i 4 ∨ Row q (4*q+2) i := by
  rw [row_case_15 q (4*q+2) i hq rfl]
  rcases coatom_partition q i hq hi1 hi2 with hi1 | hi2 | hi3 | hi4 | hi5 | hi6 | hi7 | hi8 | hi9 | hi10 | hi11 | hi12 | hi13
  · rw [row_case_1 q i 3 hq hi1,row_case_1 q i 4 hq hi1]
    omega
  · rw [row_case_2 q i 3 hq hi2,row_case_2 q i 4 hq hi2]
    omega
  · rw [row_case_3 q i 3 hq hi3,row_case_3 q i 4 hq hi3]
    omega
  · rw [row_case_4 q i 3 hq hi4,row_case_4 q i 4 hq hi4]
    omega
  · rw [row_case_5 q i 3 hq hi5,row_case_5 q i 4 hq hi5]
    omega
  · rw [row_case_6 q i 3 hq hi6,row_case_6 q i 4 hq hi6]
    omega
  · rw [row_case_7 q i 3 hq hi7,row_case_7 q i 4 hq hi7]
    omega
  · rw [row_case_8 q i 3 hq hi8,row_case_8 q i 4 hq hi8]
    omega
  · rw [row_case_9 q i 3 hq hi9,row_case_9 q i 4 hq hi9]
    omega
  · rw [row_case_10 q i 3 hq hi10,row_case_10 q i 4 hq hi10]
    omega
  · rw [row_case_11 q i 3 hq hi11,row_case_11 q i 4 hq hi11]
    omega
  · rw [row_case_12 q i 3 hq hi12,row_case_12 q i 4 hq hi12]
    omega
  · rw [row_case_13 q i 3 hq hi13,row_case_13 q i 4 hq hi13]
    omega

end LuRazParametric
