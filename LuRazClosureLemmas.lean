import LuRazParametric

/-!
All-parameter lemmas used by the separate written closure-count argument.
This file deliberately does NOT claim a Lean cardinality theorem for the closure.
It verifies the reparametrized generator families, the interval description,
the no-two-gaps lemma, and the final polynomial arithmetic.
-/
namespace LuRazClosure

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def I (a b e : Nat) : Prop := a ≤ e ∧ e ≤ b
def g (q a : Nat) : Nat :=
  if a ≤ q+3 then 2*q+a-3 else 2*q+a-4
def beta (q p : Nat) : Nat :=
  if p ≤ q+1 then 2*q+p else 2*q+p-1
def P (q p : Nat) : Prop := 4 ≤ p ∧ p ≤ 2*q+1 ∧ p ≠ q+2
def JIndex (a : Nat) : Nat := if a=5 then 3 else a-1
def LIndex (q p : Nat) : Nat := beta q p-1
def LEnd (q p : Nat) : Nat := if p=q+3 then 4*q-1 else 4*q

theorem g_bounds (q a : Nat) (hq : 4 ≤ q)
    (ha : 5 ≤ a ∧ a ≤ 2*q+1) :
    2*q+2 ≤ g q a ∧ g q a ≤ 4*q-3 := by
  unfold g
  split <;> omega

theorem g_monotone (q a c : Nat) (hq : 4 ≤ q)
    (ha : 5 ≤ a) (hc : c ≤ 2*q+1) (hac : a ≤ c) :
    g q a ≤ g q c := by
  unfold g
  repeat first | omega | split

theorem g_surjective (q b : Nat) (hq : 4 ≤ q)
    (hb : 2*q+2 ≤ b ∧ b ≤ 4*q-3) :
    ∃ a, 5 ≤ a ∧ a ≤ 2*q+1 ∧ g q a=b := by
  by_cases h : b ≤ 3*q
  · refine ⟨b-2*q+3, ?_, ?_, ?_⟩
    · omega
    · omega
    · unfold g
      split <;> omega
  · refine ⟨b-2*q+4, ?_, ?_, ?_⟩
    · omega
    · omega
    · unfold g
      split <;> omega

theorem beta_bounds (q p : Nat) (hq : 4 ≤ q) (hp : P q p) :
    2*q+4 ≤ beta q p ∧ beta q p ≤ 4*q := by
  unfold P at hp
  unfold beta
  split <;> omega

theorem beta_strict (q p t : Nat) (hq : 4 ≤ q)
    (hp : P q p) (ht : P q t) (hpt : p < t) :
    beta q p < beta q t := by
  unfold P at hp ht
  unfold beta
  repeat first | omega | split

theorem beta_surjective (q b : Nat) (hq : 4 ≤ q)
    (hb : 2*q+4 ≤ b ∧ b ≤ 4*q) :
    ∃ p, P q p ∧ beta q p=b := by
  by_cases h : b ≤ 3*q+1
  · refine ⟨b-2*q, ?_, ?_⟩
    · unfold P; omega
    · unfold beta; split <;> omega
  · refine ⟨b-2*q+1, ?_, ?_⟩
    · unfold P; omega
    · unfold beta; split <;> omega

theorem J_is_source_row (q a e : Nat) (hq : 4 ≤ q)
    (ha : 5 ≤ a ∧ a ≤ 2*q+1) :
    LuRazParametric.Row q (JIndex a) e ↔
      e=1 ∨ e=4 ∨ I a (g q a) e := by
  by_cases h5 : a=5
  · subst a
    have hj : JIndex 5=3 := by decide
    rw [hj]
    rw [LuRazParametric.row_case_3 q 3 e (by omega) rfl]
    unfold g I
    split <;> omega
  · unfold JIndex
    rw [if_neg h5]
    by_cases h : a ≤ q+3
    · rw [LuRazParametric.row_case_5 q (a-1) e (by omega) (by omega)]
      unfold g I
      split <;> omega
    · rw [LuRazParametric.row_case_6 q (a-1) e (by omega) (by omega)]
      unfold g I
      split <;> omega

theorem L_is_source_row (q p e : Nat) (hq : 4 ≤ q)
    (hp : P q p) :
    LuRazParametric.Row q (LIndex q p) e ↔
      e=2 ∨ e=3 ∨ I 5 p e ∨ I (beta q p) (LEnd q p) e := by
  unfold P at hp
  by_cases h4 : p=4
  · subst p
    have hi : LIndex q 4 = 2*q+3 := by unfold LIndex beta; split <;> omega
    rw [hi, LuRazParametric.row_case_9 q (2*q+3) e (by omega) rfl]
    unfold I beta LEnd
    repeat first | omega | split
  · by_cases h : p ≤ q+1
    · have hi : LIndex q p = 2*q+p-1 := by unfold LIndex beta; split <;> omega
      rw [hi, LuRazParametric.row_case_10 q (2*q+p-1) e (by omega) (by omega)]
      unfold I beta LEnd
      repeat first | omega | split
    · by_cases he : p=q+3
      · subst p
        have hi : LIndex q (q+3) = 3*q+1 := by unfold LIndex beta; split <;> omega
        rw [hi, LuRazParametric.row_case_11 q (3*q+1) e (by omega) rfl]
        unfold I beta LEnd
        repeat first | omega | split
      · have hi : LIndex q p = 2*q+p-2 := by unfold LIndex beta; split <;> omega
        rw [hi, LuRazParametric.row_case_12 q (2*q+p-2) e (by omega) (by omega)]
        unfold I beta LEnd
        repeat first | omega | split

/-- A left gap forces the middle interval to touch the right suffix.
    Hence a J interval and any nonempty L union cannot leave two gaps. -/
theorem no_two_gaps (q p a : Nat) (hq : 4 ≤ q)
    (hp : P q p) (ha : 5 ≤ a ∧ a ≤ 2*q+1)
    (hgap : p+2 ≤ a) : beta q p ≤ g q a+1 := by
  unfold P at hp
  unfold beta g
  repeat first | omega | split

theorem two_intervals (a b c d k e : Nat)
    (ha : a ≤ k ∧ k ≤ b) (hc : c ≤ k ∧ k ≤ d) :
    (I a b e ∨ I c d e) ↔ I (min a c) (max b d) e := by
  unfold I
  omega

def JReachable (q a b : Nat) : Prop :=
  5 ≤ a ∧ a ≤ 2*q+1 ∧ 2*q+2 ≤ b ∧ b ≤ 4*q-3 ∧ g q a ≤ b

theorem J_join_closed (q a b c d e : Nat) (hq : 4 ≤ q)
    (hab : JReachable q a b) (hcd : JReachable q c d) :
    (I a b e ∨ I c d e) ↔ I (min a c) (max b d) e := by
  unfold JReachable at hab hcd
  apply two_intervals a b c d (2*q+1) e <;> omega

theorem J_pair_attains (q a b : Nat) (hq : 4 ≤ q)
    (hab : JReachable q a b) :
    ∃ c, (5 ≤ c ∧ c ≤ 2*q+1) ∧
      ∀ e, (I a (g q a) e ∨ I c (g q c) e) ↔ I a b e := by
  have ha := hab.1
  have hau := hab.2.1
  have hb := hab.2.2.1
  have hbu := hab.2.2.2.1
  have hag := hab.2.2.2.2
  by_cases heq : b=g q a
  · refine ⟨a, ⟨ha,hau⟩, ?_⟩
    intro e
    rw [heq]
    simp only [or_self]
  · obtain ⟨c,hc,hcu,hcg⟩ := g_surjective q b hq ⟨hb,hbu⟩
    have hac : a ≤ c := by
      apply Classical.byContradiction
      intro h
      have hca : c ≤ a := by omega
      have hm := g_monotone q c a hq hc hau hca
      omega
    refine ⟨c, ⟨hc,hcu⟩, ?_⟩
    intro e
    have hga := g_bounds q a hq ⟨ha,hau⟩
    have hgc := g_bounds q c hq ⟨hc,hcu⟩
    unfold I
    omega

/- Counts below are doubled, avoiding integer division. This verifies the
   arithmetic of the written classification, NOT the classification itself. -/
theorem scale_square (q c : Int) : q*(q*c)=c*(q*q) := by
  rw [← Int.mul_assoc, Int.mul_comm (q*q) c]

def counts2 (q : Int) : List Int :=
  [2,4,2,2,4,10, 2*(2*q*q-q-3), 3*q*q+7*q-14,
   2*(3*q*q-5*q+2),12,2*(9*q-10),2*(10*q-16),
   2*(6*q-6),2*(5*q*q-5*q+1)]

theorem fourteen_counts_sum (q : Int) :
    (counts2 q).sum = 23*q*q+35*q-42 := by
  unfold counts2
  simp only [List.sum_cons,List.sum_nil]
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul]
  simp only [Int.mul_assoc]
  omega

theorem class15_partition_arithmetic (q : Int) :
    2*((3*q-2)+(6*q-9)+(2*q-2)+(2*q-4)+
      (2*q-5)*(q-2)+1+(2*q-3)*(q-1)+(q-2)*(q-2)) =
      2*(5*q*q-5*q+1) := by
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul]
  simp only [Int.mul_assoc]
  omega

theorem x_substitution (x : Int) :
    23*(x+1)*(x+1)+35*(x+1)-42 = 23*x*x+81*x+16 := by
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul]
  simp only [Int.mul_assoc]
  omega

theorem n_substitution (q : Int) :
    23*(4*q)*(4*q)+140*(4*q)-672 = 16*(23*q*q+35*q-42) := by
  have h : q*(4*q) = 4*(q*q) := Int.mul_left_comm q 4 q
  simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc,h]
  omega

end LuRazClosure
