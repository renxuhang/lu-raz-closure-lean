import LuRazFiniteClosure

namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def FinCore14 (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) : Prop :=
  T ⟨0,by omega⟩ ∧ ¬T ⟨1,by omega⟩ ∧ ¬T ⟨2,by omega⟩ ∧ T ⟨3,by omega⟩

def FinCore23 (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) : Prop :=
  ¬T ⟨0,by omega⟩ ∧ T ⟨1,by omega⟩ ∧ T ⟨2,by omega⟩ ∧ ¬T ⟨3,by omega⟩

theorem lift_at (q : Nat) (T : Fin (4*q) → Prop) (k : Nat) (hk : 1≤k ∧ k≤4*q) :
    Lift q T k ↔ T ⟨k-1,by omega⟩ := by
  constructor
  · rintro ⟨_,h⟩; exact h
  · intro h; exact ⟨hk,h⟩

theorem fin_core14_iff (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) :
    Core14 (Lift q T) ↔ FinCore14 q hq T := by
  unfold Core14 FinCore14
  rw [lift_at q T 1 (by omega),lift_at q T 2 (by omega),
      lift_at q T 3 (by omega),lift_at q T 4 (by omega)]

theorem fin_core23_iff (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) :
    Core23 (Lift q T) ↔ FinCore23 q hq T := by
  unfold Core23 FinCore23
  rw [lift_at q T 1 (by omega),lift_at q T 2 (by omega),
      lift_at q T 3 (by omega),lift_at q T 4 (by omega)]

/-- Exact count in the nonempty union closure of the original Fin-indexed S. -/
theorem core14_finite_for_every_x (x : Nat) (hx : 3≤x) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated (x+1) T ∧ FinCore14 (x+1) (by omega) T) ∧
      (l.length : Int)=3*(x:Int)*(x:Int)+(x:Int) := by
  obtain ⟨l,hn,he,hl⟩ := core14_for_every_x x hx
  have ht := transfer_enumeration (x+1) (by omega) Core14 l hn he
  refine ⟨l.map (Restrict (x+1)),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (fin_core14_iff (x+1) (by omega) T))
  · rw [List.length_map]
    exact hl

theorem core23_finite_for_every_x (x : Nat) (hx : 3≤x) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated (x+1) T ∧ FinCore23 (x+1) (by omega) T) ∧
      (l.length : Int)=2*(x:Int)*(x:Int)+3*(x:Int)-2 := by
  obtain ⟨l,hn,he,hl⟩ := core23_for_every_x x hx
  have ht := transfer_enumeration (x+1) (by omega) Core23 l hn he
  refine ⟨l.map (Restrict (x+1)),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (fin_core23_iff (x+1) (by omega) T))
  · rw [List.length_map]
    exact hl

/-- The two proved classes are disjoint; their union has the summed cardinality. -/
theorem two_quadratic_classes (x : Nat) (hx : 3≤x) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated (x+1) T ∧
        (FinCore14 (x+1) (by omega) T ∨ FinCore23 (x+1) (by omega) T)) ∧
      (l.length : Int)=5*(x:Int)*(x:Int)+4*(x:Int)-2 := by
  obtain ⟨a,ha,hea,hla⟩ := core14_finite_for_every_x x hx
  obtain ⟨b,hb,heb,hlb⟩ := core23_finite_for_every_x x hx
  refine ⟨a++b,?_,?_,?_⟩
  · apply List.nodup_append.mpr
    refine ⟨ha,hb,?_⟩
    intro R hR T hT heq
    subst T
    exact ((heb R).mp hT).2.1 ((hea R).mp hR).2.1
  · intro T
    rw [List.mem_append,hea,heb]
    constructor
    · rintro (⟨hg,hc⟩ | ⟨hg,hc⟩)
      · exact ⟨hg,Or.inl hc⟩
      · exact ⟨hg,Or.inr hc⟩
    · rintro ⟨hg,hc⟩
      rcases hc with h | h
      · exact Or.inl ⟨hg,h⟩
      · exact Or.inr ⟨hg,h⟩
  · rw [List.length_append,Int.natCast_add,hla,hlb]
    simp only [Int.mul_assoc]
    omega

end LuRazClosure
