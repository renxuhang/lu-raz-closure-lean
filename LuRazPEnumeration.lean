import LuRazCore23Unique
import EnumerationCounting

namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def rankP (q k : Nat) : Nat := if k<q-2 then k+4 else k+5
def enumP (q n : Nat) : List Nat := (List.range n).map (rankP q)

theorem rankP_strict (q i j : Nat) (hij : i<j) : rankP q i<rankP q j := by
  unfold rankP
  repeat first | omega | split

theorem rankP_injective (q i j : Nat) (heq : rankP q i=rankP q j) : i=j := by
  by_cases h : i<j
  · have := rankP_strict q i j h; omega
  by_cases h : j<i
  · have := rankP_strict q j i h; omega
  omega

theorem rankP_le (q i j : Nat) : rankP q i≤rankP q j ↔ i≤j := by
  unfold rankP
  repeat first | omega | split

theorem rankP_valid (q k : Nat) (hq : 4≤q) (hk : k<2*q-3) : P q (rankP q k) := by
  unfold P rankP
  split <;> omega

theorem rankP_surjective (q p : Nat) (hq : 4≤q) (hp : P q p) :
    ∃ k, k<2*q-3 ∧ rankP q k=p := by
  unfold P at hp
  by_cases h : p≤q+1
  · refine ⟨p-4,by omega,?_⟩
    unfold rankP
    split <;> omega
  · refine ⟨p-5,by omega,?_⟩
    unfold rankP
    split <;> omega

theorem rankP_low (q k : Nat) (hq : 4≤q) :
    k<2*q-5 ↔ (k<2*q-3 ∧ rankP q k≤2*q-1) := by
  unfold rankP
  split <;> omega

theorem rankP_exception (q : Nat) (hq : 4≤q) : rankP q (q-2)=q+3 := by
  unfold rankP
  split <;> omega

theorem enumP_nodup (q n : Nat) : (enumP q n).Nodup :=
  nodup_map_injective (rankP q) (rankP_injective q) _ List.nodup_range

theorem enumP_exact (q : Nat) (hq : 4≤q) (p : Nat) :
    p ∈ enumP q (2*q-3) ↔ P q p := by
  constructor
  · rintro hp
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    exact rankP_valid q k hq (List.mem_range.mp hk)
  · intro hp
    obtain ⟨k,hk,heq⟩ := rankP_surjective q p hq hp
    exact List.mem_map.mpr ⟨k,List.mem_range.mpr hk,heq⟩

theorem enumP_low_exact (q : Nat) (hq : 4≤q) (p : Nat) :
    p ∈ enumP q (2*q-5) ↔ P q p ∧ p≤2*q-1 := by
  constructor
  · intro hp
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    have hb := (rankP_low q k hq).mp (List.mem_range.mp hk)
    exact ⟨rankP_valid q k hq hb.1,hb.2⟩
  · rintro ⟨hp,hpl⟩
    obtain ⟨k,hk,heq⟩ := rankP_surjective q p hq hp
    have hkl : k<2*q-5 := (rankP_low q k hq).mpr ⟨hk,by rw [heq]; exact hpl⟩
    exact List.mem_map.mpr ⟨k,List.mem_range.mpr hkl,heq⟩

theorem filter_ne_absent (l : List Nat) (x : Nat) (hx : x ∉ l) :
    l.filter (fun a => decide (a≠x))=l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    have hax : a≠x := by intro h; subst a; exact hx (by simp)
    have hxr : x ∉ rest := by intro h; exact hx (by simp only [List.mem_cons]; exact Or.inr h)
    simpa [hax] using congrArg (fun k => a::k) (ih hxr)

theorem filter_ne_length (l : List Nat) (hl : l.Nodup) (x : Nat) (hx : x ∈ l) :
    (l.filter (fun a => decide (a≠x))).length+1=l.length := by
  induction l with
  | nil => exact False.elim (List.not_mem_nil hx)
  | cons a rest ih =>
    have hc := List.nodup_cons.mp hl
    by_cases hax : a=x
    · subst a
      simp [filter_ne_absent rest x hc.1]
      intro a ha heq
      subst a
      exact hc.1 ha
    · have hxr : x ∈ rest := by
        rcases List.mem_cons.mp hx with h | h
        · exact False.elim (hax h.symm)
        · exact h
      have hi := ih hc.2 hxr
      simp [List.filter_cons,hax] <;> omega

end LuRazClosure
