import LuRazTotalClosure
import LuRazResults

/-! Statement correspondence for the explicitly completed Lu--Raz construction.
The frequency hypothesis below is the printed assertion in Section 3, not a
claim that an author or prize reviewer has approved this reconstruction. -/
namespace LuRazSubmission
open LuRazClosure LuRazCounting LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem nonempty_witness {α : Type} (l : List α) (h : l≠[]) : ∃ a, a∈l := by
  cases l with
  | nil => exact (h rfl).elim
  | cons a l => exact ⟨a,by simp⟩

theorem sumTo_difference_at_one (f g : Nat → Int) (m n : Nat)
    (hm : m<n) (hother : ∀ i, i<n → i≠m → f i=g i) :
    sumTo f n-sumTo g n=f m-g m := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hmn : m=n
    · subst m
      have hh : sumTo f n=sumTo g n := sumTo_congr n (fun i hi => hother i (by omega) (by omega))
      simp only [sumTo,hh]
      omega
    · have hh := ih (by omega) (fun i hi => hother i (by omega))
      have hn := hother n (by omega) (by omega)
      simp only [sumTo,hn]
      omega

/-- The other printed rows and the printed equal-frequency condition force
    the omitted row, coordinate by coordinate on the stated ground set. -/
theorem omitted_row_forced (q : Nat) (hq : 3≤q) (A : Nat → Nat → Prop)
    (hrows : ∀ i, i<4*q+3 → i≠2*q+1 → ∀ e, 1≤e → e≤4*q →
      (A i e ↔ Row q i e))
    (hfreq : ∀ e, 1≤e → e≤4*q →
      sumTo (fun i => mark (A i e)) (4*q+3)=2*(q:Int)+1)
    (e : Nat) (he1 : 1≤e) (he2 : e≤4*q) :
    A (2*q+1) e ↔ e=2 ∨ e=4 ∨ (2*q+2≤e ∧ e+2≤4*q) := by
  have hd := sumTo_difference_at_one (fun i => mark (A i e))
    (weight q e) (2*q+1) (4*q+3) (by omega)
    (fun i hi hn => mark_congr (hrows i hi hn e he1 he2))
  have ha := hfreq e he1 he2
  have hb := exact_frequencies q e hq he1 he2
  have hm : mark (A (2*q+1) e)=mark (Row q (2*q+1) e) := by
    rw [ha,hb] at hd
    unfold weight at hd
    omega
  have heq : A (2*q+1) e ↔ Row q (2*q+1) e := by
    classical
    by_cases hA : A (2*q+1) e
    · by_cases hR : Row q (2*q+1) e
      · exact ⟨fun _ => hR,fun _ => hA⟩
      · simp only [mark,hA,hR,ite_true,ite_false] at hm
        omega
    · by_cases hR : Row q (2*q+1) e
      · simp only [mark,hA,hR,ite_true,ite_false] at hm
        omega
      · exact ⟨fun h => (hA h).elim,fun h => (hR h).elim⟩
  exact heq.trans (row_case_7 q (2*q+1) e hq rfl)

theorem balanced_completion_unique (q : Nat) (hq : 3≤q) (A : Nat → Nat → Prop)
    (hrows : ∀ i, i<4*q+3 → i≠2*q+1 → ∀ e, 1≤e → e≤4*q →
      (A i e ↔ Row q i e))
    (hfreq : ∀ e, 1≤e → e≤4*q →
      sumTo (fun i => mark (A i e)) (4*q+3)=2*(q:Int)+1) :
    ∀ i, i<4*q+3 → ∀ e, 1≤e → e≤4*q → (A i e ↔ Row q i e) := by
  intro i hi e he1 he2
  by_cases hm : i=2*q+1
  · subst i
    exact (omitted_row_forced q hq A hrows hfreq e he1 he2).trans
      (row_case_7 q (2*q+1) e hq rfl).symm
  · exact hrows i hi hm e he1 he2

/-- Arbitrary nonempty subfamilies, represented by predicates on all row indices. -/
def NonemptySubfamilyUnion (q : Nat) (T : Fin (4*q) → Prop) : Prop :=
  ∃ P : Fin (4*q+3) → Prop, (∃ i, P i) ∧
    ∀ e, (∃ i, P i ∧ S q i e) ↔ T e

/-- This version also permits the empty subfamily. -/
def SubfamilyUnion (q : Nat) (T : Fin (4*q) → Prop) : Prop :=
  ∃ P : Fin (4*q+3) → Prop, ∀ e, (∃ i, P i ∧ S q i e) ↔ T e

theorem nonempty_subfamily_iff (q : Nat) (T : Fin (4*q) → Prop) :
    NonemptySubfamilyUnion q T ↔ FinGenerated q T := by
  classical
  constructor
  · rintro ⟨P,⟨i,hi⟩,he⟩
    let l := (List.finRange (4*q+3)).filter (fun j => decide (P j))
    have hmem : ∀ j, j∈l ↔ P j := by intro j; simp [l]
    refine ⟨l,List.ne_nil_of_mem ((hmem i).mpr hi),?_⟩
    intro e
    exact (exists_congr fun j => and_congr (hmem j) Iff.rfl).trans (he e)
  · rintro ⟨l,hl,he⟩
    obtain ⟨i,hi⟩ := nonempty_witness l hl
    exact ⟨fun j => j∈l,⟨i,hi⟩,he⟩

theorem subfamily_union_iff (q : Nat) (T : Fin (4*q) → Prop) :
    SubfamilyUnion q T ↔ T=(fun _ => False) ∨ FinGenerated q T := by
  classical
  constructor
  · rintro ⟨P,he⟩
    by_cases hp : ∃ i, P i
    · exact Or.inr ((nonempty_subfamily_iff q T).mp ⟨P,hp,he⟩)
    · left
      funext e
      apply propext
      constructor
      · intro hT
        obtain ⟨i,hi,_⟩ := (he e).mpr hT
        exact hp ⟨i,hi⟩
      · intro h; exact h.elim
  · rintro (h | h)
    · subst T
      refine ⟨fun _ => False,?_⟩
      intro e
      simp
    · obtain ⟨P,_,he⟩ := (nonempty_subfamily_iff q T).mpr h
      exact ⟨P,he⟩

theorem source_row_nonempty (q : Nat) (hq : 3≤q) (i : Fin (4*q+3)) :
    ∃ e, S q i e := by
  classical
  have hl := minimum_size_lower q hq i
  have hpos : 0<setSize q i := by omega
  unfold setSize at hpos
  have hne : ((List.finRange (4*q)).filter (fun e => decide (S q i e)))≠[] := by
    intro hh
    simp only [hh,List.length_nil] at hpos
    omega
  obtain ⟨e,he⟩ := nonempty_witness _ hne
  exact ⟨e,of_decide_eq_true (List.mem_filter.mp he).2⟩

theorem empty_not_generated (q : Nat) (hq : 3≤q) :
    ¬FinGenerated q (fun _ => False) := by
  rintro ⟨l,hl,he⟩
  obtain ⟨i,hi⟩ := nonempty_witness l hl
  obtain ⟨e,hie⟩ := source_row_nonempty q hq i
  exact (he e).mp ⟨i,hi,hie⟩

/-- The original x>=5 range follows, with ordinary subfamily semantics. -/
theorem nonempty_count_in_paper_range (x : Nat) (hx : 5≤x) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ NonemptySubfamilyUnion (x+1) T) ∧
      l.length=(23*x*x+81*x+16)/2 := by
  obtain ⟨l,hn,he,hl⟩ := closure_cardinality_for_every_x x (by omega)
  exact ⟨l,hn,fun T => (he T).trans (nonempty_subfamily_iff (x+1) T).symm,hl⟩

/-- Including the empty union adds exactly one distinct set, for every x>=3. -/
theorem including_empty_count (x : Nat) (hx : 3≤x) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ SubfamilyUnion (x+1) T) ∧
      l.length=(23*x*x+81*x+18)/2 := by
  classical
  obtain ⟨l,hn,he,hl⟩ := closure_cardinality_for_every_x x hx
  refine ⟨(fun _ => False)::l,?_,?_,?_⟩
  · rw [List.nodup_cons]
    exact ⟨fun hm => empty_not_generated (x+1) (by omega) ((he _).mp hm),hn⟩
  · intro T
    rw [List.mem_cons,he,subfamily_union_iff]
  · simp only [List.length_cons]
    omega

/-- The printed n-polynomial with all denominators cleared: n=4q. -/
theorem nonempty_count_n_scaled (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ NonemptySubfamilyUnion q T) ∧
      32*(l.length:Int)=23*(4*(q:Int))*(4*(q:Int))+140*(4*(q:Int))-672 := by
  obtain ⟨l,hn,he,hl⟩ := closure_finite_cardinality q hq
  refine ⟨l,hn,fun T => (he T).trans (nonempty_subfamily_iff q T).symm,?_⟩
  rw [n_substitution,←hl]
  omega

/-- A nonempty union in any proposed completion of the printed source table. -/
def CompletionUnion (q : Nat) (A : Nat → Nat → Prop) (T : Fin (4*q) → Prop) : Prop :=
  ∃ P : Fin (4*q+3) → Prop, (∃ i, P i) ∧
    ∀ e, (∃ i, P i ∧ A i.val (e.val+1)) ↔ T e

/-- No author-intent axiom is needed: every completion with the printed rows
    and printed equal column frequencies has the same nonempty closure count. -/
theorem every_balanced_completion_count (x : Nat) (hx : 5≤x) (A : Nat → Nat → Prop)
    (hrows : ∀ i, i<4*(x+1)+3 → i≠2*(x+1)+1 → ∀ e, 1≤e → e≤4*(x+1) →
      (A i e ↔ Row (x+1) i e))
    (hfreq : ∀ e, 1≤e → e≤4*(x+1) →
      sumTo (fun i => mark (A i e)) (4*(x+1)+3)=2*((x+1:Int))+1) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ CompletionUnion (x+1) A T) ∧
      l.length=(23*x*x+81*x+16)/2 := by
  have hu := balanced_completion_unique (x+1) (by omega) A hrows hfreq
  obtain ⟨l,hn,he,hl⟩ := nonempty_count_in_paper_range x hx
  refine ⟨l,hn,?_,hl⟩
  intro T
  rw [he]
  constructor
  · rintro ⟨P,hp,hT⟩
    refine ⟨P,hp,?_⟩
    intro e
    have hi : ∀ i : Fin (4*(x+1)+3),
        S (x+1) i e ↔ A i.val (e.val+1) := by
      intro i
      exact (hu i.val i.isLt (e.val+1) (by omega) (by have := e.isLt; omega)).symm
    exact (exists_congr fun i => and_congr Iff.rfl (hi i)).symm.trans (hT e)
  · rintro ⟨P,hp,hT⟩
    refine ⟨P,hp,?_⟩
    intro e
    have hi : ∀ i : Fin (4*(x+1)+3),
        S (x+1) i e ↔ A i.val (e.val+1) := by
      intro i
      exact (hu i.val i.isLt (e.val+1) (by omega) (by have := e.isLt; omega)).symm
    exact (exists_congr fun i => and_congr Iff.rfl (hi i)).trans (hT e)

end LuRazSubmission
