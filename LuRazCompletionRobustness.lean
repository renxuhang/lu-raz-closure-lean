import LuRazMixedResults

namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Replace the source's omitted row by an arbitrary predicate M. -/
def VariantRow (q : Nat) (M : Nat → Prop) (i e : Nat) : Prop :=
  if i=2*q+1 then M e else LuRazParametric.Row q i e

def VariantGenerated (q : Nat) (M R : Nat → Prop) : Prop :=
  ∃ l : List Nat, l≠[] ∧ (∀ i∈l, i≤4*q+2) ∧
    ∀ e, ListUnion (VariantRow q M) l e ↔ R e

/-- A generator containing an excluded coordinate cannot affect the target class. -/
theorem variant_avoiding_coordinate (q c : Nat) (M R : Nat → Prop)
    (hold : LuRazParametric.Row q (2*q+1) c) (hnew : M c) (hnot : ¬R c) :
    VariantGenerated q M R ↔ Generated q R := by
  constructor
  · rintro ⟨l,hne,hvalid,heq⟩
    have hi : ∀ i∈l, i≠2*q+1 := by
      intro i him hieq
      subst i
      have hh : VariantRow q M (2*q+1) c := by simpa [VariantRow] using hnew
      exact hnot ((heq c).mp ⟨2*q+1,him,hh⟩)
    refine ⟨l,hne,hvalid,?_⟩
    intro e
    have hrows : ∀ i∈l, ∀ e, LuRazParametric.Row q i e ↔ VariantRow q M i e := by
      intro i him e
      simp only [VariantRow,hi i him,ite_false]
    exact (listUnion_congr _ _ l hrows e).trans (heq e)
  · rintro ⟨l,hne,hvalid,heq⟩
    have hi : ∀ i∈l, i≠2*q+1 := by
      intro i him hieq
      subst i
      exact hnot ((heq c).mp ⟨2*q+1,him,hold⟩)
    refine ⟨l,hne,hvalid,?_⟩
    intro e
    have hrows : ∀ i∈l, ∀ e, VariantRow q M i e ↔ LuRazParametric.Row q i e := by
      intro i him e
      simp only [VariantRow,hi i him,ite_false]
    exact (listUnion_congr _ _ l hrows e).trans (heq e)

theorem variant_core14_iff (q : Nat) (hq : 4≤q) (M R : Nat → Prop) (hM : M 2) :
    (VariantGenerated q M R ∧ Core14 R) ↔ (Generated q R ∧ Core14 R) := by
  have hold : LuRazParametric.Row q (2*q+1) 2 :=
    (LuRazParametric.row_case_7 q (2*q+1) 2 (by omega) rfl).mpr (by omega)
  constructor
  · rintro ⟨hg,hc⟩
    exact ⟨(variant_avoiding_coordinate q 2 M R hold hM hc.2.1).mp hg,hc⟩
  · rintro ⟨hg,hc⟩
    exact ⟨(variant_avoiding_coordinate q 2 M R hold hM hc.2.1).mpr hg,hc⟩

theorem variant_core23_iff (q : Nat) (hq : 4≤q) (M R : Nat → Prop) (hM : M 4) :
    (VariantGenerated q M R ∧ Core23 R) ↔ (Generated q R ∧ Core23 R) := by
  have hold : LuRazParametric.Row q (2*q+1) 4 :=
    (LuRazParametric.row_case_7 q (2*q+1) 4 (by omega) rfl).mpr (by omega)
  constructor
  · rintro ⟨hg,hc⟩
    exact ⟨(variant_avoiding_coordinate q 4 M R hold hM hc.2.2.2).mp hg,hc⟩
  · rintro ⟨hg,hc⟩
    exact ⟨(variant_avoiding_coordinate q 4 M R hold hM hc.2.2.2).mpr hg,hc⟩

theorem variant_core14_for_every_x (x : Nat) (hx : 3≤x) (M : Nat → Prop) (hM : M 2) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ VariantGenerated (x+1) M R ∧ Core14 R) ∧
      (l.length : Int)=3*(x:Int)*(x:Int)+(x:Int) := by
  obtain ⟨l,hn,he,hl⟩ := core14_for_every_x x hx
  exact ⟨l,hn,fun R => (he R).trans (variant_core14_iff (x+1) (by omega) M R hM).symm,hl⟩

theorem variant_core23_for_every_x (x : Nat) (hx : 3≤x) (M : Nat → Prop) (hM : M 4) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ VariantGenerated (x+1) M R ∧ Core23 R) ∧
      (l.length : Int)=2*(x:Int)*(x:Int)+3*(x:Int)-2 := by
  obtain ⟨l,hn,he,hl⟩ := core23_for_every_x x hx
  exact ⟨l,hn,fun R => (he R).trans (variant_core23_iff (x+1) (by omega) M R hM).symm,hl⟩

end LuRazClosure
