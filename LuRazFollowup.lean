import Std

/-!
Private research follow-up to Lu--Raz, arXiv:2405.10639v2.
Mathematical credit: Kengbo Lu and Abigail Raz (2024).

The source construction omits S_(n/2+1). Any finite instance below states
its actual data explicitly; it must not be mistaken for an author-approved
correction or a proof of the parameterized closure-size conjecture.
-/
namespace LuRazFollowup

abbrev SubsetOf (α : Type) := α → Prop

def Included {α : Type} (A B : SubsetOf α) : Prop := ∀ x, A x → B x

def InInterval {α : Type} (A F T : SubsetOf α) : Prop :=
  Included A T ∧ Included T F

-- Lu--Raz Lemma 2, including both directions and the containment assumptions
-- used implicitly in the paper. There is no restriction on the ground type.
theorem intervals_disjoint_iff {α : Type} {A B F G : SubsetOf α}
    (hAF : Included A F) (hBG : Included B G) :
    (¬ ∃ T, InInterval A F T ∧ InInterval B G T) ↔
      (∃ x, (A x ∧ ¬ G x) ∨ (B x ∧ ¬ F x)) := by
  classical
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    apply h
    refine ⟨(fun x => A x ∨ B x), ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro x hx; exact Or.inl hx
    · intro x hx
      cases hx with
      | inl ha => exact hAF x ha
      | inr hb =>
        apply Classical.byContradiction
        intro hf
        exact hn ⟨x, Or.inr ⟨hb,hf⟩⟩
    · intro x hx; exact Or.inr hx
    · intro x hx
      cases hx with
      | inl ha =>
        apply Classical.byContradiction
        intro hg
        exact hn ⟨x, Or.inl ⟨ha,hg⟩⟩
      | inr hb => exact hBG x hb
  · rintro ⟨x,hx⟩ ⟨T, ⟨hAT,hTF⟩, ⟨hBT,hTG⟩⟩
    cases hx with
    | inl h => exact h.2 (hTG x (hAT x h.1))
    | inr h => exact h.2 (hTF x (hBT x h.1))

-- For the n co-atoms F_p = U \ {p}, interval separation is a tournament
-- condition: q belongs to S_p or p belongs to S_q (paper Lemma 2).
theorem coatom_intervals_disjoint_iff {α : Type} [DecidableEq α]
    {p q : α} {A B : SubsetOf α}
    (hA : Included A (fun x => x ≠ p))
    (hB : Included B (fun x => x ≠ q)) :
    (¬ ∃ T, InInterval A (fun x => x ≠ p) T ∧
                InInterval B (fun x => x ≠ q) T) ↔ (A q ∨ B p) := by
  rw [intervals_disjoint_iff hA hB]
  constructor
  · rintro ⟨x, hx | hx⟩
    · have heq : x = q := Classical.byContradiction hx.2
      exact Or.inl (heq ▸ hx.1)
    · have heq : x = p := Classical.byContradiction hx.2
      exact Or.inr (heq ▸ hx.1)
  · intro h
    cases h with
    | inl h => exact ⟨q, Or.inl ⟨h,fun hn => hn rfl⟩⟩
    | inr h => exact ⟨p, Or.inr ⟨h,fun hn => hn rfl⟩⟩

-- Observation 3 with its required hypothesis made explicit: the filter
-- contains every co-atom. Reimer conditions alone do not force this.
theorem top_preimage_is_top {α ι : Type}
    (S F : ι → SubsetOf α) (topIndex : ι)
    (hTop : ∀ x, F topIndex x)
    (hSub : ∀ i, Included (S i) (F i))
    (hCoatom : ∀ x, ∃ j, ∀ y, F j y ↔ y ≠ x)
    (hDisjoint : ∀ i j, i ≠ j →
      ¬ ∃ T, InInterval (S i) (F i) T ∧ InInterval (S j) (F j) T) :
    ∀ x, S topIndex x := by
  classical
  intro x
  apply Classical.byContradiction
  intro hs
  obtain ⟨j,hj⟩ := hCoatom x
  have hne : topIndex ≠ j := by
    intro heq
    have hx := hTop x
    rw [heq] at hx
    exact ((hj x).mp hx) rfl
  apply hDisjoint topIndex j hne
  refine ⟨F j, ⟨?_, ?_⟩, ⟨hSub j, ?_⟩⟩
  · intro y hy
    apply (hj y).mpr
    intro hyx
    exact hs (hyx ▸ hy)
  · intro y _; exact hTop y
  · intro y hy; exact hy

-- Any superset of a set missing at most two elements is one of its four
-- possible supersets. This avoids exhaustive enumeration of 2^n subsets.
theorem two_hole_superset {α : Type} (T : α → Prop) (p q : α)
    (h : ∀ y, y ≠ p → y ≠ q → T y) :
    (∀ y, T y) ∨ (∀ y, T y ↔ y ≠ p) ∨
      (∀ y, T y ↔ y ≠ q) ∨ (∀ y, T y ↔ y ≠ p ∧ y ≠ q) := by
  classical
  by_cases hp : T p
  · by_cases hq : T q
    · left
      intro y
      by_cases hyp : y = p
      · exact hyp ▸ hp
      by_cases hyq : y = q
      · exact hyq ▸ hq
      exact h y hyp hyq
    · right; right; left
      intro y
      constructor
      · intro hy heq; exact hq (heq ▸ hy)
      · intro hy
        by_cases heq : y = p
        · exact heq ▸ hp
        exact h y heq hy
  · by_cases hq : T q
    · right; left
      intro y
      constructor
      · intro hy heq; exact hp (heq ▸ hy)
      · intro hy
        by_cases heq : y = q
        · exact heq ▸ hq
        exact h y hy heq
    · right; right; right
      intro y
      constructor
      · intro hy
        exact ⟨fun heq => hp (heq ▸ hy), fun heq => hq (heq ▸ hy)⟩
      · intro hy; exact h y hy.1 hy.2

#print axioms intervals_disjoint_iff
#print axioms coatom_intervals_disjoint_iff
#print axioms top_preimage_is_top

end LuRazFollowup
