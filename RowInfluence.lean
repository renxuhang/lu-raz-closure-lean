import LuRazTotalClosure

/-! A structural obstruction to an overly broad fixed-row stability claim.
Deleting just A loses an entire two-parameter family. This is a structural
theorem about deletion, not an admissible prize construction on its own. -/
namespace LuRazRowInfluence
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def WithoutRow (q banned : Nat) (R : Nat → Prop) : Prop :=
  ∃ l : List Nat, l ≠ [] ∧ (∀ i∈l, i≤4*q+2 ∧ i≠banned) ∧
    ∀ e, ListUnion (Row q) l e ↔ R e

theorem one_without_four_source (q i : Nat) (hq : 4≤q)
    (h1 : Row q i 1) (h4 : ¬Row q i 4) : i=4 ∨ i=4*q+2 := by
  unfold Row at h1
  rcases h1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals first | omega | (exfalso; apply h4; unfold Row; omega)

theorem high_missing_cut (q t p : Nat) (hq : 4≤q)
    (ht : P q t) (hp : P q p) : ¬NF123.eval q (.high t p) (2*q+3) := by
  intro h
  simp only [NF123.eval,NF123.body,LRow,LNormal,I] at h
  have hp' := hp
  have ht' := ht
  unfold P at hp' ht'
  unfold beta at h
  split at h <;> omega

theorem high_requires_A (q t p : Nat) (hq : 4≤q)
    (hz : NF123.Valid q (.high t p)) :
    ¬WithoutRow q (4*q+2) (NF123.eval q (.high t p)) := by
  intro hg
  obtain ⟨l,_,hv,he⟩ := hg
  have hc := NF123.core q hq (.high t p) hz
  obtain ⟨i,hi,h1⟩ := (he 1).mpr hc.1
  have h4 : ¬Row q i 4 := by
    intro hr
    exact hc.2.2.2 ((he 4).mp ⟨i,hi,hr⟩)
  rcases one_without_four_source q i hq h1 h4 with h | h
  · have hr : Row q i (2*q+3) := by
      exact (row_case_4 q i (2*q+3) (by omega) h).mpr (by omega)
    have hz' : P q t ∧ P q p ∧ q+3≤p ∧ t≤p := hz
    exact high_missing_cut q t p hq hz'.1 hz'.2.1 ((he (2*q+3)).mp ⟨i,hi,hr⟩)
  · exact (hv i hi).2 h

theorem high_generated_and_lost (q t p : Nat) (hq : 4≤q)
    (hz : NF123.Valid q (.high t p)) :
    Generated q (NF123.eval q (.high t p)) ∧
    ¬WithoutRow q (4*q+2) (NF123.eval q (.high t p)) :=
  ⟨NF123.generated q hq (.high t p) hz, high_requires_A q t p hq hz⟩

theorem high_pair_unique (q t p u v : Nat) (hq : 4≤q)
    (hz : NF123.Valid q (.high t p)) (hw : NF123.Valid q (.high u v))
    (he : ∀e,NF123.eval q (.high t p) e ↔ NF123.eval q (.high u v) e) :
    t=u ∧ p=v := by
  have h := NF123.unique q hq (.high t p) (.high u v) hz hw he
  cases h
  exact ⟨rfl,rfl⟩

/-- A nonempty union of rows, with every row drawn from a specified support. -/
def SupportedGenerated {ι α : Type} (Rows : ι → α → Prop)
    (Keep : ι → Prop) (T : α → Prop) : Prop :=
  ∃ l : List ι, l ≠ [] ∧ (∀i∈l, Keep i) ∧
    ∀e, (∃i∈l, Rows i e) ↔ T e

/-- Any member generated entirely from common unchanged rows is retained. -/
theorem supported_generated_transfer {ι α : Type}
    (Old New : ι → α → Prop) (Keep : ι → Prop) (T : α → Prop)
    (hsame : ∀i,Keep i → ∀e,Old i e ↔ New i e)
    (hg : SupportedGenerated Old Keep T) : SupportedGenerated New Keep T := by
  obtain ⟨l,hl,hkeep,he⟩ := hg
  refine ⟨l,hl,hkeep,?_⟩
  intro e
  constructor
  · rintro ⟨i,hi,hr⟩
    exact (he e).mp ⟨i,hi,(hsame i (hkeep i hi) e).mpr hr⟩
  · intro ht
    obtain ⟨i,hi,hr⟩ := (he e).mpr ht
    exact ⟨i,hi,(hsame i (hkeep i hi) e).mp hr⟩

theorem supported_generated_iff {ι α : Type}
    (Old New : ι → α → Prop) (Keep : ι → Prop) (T : α → Prop)
    (hsame : ∀i,Keep i → ∀e,Old i e ↔ New i e) :
    SupportedGenerated Old Keep T ↔ SupportedGenerated New Keep T := by
  constructor
  · exact supported_generated_transfer Old New Keep T hsame
  · exact supported_generated_transfer New Old Keep T (fun i hi e => (hsame i hi e).symm)

end LuRazRowInfluence
