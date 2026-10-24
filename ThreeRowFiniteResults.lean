import ThreeRowFinite
import ThreeRowCore5
import ThreeRowCore12Count
import ThreeRowCore23Count
import ThreeRowCore234Count

namespace LuRazThreeRow
open LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem core5_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ Core5 (Lift q T)) ∧ l.length=5 := by
  obtain ⟨l,hn,he,hl⟩ := core5_cardinality q hq
  have ht := transfer_enumeration q hq Core5 l hn he
  exact ⟨l.map (Restrict q),ht.1,ht.2.1,ht.2.2.trans hl⟩

theorem core12_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ Core12 (Lift q T)) ∧ l.length=4 := by
  obtain ⟨l,hn,he,hl⟩ := core12_cardinality q hq
  have ht := transfer_enumeration q hq Core12 l hn he
  exact ⟨l.map (Restrict q),ht.1,ht.2.1,ht.2.2.trans hl⟩

theorem core23_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ Core23 (Lift q T)) ∧
      (l.length : Int)=2*(q:Int)*(q:Int)-3*(q:Int)-1 := by
  obtain ⟨l,hn,he,hl⟩ := core23_cardinality q hq
  have ht := transfer_enumeration q hq Core23 l hn he
  exact ⟨l.map (Restrict q),ht.1,ht.2.1,by rw [ht.2.2]; exact hl⟩

theorem core234_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ Core234 (Lift q T)) ∧
      (l.length : Int)=10*(q:Int)-15 := by
  obtain ⟨l,hn,he,hl⟩ := core234_cardinality q hq
  have ht := transfer_enumeration q hq Core234 l hn he
  exact ⟨l.map (Restrict q),ht.1,ht.2.1,by rw [ht.2.2]; exact hl⟩

end LuRazThreeRow
