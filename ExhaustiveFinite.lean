import ExhaustiveTotal

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

theorem core123_new_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ FinCore123 q hq T) ∧
      2*(l.length : Int)=3*(q:Int)*(q:Int)+3*(q:Int)-6 := by
  obtain ⟨l,hn,he,hl⟩ := core123_new_cardinality q hq
  have ht := transfer_enumeration q hq Core123 l hn he
  refine ⟨l.map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (fin_core123_iff q hq T))
  · simpa only [List.length_map] using hl

theorem core134_new_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ FinCore134 q hq T) ∧
      (l.length : Int)=10*(q:Int)-16 := by
  obtain ⟨l,hn,he,hl⟩ := core134_new_cardinality q hq
  have ht := transfer_enumeration q hq Core134 l hn he
  refine ⟨l.map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (fin_core134_iff q hq T))
  · simpa only [List.length_map] using hl

theorem full_new_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ CoreFull (Lift q T)) ∧
      (l.length : Int)=5*(q:Int)*(q:Int)-7*(q:Int)+6 := by
  obtain ⟨l,hn,he,hl⟩ := full_new_cardinality q hq
  have ht := transfer_enumeration q hq CoreFull l hn he
  exact ⟨l.map (Restrict q),ht.1,ht.2.1,by simpa only [List.length_map] using hl⟩

/-- Exact enumeration of unions of nonempty subfamilies of the actual finite source V. -/
theorem closure_new_finite_doubled (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T) ∧
      2*(l.length : Int)=23*(q:Int)*(q:Int)+31*(q:Int)-30 := by
  obtain ⟨l,hn,he,hl⟩ := closure_new_cardinality q hq
  have he' : ∀ R, R∈l ↔ Generated q R ∧ True := by
    intro R
    simpa only [and_true] using he R
  have ht := transfer_enumeration q hq (fun _ => True) l hn he'
  refine ⟨l.map (Restrict q),ht.1,?_,?_⟩
  · intro T
    simpa only [and_true] using ht.2.1 T
  · simpa only [List.length_map] using hl

theorem closure_new_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T) ∧
      l.length=(23*q*q+31*q-30)/2 := by
  obtain ⟨l,hn,he,hl⟩ := closure_new_finite_doubled q hq
  refine ⟨l,hn,he,?_⟩
  have hc : ((23*q*q+31*q : Nat) : Int)=23*(q:Int)*(q:Int)+31*(q:Int) := by simp
  have hnat : 2*l.length+30=23*q*q+31*q := by omega
  omega

theorem closure_new_finite_for_every_x (x : Nat) (hx : 3≤x) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated (x+1) T) ∧
      l.length=(23*x*x+77*x+24)/2 := by
  obtain ⟨l,hn,he,hl⟩ := closure_new_finite_doubled (x+1) (by omega)
  refine ⟨l,hn,he,?_⟩
  simp only [Int.natCast_add,Int.natCast_one,Int.mul_add,Int.add_mul,Int.mul_one,
    Int.mul_assoc] at hl
  have hc : ((23*x*x+77*x+24 : Nat) : Int)=23*(x:Int)*(x:Int)+77*(x:Int)+24 := by simp
  simp only [Int.mul_assoc] at hc
  have hnat : 2*l.length=23*x*x+77*x+24 := by omega
  omega

/-- Simultaneous exact counts, exhibiting strict improvement for every q ≥ 4. -/
theorem exact_closure_improvement (q : Nat) (hq : 4≤q) :
    ∃ old new : List (Fin (4*q) → Prop), old.Nodup ∧ new.Nodup ∧
      (∀ T, T∈old ↔ LuRazClosure.FinGenerated q T) ∧
      (∀ T, T∈new ↔ FinGenerated q T) ∧
      new.length+2*(q-3)=old.length ∧ new.length<old.length := by
  obtain ⟨old,ho,heo,hlo⟩ := LuRazClosure.closure_finite_cardinality q hq
  obtain ⟨new,hn,hen,hln⟩ := closure_new_finite_doubled q hq
  refine ⟨old,new,ho,hn,heo,hen,?_,?_⟩ <;> omega

end LuRazThreeRow
