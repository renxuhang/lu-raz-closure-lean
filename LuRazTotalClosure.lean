import LuRazFullCount
namespace LuRazClosure
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

def fullMembers (q : Nat) : List (Nat → Prop) := (enumFull q).map (NFFull.eval q)

theorem full_members_nodup (q : Nat) (hq : 4≤q) : (fullMembers q).Nodup := by
  apply nodup_map_on _ _ (enumFull_nodup q)
  intro a ha b hb he
  exact NFFull.unique q hq a b ((enumFull_exact q hq a).mp ha) ((enumFull_exact q hq b).mp hb) (fun e => Iff.of_eq (congrFun he e))

theorem full_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈fullMembers q ↔ Generated q R ∧ CoreFull R := by
  constructor
  · intro hr
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
    exact (full_closure_exact q hq _).mpr ⟨z,(enumFull_exact q hq z).mp hz,fun _ => Iff.rfl⟩
  · intro hr
    obtain ⟨z,hz,he⟩ := (full_closure_exact q hq R).mp hr
    refine List.mem_map.mpr ⟨z,(enumFull_exact q hq z).mpr hz,?_⟩
    funext e
    exact propext (he e).symm

theorem full_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ CoreFull R) ∧
      (l.length : Int)=5*(q:Int)*(q:Int)-5*(q:Int)+1 := by
  exact ⟨fullMembers q,full_members_nodup q hq,full_members_exact q hq,by simpa only [fullMembers,List.length_map] using enumFull_length q hq⟩

theorem full_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ FinCoreFull q hq T) ∧
      (l.length : Int)=5*(q:Int)*(q:Int)-5*(q:Int)+1 := by
  obtain ⟨l,hn,he,hl⟩ := full_cardinality q hq
  have ht := transfer_enumeration q hq CoreFull l hn he
  refine ⟨l.map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (fin_coreFull_iff q hq T))
  · simpa only [List.length_map] using hl

theorem full_finite_for_every_x (x : Nat) (hx : 3≤x) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated (x+1) T ∧ FinCoreFull (x+1) (by omega) T) ∧
      (l.length : Int)=5*(x:Int)*(x:Int)+5*(x:Int)+1 := by
  obtain ⟨l,hn,he,hl⟩ := full_finite_cardinality (x+1) (by omega)
  refine ⟨l,hn,he,?_⟩
  simp only [Int.natCast_add,Int.natCast_one,Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at hl ⊢
  omega

noncomputable def closureMembers (q : Nat) : List (Nat → Prop) := partialMembers q ++ fullMembers q

theorem closure_members_nodup (q : Nat) (hq : 4≤q) : (closureMembers q).Nodup := by
  rw [closureMembers,List.nodup_append]
  refine ⟨partialMembers_nodup q hq,full_members_nodup q hq,?_⟩
  intro R hR T hT heq
  have hr := ((partialMembers_exact q hq R).mp hR).2
  have ht := ((full_members_exact q hq T).mp hT).2
  subst T
  exact hr ht

theorem closure_members_exact (q : Nat) (hq : 4≤q) (R : Nat → Prop) :
    R∈closureMembers q ↔ Generated q R := by
  classical
  rw [closureMembers,List.mem_append,partialMembers_exact q hq R,full_members_exact q hq R]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hg
    by_cases hc : CoreFull R
    · exact Or.inr ⟨hg,hc⟩
    · exact Or.inl ⟨hg,hc⟩

theorem closure_members_length (q : Nat) (hq : 4≤q) :
    2*((closureMembers q).length : Int)=23*(q:Int)*(q:Int)+35*(q:Int)-42 := by
  have hp := partialMembers_length q hq
  have hf : ((fullMembers q).length : Int)=5*(q:Int)*(q:Int)-5*(q:Int)+1 := by
    simpa only [fullMembers,List.length_map] using enumFull_length q hq
  simp only [closureMembers,List.length_append,Int.natCast_add]
  simp only [Int.mul_assoc] at hp hf ⊢
  omega

theorem closure_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T) ∧
      2*(l.length : Int)=23*(q:Int)*(q:Int)+35*(q:Int)-42 := by
  have hn := closure_members_nodup q hq
  have he : ∀ R, R∈closureMembers q ↔ Generated q R ∧ True := by
    intro R
    simpa only [and_true] using closure_members_exact q hq R
  have ht := transfer_enumeration q hq (fun _ => True) (closureMembers q) hn he
  refine ⟨(closureMembers q).map (Restrict q),ht.1,?_,?_⟩
  · intro T
    simpa only [and_true] using ht.2.1 T
  · simpa only [List.length_map] using closure_members_length q hq

theorem closure_finite_doubled_for_every_x (x : Nat) (hx : 3≤x) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated (x+1) T) ∧
      2*(l.length : Int)=23*(x:Int)*(x:Int)+81*(x:Int)+16 := by
  obtain ⟨l,hn,he,hl⟩ := closure_finite_cardinality (x+1) (by omega)
  refine ⟨l,hn,he,?_⟩
  simp only [Int.natCast_add,Int.natCast_one,Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at hl ⊢
  omega

/-- The exact nonempty-subfamily union-closure count, for the explicitly completed construction. -/
theorem closure_cardinality_for_every_x (x : Nat) (hx : 3≤x) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated (x+1) T) ∧
      l.length=(23*x*x+81*x+16)/2 := by
  obtain ⟨l,hn,he,hl⟩ := closure_finite_doubled_for_every_x x hx
  refine ⟨l,hn,he,?_⟩
  have hc : ((23*x*x+81*x+16:Nat):Int)=23*(x:Int)*(x:Int)+81*(x:Int)+16 := by simp
  have hnat : 2*l.length=23*x*x+81*x+16 := by omega
  omega
end LuRazClosure
