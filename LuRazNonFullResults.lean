import LuRazNonFullClosure
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem partialMembers_length (q : Nat) (hq : 4≤q) :
    2*((partialMembers q).length : Int)=13*(q:Int)*(q:Int)+45*(q:Int)-44 := by
  have h0 : ((partialGroup q 0).length : Int)=1 := by
    have hh : (enumSmall 0).length=1 := by simpa only [smallCount] using enumSmall_length 0 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h1 : ((partialGroup q 1).length : Int)=2 := by
    have hh : (enumSmall 1).length=2 := by simpa only [smallCount] using enumSmall_length 1 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h2 : ((partialGroup q 2).length : Int)=1 := by
    have hh : (enumSmall 2).length=1 := by simpa only [smallCount] using enumSmall_length 2 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h3 : ((partialGroup q 3).length : Int)=1 := by
    have hh : (enumSmall 3).length=1 := by simpa only [smallCount] using enumSmall_length 3 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h4 : ((partialGroup q 4).length : Int)=2 := by
    have hh : (enumSmall 4).length=2 := by simpa only [smallCount] using enumSmall_length 4 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h5 : ((partialGroup q 5).length : Int)=5 := by
    have hh : (enumSmall 5).length=5 := by simpa only [smallCount] using enumSmall_length 5 (by decide)
    simp only [partialGroup,smallMembers,List.length_map]
    omega
  have h6 : ((partialGroup q 6).length : Int)=2*(q:Int)*(q:Int)-(q:Int)-3 := by
    simpa only [partialGroup,core23Members,List.length_map] using enum23_length q hq
  have h7 : 2*((partialGroup q 7).length : Int)=3*(q:Int)*(q:Int)+7*(q:Int)-14 := by
    simpa only [partialGroup,core123Members,List.length_map] using enum123_length q hq
  have h9 : ((partialGroup q 9).length : Int)=3*(q:Int)*(q:Int)-5*(q:Int)+2 := by
    simpa only [partialGroup,core14Members,List.length_map] using enum14_length q hq
  have h11 : ((partialGroup q 11).length : Int)=9*(q:Int)-10 := by
    simpa only [partialGroup,core124Members,List.length_map] using enum124_length q hq
  have h13 : ((partialGroup q 13).length : Int)=10*(q:Int)-16 := by
    simpa only [partialGroup,core134Members,List.length_map] using enum134_length q hq
  have h14 : ((partialGroup q 14).length : Int)=6*(q:Int)-6 := by
    simpa only [partialGroup,core234Members,List.length_map] using enum234_length q hq
  have h10 : ((partialGroup q 10).length : Int)=6 := rfl
  have he : partialMembers q=partialGroup q 0 ++ partialGroup q 1 ++ partialGroup q 2 ++ partialGroup q 3 ++ partialGroup q 4 ++ partialGroup q 5 ++ partialGroup q 6 ++ partialGroup q 7 ++ partialGroup q 9 ++ partialGroup q 10 ++ partialGroup q 11 ++ partialGroup q 13 ++ partialGroup q 14 := by
    simp only [partialMembers,partialCodes,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  rw [he]
  simp only [List.length_append,Int.natCast_add]
  simp only [Int.mul_assoc] at h6 h7 h9 ⊢
  omega

theorem nonfull_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ ¬CoreFull R) ∧
      2*(l.length : Int)=13*(q:Int)*(q:Int)+45*(q:Int)-44 := by
  exact ⟨partialMembers q,partialMembers_nodup q hq,partialMembers_exact q hq,partialMembers_length q hq⟩

def FinCoreFull (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) : Prop :=
  T ⟨0,by omega⟩ ∧ T ⟨1,by omega⟩ ∧ T ⟨2,by omega⟩ ∧ T ⟨3,by omega⟩

theorem fin_coreFull_iff (q : Nat) (hq : 4≤q) (T : Fin (4*q) → Prop) :
    CoreFull (Lift q T) ↔ FinCoreFull q hq T := by
  unfold CoreFull FinCoreFull
  rw [lift_at q T 1 (by omega),lift_at q T 2 (by omega),
      lift_at q T 3 (by omega),lift_at q T 4 (by omega)]

theorem nonfull_finite_cardinality (q : Nat) (hq : 4≤q) :
    ∃ l : List (Fin (4*q) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated q T ∧ ¬FinCoreFull q hq T) ∧
      2*(l.length : Int)=13*(q:Int)*(q:Int)+45*(q:Int)-44 := by
  obtain ⟨l,hn,he,hl⟩ := nonfull_cardinality q hq
  have ht := transfer_enumeration q hq (fun R => ¬CoreFull R) l hn he
  refine ⟨l.map (Restrict q),ht.1,?_,?_⟩
  · intro T
    exact (ht.2.1 T).trans (and_congr Iff.rfl (not_congr (fin_coreFull_iff q hq T)))
  · rw [List.length_map]
    exact hl

theorem nonfull_finite_for_every_x (x : Nat) (hx : 3≤x) :
    ∃ l : List (Fin (4*(x+1)) → Prop), l.Nodup ∧
      (∀ T, T∈l ↔ FinGenerated (x+1) T ∧ ¬FinCoreFull (x+1) (by omega) T) ∧
      2*(l.length : Int)=13*(x:Int)*(x:Int)+71*(x:Int)+14 := by
  obtain ⟨l,hn,he,hl⟩ := nonfull_finite_cardinality (x+1) (by omega)
  refine ⟨l,hn,he,?_⟩
  simp only [Int.natCast_add,Int.natCast_one,Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at hl ⊢
  omega
end LuRazClosure
