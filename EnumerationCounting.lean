import Std

namespace LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem range_mem (a s n : Nat) :
    a ∈ List.range' s n ↔ s ≤ a ∧ a < s+n := by
  rw [List.mem_range']
  simp only [Nat.one_mul]
  constructor
  · rintro ⟨i,hi,he⟩
    omega
  · intro h
    exact ⟨a-s,by omega,by omega⟩

theorem nodup_map_injective {α β : Type} (f : α → β)
    (hf : ∀ a b, f a=f b → a=b) (l : List α) (hl : l.Nodup) : (l.map f).Nodup := by
  apply List.Pairwise.map f ?_ hl
  intro a b hab heq
  exact hab (hf a b heq)

theorem nodup_map_on {α β : Type} (f : α → β) (l : List α) (hl : l.Nodup)
    (hf : ∀ a ∈ l, ∀ b ∈ l, f a=f b → a=b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have hc := List.nodup_cons.mp hl
    rw [List.map_cons,List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨b,hb,heq⟩ := List.mem_map.mp hm
      have hab := hf a (by simp) b (by simp only [List.mem_cons]; exact Or.inr hb) heq.symm
      subst b
      exact hc.1 hb
    · apply ih hc.2
      intro b hb c hc heq
      exact hf b (by simp only [List.mem_cons]; exact Or.inr hb)
        c (by simp only [List.mem_cons]; exact Or.inr hc) heq

theorem nodup_flatMap_separated {α β : Type} (f : α → List β) (l : List α)
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup)
    (hsep : ∀ a ∈ l, ∀ b ∈ l, ∀ x ∈ f a, ∀ y ∈ f b, x=y → a=b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    have hc := List.nodup_cons.mp hl
    rw [List.flatMap_cons,List.nodup_append]
    refine ⟨hf a (by simp),?_,?_⟩
    · apply ih hc.2
      · intro b hb
        exact hf b (by simp only [List.mem_cons]; exact Or.inr hb)
      · intro b hb c hc x hx y hy heq
        exact hsep b (by simp only [List.mem_cons]; exact Or.inr hb)
          c (by simp only [List.mem_cons]; exact Or.inr hc) x hx y hy heq
    · intro x hx y hy heq
      obtain ⟨b,hb,hyb⟩ := List.mem_flatMap.mp hy
      have hab := hsep a (by simp) b (by simp only [List.mem_cons]; exact Or.inr hb) x hx y hyb heq
      subst b
      exact hc.1 hb

def pairs {α : Type} (C : Nat → Nat → α) (s n : Nat) (lo len : Nat → Nat) : List α :=
  (List.range' s n).flatMap (fun a => (List.range' (lo a) (len a)).map (C a))

theorem pairs_split {α : Type} (C : Nat → Nat → α) (s m n : Nat)
    (lo len : Nat → Nat) :
    pairs C s (m+n) lo len = pairs C s m lo len ++ pairs C (s+m) n lo len := by
  have h := List.range'_append (s:=s) (m:=m) (n:=n) (step:=1)
  simp only [Nat.one_mul] at h
  unfold pairs
  rw [←h,List.flatMap_append]

theorem pairs_mem {α : Type} (C : Nat → Nat → α) (s n : Nat)
    (lo len : Nat → Nat) (z : α) :
    z ∈ pairs C s n lo len ↔
      ∃ a b, (s ≤ a ∧ a < s+n) ∧
        (lo a ≤ b ∧ b < lo a+len a) ∧ C a b=z := by
  simp only [pairs,List.mem_flatMap,List.mem_map,range_mem]
  constructor
  · rintro ⟨a,ha,b,hb,heq⟩
    exact ⟨a,b,ha,hb,heq⟩
  · rintro ⟨a,b,ha,hb,heq⟩
    exact ⟨a,ha,b,hb,heq⟩

theorem pairs_nodup {α : Type} (C : Nat → Nat → α)
    (hC : ∀ a b c d, C a b=C c d → a=c ∧ b=d)
    (s n : Nat) (lo len : Nat → Nat) : (pairs C s n lo len).Nodup := by
  unfold pairs
  apply nodup_flatMap_separated _ _ (List.nodup_range')
  · intro a _
    apply nodup_map_injective _ ?_ _ List.nodup_range'
    intro b d h
    exact (hC a b a d h).2
  · intro a _ c _ x hx y hy heq
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨d,_,rfl⟩ := List.mem_map.mp hy
    exact (hC a b c d heq).1

theorem int_length_flatMap {α β : Type} (l : List α) (f : α → List β) :
    ((l.flatMap f).length : Int) = (l.map (fun a => ((f a).length : Int))).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons,List.length_append,Int.natCast_add,
      List.map_cons,List.sum_cons,ih]

/-- Twice the arithmetic progression sum, with no division or finite bound. -/
theorem twice_sum_linear (K : Int) (s n : Nat) :
    2*((List.range' s n).map (fun (a:Nat) => K-(a:Int))).sum =
      (n:Int)*(2*K-2*(s:Int)-(n:Int)+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range'_concat]
    simp only [Nat.one_mul,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,Int.add_zero,Int.natCast_add,Int.natCast_one]
    simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at ih ⊢
    omega

theorem pairs_length_linear {α : Type} (C : Nat → Nat → α) (s n : Nat)
    (lo len : Nat → Nat) (K : Int)
    (hlen : ∀ a, s ≤ a ∧ a < s+n → (len a : Int)=K-(a:Int)) :
    2*((pairs C s n lo len).length : Int) =
      (n:Int)*(2*K-2*(s:Int)-(n:Int)+1) := by
  unfold pairs
  rw [int_length_flatMap]
  have heq :
      (List.range' s n).map (fun a => (((List.range' (lo a) (len a)).map (C a)).length : Int)) =
      (List.range' s n).map (fun (a:Nat) => K-(a:Int)) := by
    apply List.map_congr_left
    intro a ha
    simp only [List.length_map,List.length_range']
    exact hlen a ((range_mem a s n).mp ha)
  rw [heq]
  exact twice_sum_linear K s n

theorem triangular_pairs_count {α : Type} (C : Nat → Nat → α) (n : Nat) :
    2*((pairs C 0 n (fun _ => 0) (fun r => r+1)).length : Int)=(n:Int)*((n:Int)+1) := by
  induction n with
  | zero => simp [pairs]
  | succ n ih =>
    have hs := pairs_split C 0 n 1 (fun _ => 0) (fun r => r+1)
    simp only [Nat.zero_add] at hs
    have hl : (pairs C n 1 (fun _ => 0) (fun r => r+1)).length=n+1 := by simp [pairs]
    rw [hs,List.length_append,Int.natCast_add,hl,Int.natCast_add]
    simp only [Int.mul_add,Int.mul_sub,Int.add_mul,Int.sub_mul,Int.mul_assoc] at ih ⊢
    omega

theorem pairs_length_constant {α : Type} (C : Nat → Nat → α) (s n : Nat)
    (lo : Nat → Nat) (k : Nat) :
    (pairs C s n lo (fun _ => k)).length=n*k := by
  induction n with
  | zero => simp [pairs]
  | succ n ih =>
    have hs := pairs_split C s n 1 lo (fun _ => k)
    have hl : (pairs C (s+n) 1 lo (fun _ => k)).length=k := by simp [pairs]
    rw [hs,List.length_append,ih,hl,Nat.add_mul,Nat.one_mul]

end LuRazEnumeration
