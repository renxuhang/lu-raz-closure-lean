import LatticeSourceTally

namespace LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
noncomputable section

theorem sum_scale {α : Type} (l : List α) (f : α→Int) (k : Int) :
    (l.map (fun a => k*f a)).sum=k*(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih,Int.mul_add]

theorem sum_add_functions {α : Type} (l : List α) (f g : α→Int) :
    (l.map (fun a => f a+g a)).sum=(l.map f).sum+(l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih]; omega

theorem tally_as_sum {α : Type} (l : List α) (P : α→Prop) :
    tally l P=(l.map (fun a => LuRazCounting.mark (P a))).sum := by
  classical
  induction l with
  | nil => simp [tally]
  | cons a l ih => by_cases hp : P a <;> simp [tally,LuRazCounting.mark,hp] at ih ⊢ <;> omega

theorem sum_swap {α β : Type} (l : List α) (k : List β) (f : α→β→Int) :
    (l.map (fun a => (k.map (f a)).sum)).sum=
      (k.map (fun b => (l.map (fun a => f a b)).sum)).sum := by
  induction l with
  | nil =>
    simp only [List.map_nil,List.sum_nil]
    induction k with
    | nil => rfl
    | cons b k hk => simp only [List.map_cons,List.sum_cons,Int.zero_add]; exact hk
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons,ih]
    rw [sum_add_functions]

def quadraticAnti (a b c t : Int) : Int :=
  a*t*(t-1)*(2*t-1)+3*b*t*(t-1)+6*c*t

theorem six_sum_quadratic (a b c : Int) (s n : Nat) :
    6*((List.range' s n).map (fun e : Nat => a*(e:Int)*(e:Int)+b*(e:Int)+c)).sum=
      quadraticAnti a b c ((s:Int)+(n:Int))-quadraticAnti a b c (s:Int) := by
  induction n with
  | zero => simp [quadraticAnti]
  | succ n ih =>
    rw [List.range'_concat]
    simp only [Nat.one_mul,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,Int.add_zero,Int.natCast_add,Int.natCast_one]
    unfold quadraticAnti at ih ⊢
    grind

#print axioms tally_as_sum
#print axioms sum_swap
#print axioms six_sum_quadratic
end
end LuRazLattice
