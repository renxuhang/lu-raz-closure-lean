import LatticeTally

namespace LuRazLattice
noncomputable section

theorem tally_perm {α : Type} {l k : List α} (h : l.Perm k) (P : α→Prop) :
    tally l P=tally k P := by
  classical
  unfold tally
  exact congrArg (fun n : Nat => (n:Int)) (h.filter (fun x => decide (P x))).length_eq

theorem tally_flatMap {α β : Type} (l : List α) (f : α→List β) (P : β→Prop) :
    tally (l.flatMap f) P=(l.map (fun a => tally (f a) P)).sum := by
  induction l with
  | nil => simp [tally]
  | cons a l ih => simp only [List.flatMap_cons,tally_append,List.map_cons,List.sum_cons,ih]

end
end LuRazLattice
