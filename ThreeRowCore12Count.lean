import ThreeRowCore12
import EnumerationCounting

namespace LuRazThreeRow
open LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def flags12 : List (Bool × Bool) := [(false,false),(false,true),(true,false),(true,true)]
def eval12 (q : Nat) (z : Bool × Bool) : Nat → Prop := Mix12 q (z.1=true) (z.2=true)
def members12 (q : Nat) : List (Nat → Prop) := flags12.map (eval12 q)

theorem flags12_all (z : Bool × Bool) : z ∈ flags12 := by
  obtain ⟨a,b⟩ := z
  cases a <;> cases b <;> decide

theorem members12_exact (q : Nat) (hq : 4 ≤ q) (R : Nat → Prop) :
    R ∈ members12 q ↔ Generated q R ∧ Core12 R := by
  rw [core12_exact q hq R]
  constructor
  · intro h
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp h
    exact ⟨z.1=true,z.2=true,fun _ => Iff.rfl⟩
  · rintro ⟨c,b,he⟩
    classical
    let z : Bool × Bool := (decide c,decide b)
    refine List.mem_map.mpr ⟨z,flags12_all z,?_⟩
    funext e
    apply propext
    have hz : eval12 q z e ↔ Mix12 q c b e := by simp only [eval12,z,decide_eq_true_eq]
    exact hz.trans (he e).symm

theorem members12_nodup (q : Nat) (hq : 4 ≤ q) : (members12 q).Nodup := by
  apply nodup_map_on _ _ (by decide : flags12.Nodup)
  intro a _ b _ he
  have hu := mix12_unique q hq (a.1=true) (a.2=true) (b.1=true) (b.2=true)
    (fun e => Iff.of_eq (congrFun he e))
  obtain ⟨a1,a2⟩ := a
  obtain ⟨b1,b2⟩ := b
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> simp_all

theorem core12_cardinality (q : Nat) (hq : 4 ≤ q) :
    ∃ l : List (Nat → Prop), l.Nodup ∧
      (∀ R, R∈l ↔ Generated q R ∧ Core12 R) ∧ l.length=4 :=
  ⟨members12 q,members12_nodup q hq,members12_exact q hq,by simp [members12,flags12]⟩

end LuRazThreeRow
