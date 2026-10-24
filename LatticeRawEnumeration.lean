import LatticePointProperties
import LatticeShapeCoverage

namespace LuRazClosure.SourcePieces
open LuRazLattice LuRazEnumeration
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
noncomputable section

def rawMembers (q : Nat) : List (Nat×Nat×Nat) :=
  positiveIds.flatMap (fun i => (natPoints q i).map (fun p => (i,p)))

theorem rawMembers_mem (q i a b : Nat) (hq : 4≤q) :
    (i,a,b)∈rawMembers q ↔ Domain q i a b := by
  constructor
  · intro h
    obtain ⟨j,hj,hp⟩ := List.mem_flatMap.mp h
    obtain ⟨p,hp,he⟩ := List.mem_map.mp hp
    cases he
    exact (natPoints_mem q i a b hq hj).mp hp
  · intro h
    have hi := domain_ids q i a b h
    exact List.mem_flatMap.mpr ⟨i,hi,List.mem_map.mpr ⟨(a,b),(natPoints_mem q i a b hq hi).mpr h,rfl⟩⟩

theorem rawMembers_nodup (q : Nat) (hq : 4≤q) : (rawMembers q).Nodup := by
  apply nodup_flatMap_separated _ _ (by decide : positiveIds.Nodup)
  · intro i hi
    apply nodup_map_injective _ ?_ _ (natPoints_nodup q i hq hi)
    intro a b he
    exact congrArg Prod.snd he
  · intro i _ j _ x hx y hy he
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hy
    exact congrArg Prod.fst he

def rawEval (q : Nat) (p : Nat×Nat×Nat) : Nat→Prop :=
  (decode q p.1 p.2.1 p.2.2).eval q

def latticeMembers (q : Nat) : List (Nat→Prop) := (rawMembers q).map (rawEval q)

theorem rawEval_injective (q : Nat) (hq : 4≤q) (p r : Nat×Nat×Nat)
    (hp : p∈rawMembers q) (hr : r∈rawMembers q) (he : rawEval q p=rawEval q r) : p=r := by
  obtain ⟨i,a,b⟩ := p
  obtain ⟨j,c,d⟩ := r
  have hd := (rawMembers_mem q i a b hq).mp hp
  have hd' := (rawMembers_mem q j c d hq).mp hr
  have hs := Shape.unique q hq (decode q i a b) (decode q j c d)
    (decode_valid q i a b hq hd) (decode_valid q j c d hq hd')
    (fun e => Iff.of_eq (congrFun he e))
  have hh := congrArg (identify q) hs
  simpa only [identify_decode q i a b hq hd,identify_decode q j c d hq hd'] using hh

theorem latticeMembers_nodup (q : Nat) (hq : 4≤q) : (latticeMembers q).Nodup := by
  exact nodup_map_on (rawEval q) (rawMembers q) (rawMembers_nodup q hq)
    (fun a ha b hb he => rawEval_injective q hq a b ha hb he)

theorem latticeMembers_exact (q : Nat) (hq : 4≤q) (R : Nat→Prop) :
    R∈latticeMembers q ↔ Generated q R := by
  constructor
  · intro h
    obtain ⟨⟨i,a,b⟩,hp,rfl⟩ := List.mem_map.mp h
    exact Shape.generated q hq (decode q i a b)
      (decode_valid q i a b hq ((rawMembers_mem q i a b hq).mp hp))
  · intro h
    obtain ⟨z,hz,he⟩ := shape_of_generated q hq R h
    have hd := identify_valid q hq z hz
    generalize hi : identify q z=p at hd
    obtain ⟨i,a,b⟩ := p
    apply List.mem_map.mpr
    refine ⟨(i,a,b),(rawMembers_mem q i a b hq).mpr hd.1,?_⟩
    unfold rawEval
    rw [hd.2]
    funext e
    exact propext (he e).symm

theorem latticeMembers_perm (q : Nat) (hq : 4≤q) :
    (latticeMembers q).Perm (closureMembers q) := by
  apply (List.perm_ext_iff_of_nodup (latticeMembers_nodup q hq) (closure_members_nodup q hq)).mpr
  intro R
  rw [latticeMembers_exact q hq R,closure_members_exact q hq R]

#print axioms rawMembers_nodup
#print axioms rawEval_injective
#print axioms latticeMembers_exact
#print axioms latticeMembers_perm
end
end LuRazClosure.SourcePieces
