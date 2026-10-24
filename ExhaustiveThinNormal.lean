import ExhaustiveThinParts
namespace LuRazThreeRow
open LuRazClosure LuRazParametric
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

inductive NormalFull where | old (z : NFFull) | fresh (z : AddFull) deriving DecidableEq, Repr
def NormalFull.Valid (q : Nat) : NormalFull → Prop
  | .old z => z.Valid q ∧ ¬LostFull q z | .fresh z => z.Valid q
def NormalFull.eval (q : Nat) : NormalFull → Nat → Prop
  | .old z => z.eval q | .fresh z => z.eval q

theorem fixed_thin_normal (q : Nat) (hq : 4≤q) (u d k f l : Prop)
    (hc : CoreFull (FixedThin q u d k f l)) (hn : FixedThin q u d k f l (4*q)) :
    ∃ z : NormalFull, z.Valid q ∧ ∀ e, FixedThin q u d k f l e ↔ z.eval q e := by
  classical
  have h1 := hc.1
  have h2 := hc.2.1
  have h3 := hc.2.2.1
  have h4 := hc.2.2.2
  by_cases hu : u
  ·
    by_cases hd : d
    ·
      by_cases hk : k
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
        ·
          by_cases hl : l
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
    ·
      by_cases hk : k
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            refine ⟨.fresh (.gap (2*q+2)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.fresh .point,?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
        ·
          by_cases hl : l
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
  ·
    by_cases hd : d
    ·
      by_cases hk : k
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
        ·
          by_cases hl : l
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
        ·
          by_cases hl : l
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
    ·
      by_cases hk : k
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            refine ⟨.fresh (.right (2*q+2)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
        ·
          by_cases hl : l
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.fresh .point,?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
        ·
          by_cases hl : l
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)

theorem mixed_thin_normal (q a b : Nat) (hq : 4≤q) (hab : JReachable q a b) (u d k f l : Prop)
    (hc : CoreFull (MixedThin q a b u d k f l)) (hn : MixedThin q a b u d k f l (4*q)) :
    ∃ z : NormalFull, z.Valid q ∧ ∀ e, MixedThin q a b u d k f l e ↔ z.eval q e := by
  classical
  have hb := hab
  unfold JReachable at hb
  have h2 := hc.2.1
  by_cases hu : u
  ·
    by_cases hd : d
    ·
      by_cases hk : k
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
        ·
          by_cases hl : l
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
    ·
      by_cases hk : k
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            by_cases ha : a≤q+3
            ·
              refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
              · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
              · intro e
                simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            ·
              refine ⟨.fresh (.gap a),?_,?_⟩
              · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
              · intro e
                simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            by_cases ha : a≤q+3
            ·
              refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
              · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
              · intro e
                simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            ·
              refine ⟨.fresh (.gap a),?_,?_⟩
              · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
              · intro e
                simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
        ·
          by_cases hl : l
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
  ·
    by_cases hd : d
    ·
      by_cases hk : k
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
        ·
          by_cases hl : l
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
    ·
      by_cases hk : k
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            by_cases ha : a=5
            ·
              refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
              · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
              · intro e
                simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            ·
              refine ⟨.fresh (.right a),?_,?_⟩
              · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
              · intro e
                simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
      ·
        by_cases hf : f
        ·
          by_cases hl : l
          ·
            refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
            · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            · intro e
              simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
          ·
            by_cases ha : a=5
            ·
              refine ⟨.old (.rightGap (4*q-2) (4*q)),?_,?_⟩
              · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
              · intro e
                simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
            ·
              refine ⟨.fresh (.right a),?_,?_⟩
              · simp [NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
              · intro e
                simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I,NormalFull.Valid,NormalFull.eval,NFFull.Valid,NFFull.eval,FullHead,LostFull,AddFull.Valid,AddFull.eval,I] <;> omega
        ·
          by_cases hl : l
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)
          ·
            exact False.elim (by simp_all [FixedThin,MixedThin,JRow,ARow,CRow,K1Row,EPrime,LPrime,I] <;> omega)

theorem full_thin_normal (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : CoreFull R) (hn1 : ¬R (4*q-1)) (hn : R (4*q)) :
    ∃ z : NormalFull, z.Valid q ∧ ∀ e, R e ↔ z.eval q e := by
  obtain ⟨u,d,k,f,l,hp⟩ := thin_parts q hq R hg hn1
  rcases hp with he | ⟨a,b,hab,he⟩
  · have hcc : CoreFull (FixedThin q u d k f l) := by
      unfold CoreFull at *
      rw [←he 1,←he 2,←he 3,←he 4]
      exact hc
    obtain ⟨z,hz,hze⟩ := fixed_thin_normal q hq u d k f l hcc ((he _).mp hn)
    exact ⟨z,hz,fun e => (he e).trans (hze e)⟩
  · have hcc : CoreFull (MixedThin q a b u d k f l) := by
      unfold CoreFull at *
      rw [←he 1,←he 2,←he 3,←he 4]
      exact hc
    obtain ⟨z,hz,hze⟩ := mixed_thin_normal q a b hq hab u d k f l hcc ((he _).mp hn)
    exact ⟨z,hz,fun e => (he e).trans (hze e)⟩

end LuRazThreeRow
