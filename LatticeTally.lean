import LatticePointSets

namespace LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section

def tally {α : Type} (l : List α) (P : α → Prop) : Int := by
  classical
  exact ((l.filter (fun x => decide (P x))).length:Int)

theorem tally_eq_filter {α : Type} (l : List α) (P : α → Prop) [DecidablePred P] :
    tally l P=(((l.filter (fun x => decide (P x))).length):Int) := by
  classical
  unfold tally
  congr 1
  congr 1
  apply List.filter_congr
  intro x _
  by_cases hp : P x <;> simp [hp]

theorem tally_congr {α : Type} (l : List α) (P Q : α → Prop)
    (h : ∀ x∈l,P x↔Q x) : tally l P=tally l Q := by
  classical
  unfold tally
  congr 1
  congr 1
  apply List.filter_congr
  intro x hx
  have he := h x hx
  by_cases hp : P x <;> by_cases hq : Q x <;> simp_all

theorem tally_or {α : Type} (l : List α) (P Q : α → Prop) :
    tally l (fun x => P x∨Q x)=tally l P+tally l Q-tally l (fun x => P x∧Q x) := by
  classical
  induction l with
  | nil => simp [tally]
  | cons x l ih =>
    by_cases hp : P x <;> by_cases hq : Q x <;>
      simp [tally,hp,hq] at ih ⊢ <;> omega

theorem tally_or3 {α : Type} (l : List α) (P Q R : α → Prop) :
    tally l (fun x => P x∨Q x∨R x)=
      tally l P+tally l Q+tally l R-
      tally l (fun x => P x∧Q x)-tally l (fun x => P x∧R x)-tally l (fun x => Q x∧R x)+
      tally l (fun x => P x∧Q x∧R x) := by
  classical
  induction l with
  | nil => simp [tally]
  | cons x l ih =>
    by_cases hp : P x <;> by_cases hq : Q x <;> by_cases hr : R x <;>
      simp [tally,hp,hq,hr] at ih ⊢ <;> omega

theorem tally_and_not {α : Type} (l : List α) (P Q : α → Prop) :
    tally l (fun x => P x∧¬Q x)=tally l P-tally l (fun x => P x∧Q x) := by
  classical
  induction l with
  | nil => simp [tally]
  | cons x l ih =>
    by_cases hp : P x <;> by_cases hq : Q x <;>
      simp [tally,hp,hq] at ih ⊢ <;> omega

theorem tally_map {α β : Type} (l : List α) (f : α → β) (P : β → Prop) :
    tally (l.map f) P=tally l (fun x => P (f x)) := by
  classical
  simp only [tally,List.filter_map,List.length_map,Function.comp_def]

theorem tally_true {α : Type} (l : List α) : tally l (fun _ => True)=(l.length:Int) := by
  classical
  rw [tally_eq_filter]
  have h : l.filter (fun _ => decide True)=l := List.filter_eq_self.mpr (by intro x _; decide)
  rw [h]

theorem tally_false {α : Type} (l : List α) : tally l (fun _ => False)=0 := by
  classical
  simp [tally]

theorem tally_append {α : Type} (l k : List α) (P : α → Prop) :
    tally (l++k) P=tally l P+tally k P := by
  classical
  simp only [tally,List.filter_append,List.length_append,Int.natCast_add]

inductive BoxMode where | rect | lower | upper deriving DecidableEq

def orientedPoints : BoxMode → Int → Int → Int → Int → Int → List (Int×Int)
  | .rect,al,au,bl,bu,_ => rectanglePoints al au bl bu
  | .lower,al,au,bl,bu,c => trianglePoints al au bl bu c
  | .upper,al,au,bl,bu,c => (trianglePoints bl bu al au (-c)).map Prod.swap

def orientedCount2 : BoxMode → Int → Int → Int → Int → Int → Int
  | .rect,al,au,bl,bu,_ => rectangleBox2 al au bl bu
  | .lower,al,au,bl,bu,c => triangleBox2 al au bl bu c
  | .upper,al,au,bl,bu,c => triangleBox2 bl bu al au (-c)

theorem orientedPoints_mem (mode : BoxMode) (al au bl bu c x y : Int) :
    (x,y)∈orientedPoints mode al au bl bu c ↔
      al≤x ∧ x≤au ∧ bl≤y ∧ y≤bu ∧
      (mode=.lower → x+c≤y) ∧ (mode=.upper → y≤x+c) := by
  cases mode
  · simp [orientedPoints,rectanglePoints_mem]
  · simp [orientedPoints,trianglePoints_mem]
  · simp only [orientedPoints,List.mem_map]
    constructor
    · rintro ⟨⟨a,b⟩,hm,he⟩
      have h := (trianglePoints_mem _ _ _ _ _ _ _).mp hm
      have hx : b=x := congrArg Prod.fst he
      have hy : a=y := congrArg Prod.snd he
      simp_all
      omega
    · intro h
      refine ⟨(y,x),(trianglePoints_mem _ _ _ _ _ _ _).mpr ?_,rfl⟩
      simp_all
      omega

theorem orientedPoints_nodup (mode : BoxMode) (al au bl bu c : Int) :
    (orientedPoints mode al au bl bu c).Nodup := by
  cases mode
  · exact trianglePoints_nodup _ _ _ _ _
  · exact trianglePoints_nodup _ _ _ _ _
  · apply LuRazEnumeration.nodup_map_injective _ ?_ _ (trianglePoints_nodup _ _ _ _ _)
    intro a b h
    have hs := congrArg Prod.swap h
    simpa only [Prod.swap_swap] using hs

theorem orientedPoints_length (mode : BoxMode) (al au bl bu c : Int) :
    2*((orientedPoints mode al au bl bu c).length:Int)=orientedCount2 mode al au bl bu c := by
  cases mode
  · exact rectanglePoints_length _ _ _ _
  · exact trianglePoints_length _ _ _ _ _
  · simpa only [orientedPoints,orientedCount2,List.length_map] using trianglePoints_length bl bu al au (-c)

theorem tally_oriented_clip (mode : BoxMode) (al au bl bu c xl xu yl yu : Int) :
    2*tally (orientedPoints mode al au bl bu c)
      (fun p => xl≤p.1 ∧ p.1≤xu ∧ yl≤p.2 ∧ p.2≤yu)=
      orientedCount2 mode (max al xl) (min au xu) (max bl yl) (min bu yu) c := by
  classical
  have hp : ((orientedPoints mode al au bl bu c).filter
      (fun p => decide (xl≤p.1 ∧ p.1≤xu ∧ yl≤p.2 ∧ p.2≤yu))).Perm
      (orientedPoints mode (max al xl) (min au xu) (max bl yl) (min bu yu) c) := by
    apply (List.perm_ext_iff_of_nodup
      (List.Nodup.sublist List.filter_sublist (orientedPoints_nodup _ _ _ _ _ _))
      (orientedPoints_nodup _ _ _ _ _ _)).mpr
    intro p
    obtain ⟨x,y⟩ := p
    simp only [List.mem_filter,orientedPoints_mem,decide_eq_true_eq]
    cases mode <;> simp_all <;> omega
  rw [tally_eq_filter]
  rw [hp.length_eq,orientedPoints_length]

theorem tally_oriented_predicate (mode : BoxMode) (al au bl bu c xl xu yl yu : Int)
    (P : (Int×Int) → Prop) (C : Prop) [Decidable C]
    (hx0 : al≤xl) (hx1 : xu≤au) (hy0 : bl≤yl) (hy1 : yu≤bu)
    (he : ∀ p∈orientedPoints mode al au bl bu c,
      P p↔C ∧ xl≤p.1 ∧ p.1≤xu ∧ yl≤p.2 ∧ p.2≤yu) :
    2*tally (orientedPoints mode al au bl bu c) P=
      if C then orientedCount2 mode xl xu yl yu c else 0 := by
  classical
  by_cases hc : C
  · rw [ite_eq_left hc]
    have ht : tally (orientedPoints mode al au bl bu c) P=
        tally (orientedPoints mode al au bl bu c)
          (fun p => xl≤p.1 ∧ p.1≤xu ∧ yl≤p.2 ∧ p.2≤yu) := by
      apply tally_congr
      intro p hp
      exact (he p hp).trans (by simp only [hc,true_and])
    rw [ht,tally_oriented_clip]
    have h0 : max al xl=xl := by omega
    have h1 : min au xu=xu := by omega
    have h2 : max bl yl=yl := by omega
    have h3 : min bu yu=yu := by omega
    rw [h0,h1,h2,h3]
  · rw [ite_eq_right hc]
    have ht : tally (orientedPoints mode al au bl bu c) P=
        tally (orientedPoints mode al au bl bu c) (fun _ => False) := by
      apply tally_congr
      intro p hp
      exact (he p hp).trans (by simp only [hc,false_and])
    rw [ht,tally_false]
    rfl

def guardedCount2 : BoxMode → Int → Int → Int → Int → Int → Int
  | .rect,al,au,bl,bu,_ => if al≤au ∧ bl≤bu then 2*pos (au-al+1)*pos (bu-bl+1) else 0
  | .lower,al,au,bl,bu,c => triangleBox2 al au bl bu c
  | .upper,al,au,bl,bu,c => triangleBox2 bl bu al au (-c)

theorem orientedCount2_guarded (mode : BoxMode) (al au bl bu c : Int) :
    orientedCount2 mode al au bl bu c=guardedCount2 mode al au bl bu c := by
  cases mode
  · by_cases ha : al≤au
    · by_cases hb : bl≤bu
      · simp [orientedCount2,rectangleBox2,guardedCount2,ha,hb]
      · have hz : pos (bu-bl+1)=0 := by unfold pos; omega
        simp [orientedCount2,rectangleBox2,guardedCount2,ha,hb,hz]
    · have hz : pos (au-al+1)=0 := by unfold pos; omega
      simp [orientedCount2,rectangleBox2,guardedCount2,ha,hz]
  · rfl
  · rfl

#print axioms tally_or
#print axioms tally_or3
#print axioms tally_and_not
#print axioms tally_oriented_clip
#print axioms tally_oriented_predicate
end
end LuRazLattice
