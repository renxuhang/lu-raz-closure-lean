import LuRazFullRawParts
namespace LuRazClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

theorem raw_full_normalizes (q : Nat) (hq : 4≤q) (j : JPart) (hj : JPart.Valid q j)
    (l : LPart) (hl : LPart.Valid q l) (f : FixedGen → Prop)
    (hc : CoreFull (RawFull q j l f)) : FullNormalizes q (RawFull q j l f) := by
  have he := rawFull_explicit q j l f
  have hcaug : CoreFull (FixedAug q (fun e => JPart.eval j e ∨ LPart.eval q l e)
      (f .A) (f .B) (f .C) (f .D) (f .E) (f .Z) (f .K1) (f .K2)) := by
    unfold CoreFull at hc ⊢
    exact ⟨(he 1).mp hc.1,(he 2).mp hc.2.1,(he 3).mp hc.2.2.1,(he 4).mp hc.2.2.2⟩
  have hnorm : FullNormalizes q (FixedAug q (fun e => JPart.eval j e ∨ LPart.eval q l e)
      (f .A) (f .B) (f .C) (f .D) (f .E) (f .Z) (f .K1) (f .K2)) := by
    cases j with
    | none =>
      cases l with
      | none =>
        simp only [JPart.eval,LPart.eval,false_or] at hcaug ⊢
        exact full_normalizes_fixed_only q hq _ _ _ _ _ _ _ _ hcaug
      | some tp =>
        rcases tp with ⟨t,p⟩
        simp only [JPart.eval,LPart.eval,false_or] at hcaug ⊢
        exact full_normalizes_lfixed q t p hq hl.1 hl.2.1 hl.2.2 _ _ _ _ _ _ _ _ hcaug
    | some ab =>
      rcases ab with ⟨a,b⟩
      cases l with
      | none =>
        simp only [JPart.eval,LPart.eval,or_false] at hcaug ⊢
        exact full_normalizes_jfixed q a b hq hj _ _ _ _ _ _ _ _ hcaug
      | some tp =>
        rcases tp with ⟨t,p⟩
        have hs0 : FullNormalizes q (fun e => LRow q t p e ∨ JRow a b e) := lp_j_full_normal q t p a b hq hl.1 hl.2.1 hl.2.2 hj
        have hs := full_normalizes_congr q _ (fun e => JRow a b e ∨ LRow q t p e) hs0 (fun _ => or_comm)
        simpa only [JPart.eval,LPart.eval] using full_normalizes_fixedAug q hq _ hs (f .A) (f .B) (f .C) (f .D) (f .E) (f .Z) (f .K1) (f .K2)
  exact full_normalizes_congr q _ _ hnorm (fun e => (he e).symm)

/-- All full-core members of the entire source closure have a valid candidate normal form. -/
theorem full_closure_normalizes (q : Nat) (hq : 4≤q) (R : Nat → Prop)
    (hg : Generated q R) (hc : CoreFull R) : FullNormalizes q R := by
  classical
  have hs := generated_supported q hq R hg
  obtain ⟨ls,_,hv,he⟩ := hg
  by_cases h0 : 0∈ls
  · refine ⟨.full,True.intro,?_⟩
    intro e
    constructor
    · intro hr
      have hb := hs e hr
      simp only [NFFull.eval,FullHead,I]
      omega
    · intro hn
      simp only [NFFull.eval,FullHead,I] at hn
      have hb : 1≤e ∧ e≤4*q := by omega
      exact (he e).mp ⟨0,h0,(LuRazParametric.row_case_0 q 0 e (by omega) rfl).mpr hb⟩
  · have hvalid : ∀ i∈ls, i≠0 ∧ i≤4*q+2 := by
      intro i hi
      exact ⟨fun h => h0 (h ▸ hi),hv i hi⟩
    obtain ⟨j,hj,l,hl,f,hn⟩ := raw_parts_list q hq ls hvalid
    have hR : ∀ e, R e ↔ RawFull q j l f e := fun e => (he e).symm.trans (hn e)
    have hcore : CoreFull (RawFull q j l f) := by
      unfold CoreFull at hc ⊢
      exact ⟨(hR 1).mp hc.1,(hR 2).mp hc.2.1,(hR 3).mp hc.2.2.1,(hR 4).mp hc.2.2.2⟩
    exact full_normalizes_congr q _ _ (raw_full_normalizes q hq j hj l hl f hcore) (fun e => (hR e).symm)
end LuRazClosure
