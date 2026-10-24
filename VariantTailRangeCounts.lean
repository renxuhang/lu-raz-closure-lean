import VariantTailCountTools
import VariantFixedTailCounts
import VariantGlobalDifference

namespace LuRazThreeRow
open LuRazClosure LuRazEnumeration LuRazCounting LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
noncomputable section

theorem count_at_nil (e : Nat) : CountAt [] e=0 := by simp [CountAt]

theorem removed134_right_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ((List.range' 6 (2*q-4)).map (fun a => NF134.eval q (.ej a))) e=tailLower 6 (2*(q:Int)+1) (4*(q:Int)) (e:Int) False := by
  try simp only [List.map_map,Function.comp_def]
  have h := count_lower (6) (2*q-4) (fun a => NF134.eval q (.ej a)) e (False) (4*(q:Int)) (by
    intro a ha
    have hb := (range_mem a (6) (2*q-4)).mp ha
    try simp only [false_or,NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I]
    omega)
  have hu : (((6 : Nat):Int)+((2*q-4 : Nat):Int)-1)=2*(q:Int)+1 := by omega
  rw [hu] at h
  by_cases hp : False <;> simpa [tailLower,tailUpper,hp] using h

theorem removed134_gap_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ((List.range' (q+4) (q-2)).map (fun a => NF134.eval q (.aej a))) e=tailLower ((q:Int)+4) (2*(q:Int)+1) (4*(q:Int)) (e:Int) (5≤(e:Int) ∧ (e:Int)≤(q:Int)+2) := by
  try simp only [List.map_map,Function.comp_def]
  have h := count_lower (q+4) (q-2) (fun a => NF134.eval q (.aej a)) e (5≤(e:Int) ∧ (e:Int)≤(q:Int)+2) (4*(q:Int)) (by
    intro a ha
    have hb := (range_mem a (q+4) (q-2)).mp ha
    try simp only [false_or,NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I]
    omega)
  have hu : (((q+4 : Nat):Int)+((q-2 : Nat):Int)-1)=2*(q:Int)+1 := by omega
  rw [hu] at h
  have hs : ((q+4 : Nat):Int)=(q:Int)+4 := by omega
  rw [hs] at h
  by_cases hp : 5≤(e:Int) ∧ (e:Int)≤(q:Int)+2 <;> simpa [tailLower,tailUpper,hp] using h

theorem loss_left_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ((List.range' (2*q+4) (2*q-4)).map (fun a => NFFull.eval q (.noH1ZL a))) e=tailLower (2*(q:Int)+4) (4*(q:Int)-1) (4*(q:Int)) (e:Int) (5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) := by
  try simp only [List.map_map,Function.comp_def]
  have h := count_lower (2*q+4) (2*q-4) (fun a => NFFull.eval q (.noH1ZL a)) e (5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) (4*(q:Int)) (by
    intro a ha
    have hb := (range_mem a (2*q+4) (2*q-4)).mp ha
    try simp only [false_or,NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I]
    omega)
  have hu : (((2*q+4 : Nat):Int)+((2*q-4 : Nat):Int)-1)=4*(q:Int)-1 := by omega
  rw [hu] at h
  have hs : ((2*q+4 : Nat):Int)=2*(q:Int)+4 := by omega
  rw [hs] at h
  by_cases hp : 5≤(e:Int) ∧ (e:Int)≤2*(q:Int) <;> simpa [tailLower,tailUpper,hp] using h

theorem loss_right_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ((List.range' (2*q+2) (2*q-4)).map (fun a => NFFull.eval q (.rightGap a (4*q)))) e=tailUpper (2*(q:Int)+2) (4*(q:Int)-3) 5 (e:Int) ((e:Int)=4*(q:Int)) := by
  try simp only [List.map_map,Function.comp_def]
  have h := count_upper (2*q+2) (2*q-4) (fun a => NFFull.eval q (.rightGap a (4*q))) e ((e:Int)=4*(q:Int)) (5) (by
    intro a ha
    have hb := (range_mem a (2*q+2) (2*q-4)).mp ha
    try simp only [false_or,NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I]
    omega)
  have hu : (((2*q+2 : Nat):Int)+((2*q-4 : Nat):Int)-1)=4*(q:Int)-3 := by omega
  rw [hu] at h
  have hs : ((2*q+2 : Nat):Int)=2*(q:Int)+2 := by omega
  rw [hs] at h
  by_cases hp : (e:Int)=4*(q:Int) <;> simpa [tailLower,tailUpper,hp] using h

theorem loss_isolated_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ((List.range' (2*q+2) (q-2)).map (fun a => NFFull.eval q (.isolatedR a (4*q)))) e=tailUpper (2*(q:Int)+2) (3*(q:Int)-1) 5 (e:Int) ((e:Int)=3*(q:Int)+1 ∨ (e:Int)=4*(q:Int)) := by
  try simp only [List.map_map,Function.comp_def]
  have h := count_upper (2*q+2) (q-2) (fun a => NFFull.eval q (.isolatedR a (4*q))) e ((e:Int)=3*(q:Int)+1 ∨ (e:Int)=4*(q:Int)) (5) (by
    intro a ha
    have hb := (range_mem a (2*q+2) (q-2)).mp ha
    try simp only [false_or,NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I]
    omega)
  have hu : (((2*q+2 : Nat):Int)+((q-2 : Nat):Int)-1)=3*(q:Int)-1 := by omega
  rw [hu] at h
  have hs : ((2*q+2 : Nat):Int)=2*(q:Int)+2 := by omega
  rw [hs] at h
  by_cases hp : (e:Int)=3*(q:Int)+1 ∨ (e:Int)=4*(q:Int) <;> simpa [tailLower,tailUpper,hp] using h

theorem fresh134_zz_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ((List.range' (2*q+1) (2*q-3)).map (fun a => Fresh134.eval q (.zz a))) e=tailUpper (2*(q:Int)+1) (4*(q:Int)-3) 5 (e:Int) (4*(q:Int)-1≤(e:Int) ∧ (e:Int)≤4*(q:Int)) := by
  try simp only [List.map_map,Function.comp_def]
  have h := count_upper (2*q+1) (2*q-3) (fun a => Fresh134.eval q (.zz a)) e (4*(q:Int)-1≤(e:Int) ∧ (e:Int)≤4*(q:Int)) (5) (by
    intro a ha
    have hb := (range_mem a (2*q+1) (2*q-3)).mp ha
    try simp only [false_or,NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I]
    omega)
  have hu : (((2*q+1 : Nat):Int)+((2*q-3 : Nat):Int)-1)=4*(q:Int)-3 := by omega
  rw [hu] at h
  have hs : ((2*q+1 : Nat):Int)=2*(q:Int)+1 := by omega
  rw [hs] at h
  by_cases hp : 4*(q:Int)-1≤(e:Int) ∧ (e:Int)≤4*(q:Int) <;> simpa [tailLower,tailUpper,hp] using h

theorem fresh134_cz_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ((List.range' (2*q+2) (q-2)).map (fun a => Fresh134.eval q (.cz a))) e=tailUpper (2*(q:Int)+2) (3*(q:Int)-1) 5 (e:Int) ((e:Int)=3*(q:Int)+1 ∨ (4*(q:Int)-1≤(e:Int) ∧ (e:Int)≤4*(q:Int))) := by
  try simp only [List.map_map,Function.comp_def]
  have h := count_upper (2*q+2) (q-2) (fun a => Fresh134.eval q (.cz a)) e ((e:Int)=3*(q:Int)+1 ∨ (4*(q:Int)-1≤(e:Int) ∧ (e:Int)≤4*(q:Int))) (5) (by
    intro a ha
    have hb := (range_mem a (2*q+2) (q-2)).mp ha
    try simp only [false_or,NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I]
    omega)
  have hu : (((2*q+2 : Nat):Int)+((q-2 : Nat):Int)-1)=3*(q:Int)-1 := by omega
  rw [hu] at h
  have hs : ((2*q+2 : Nat):Int)=2*(q:Int)+2 := by omega
  rw [hs] at h
  by_cases hp : (e:Int)=3*(q:Int)+1 ∨ (4*(q:Int)-1≤(e:Int) ∧ (e:Int)≤4*(q:Int)) <;> simpa [tailLower,tailUpper,hp] using h

theorem addfull_right_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ((List.range' 6 (2*q-3)).map (fun a => AddFull.eval q (.right a))) e=tailLower 6 (2*(q:Int)+2) (4*(q:Int)-2) (e:Int) ((e:Int)=4*(q:Int)) := by
  try simp only [List.map_map,Function.comp_def]
  have h := count_lower (6) (2*q-3) (fun a => AddFull.eval q (.right a)) e ((e:Int)=4*(q:Int)) (4*(q:Int)-2) (by
    intro a ha
    have hb := (range_mem a (6) (2*q-3)).mp ha
    try simp only [false_or,NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I]
    omega)
  have hu : (((6 : Nat):Int)+((2*q-3 : Nat):Int)-1)=2*(q:Int)+2 := by omega
  rw [hu] at h
  by_cases hp : (e:Int)=4*(q:Int) <;> simpa [tailLower,tailUpper,hp] using h

theorem addfull_gap_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ((List.range' (q+4) (q-1)).map (fun a => AddFull.eval q (.gap a))) e=tailLower ((q:Int)+4) (2*(q:Int)+2) (4*(q:Int)-2) (e:Int) ((5≤(e:Int) ∧ (e:Int)≤(q:Int)+2) ∨ (e:Int)=4*(q:Int)) := by
  try simp only [List.map_map,Function.comp_def]
  have h := count_lower (q+4) (q-1) (fun a => AddFull.eval q (.gap a)) e ((5≤(e:Int) ∧ (e:Int)≤(q:Int)+2) ∨ (e:Int)=4*(q:Int)) (4*(q:Int)-2) (by
    intro a ha
    have hb := (range_mem a (q+4) (q-1)).mp ha
    try simp only [false_or,NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I]
    omega)
  have hu : (((q+4 : Nat):Int)+((q-1 : Nat):Int)-1)=2*(q:Int)+2 := by omega
  rw [hu] at h
  have hs : ((q+4 : Nat):Int)=(q:Int)+4 := by omega
  rw [hs] at h
  by_cases hp : (5≤(e:Int) ∧ (e:Int)≤(q:Int)+2) ∨ (e:Int)=4*(q:Int) <;> simpa [tailLower,tailUpper,hp] using h

theorem removed134_points_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt (((List.range 3).map NF134.extra).map (NF134.eval q)) e=tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨ (e:Int)=4*(q:Int)) +
      tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨ (3*(q:Int)+2≤(e:Int) ∧ (e:Int)≤4*(q:Int))) +
      tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨ (2*(q:Int)+3≤(e:Int) ∧ (e:Int)≤4*(q:Int))) := by
  have h0 : mark (NF134.eval q (.extra 0) e)=tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨ (e:Int)=4*(q:Int)) := fixed_tail_mark (NF134.eval q (.extra 0) e) ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨ (e:Int)=4*(q:Int)) (by
    simp [NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I] <;> omega)
  have h1 : mark (NF134.eval q (.extra 1) e)=tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨ (3*(q:Int)+2≤(e:Int) ∧ (e:Int)≤4*(q:Int))) := fixed_tail_mark (NF134.eval q (.extra 1) e) ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨ (3*(q:Int)+2≤(e:Int) ∧ (e:Int)≤4*(q:Int))) (by
    simp [NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I] <;> omega)
  have h2 : mark (NF134.eval q (.extra 2) e)=tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨ (2*(q:Int)+3≤(e:Int) ∧ (e:Int)≤4*(q:Int))) := fixed_tail_mark (NF134.eval q (.extra 2) e) ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨ (2*(q:Int)+3≤(e:Int) ∧ (e:Int)≤4*(q:Int))) (by
    simp [NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I] <;> omega)
  have hr : List.range 3=[0,1,2] := by decide
  simp only [hr,List.map_cons,List.map_nil,count_at_cons,count_at_nil]
  rw [h0,h1,h2]
  omega

theorem loss_points_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ([NFFull.eval q .noH1Exception,NFFull.eval q (.noH2 (4*q))]) e=tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨ (2*(q:Int)+2≤(e:Int) ∧ (e:Int)≤4*(q:Int)-2) ∨ (e:Int)=4*(q:Int)) +
      tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (e:Int)=4*(q:Int)) := by
  have h0 : mark (NFFull.eval q .noH1Exception e)=tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨ (2*(q:Int)+2≤(e:Int) ∧ (e:Int)≤4*(q:Int)-2) ∨ (e:Int)=4*(q:Int)) := fixed_tail_mark (NFFull.eval q .noH1Exception e) ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)) ∨ (2*(q:Int)+2≤(e:Int) ∧ (e:Int)≤4*(q:Int)-2) ∨ (e:Int)=4*(q:Int)) (by
    simp [NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I] <;> omega)
  have h1 : mark (NFFull.eval q (.noH2 (4*q)) e)=tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (e:Int)=4*(q:Int)) := fixed_tail_mark (NFFull.eval q (.noH2 (4*q)) e) ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (e:Int)=4*(q:Int)) (by
    simp [NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I] <;> omega)
  try simp only [List.map_cons,List.map_cons,List.map_nil,count_at_cons,count_at_nil]
  rw [h0,h1]
  omega

theorem fresh134_points_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ([Fresh134.eval q .lp,Fresh134.eval q .lb]) e=tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (e:Int)=4*(q:Int)) +
      tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (3*(q:Int)+2≤(e:Int) ∧ (e:Int)≤4*(q:Int))) := by
  have h0 : mark (Fresh134.eval q .lp e)=tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (e:Int)=4*(q:Int)) := fixed_tail_mark (Fresh134.eval q .lp e) ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (e:Int)=4*(q:Int)) (by
    simp [NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I] <;> omega)
  have h1 : mark (Fresh134.eval q .lb e)=tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (3*(q:Int)+2≤(e:Int) ∧ (e:Int)≤4*(q:Int))) := fixed_tail_mark (Fresh134.eval q .lb e) ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (3*(q:Int)+2≤(e:Int) ∧ (e:Int)≤4*(q:Int))) (by
    simp [NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I] <;> omega)
  try simp only [List.map_cons,List.map_cons,List.map_nil,count_at_cons,count_at_nil]
  rw [h0,h1]
  omega

theorem addfull_point_tail (q e : Nat) (hq : 4≤q) (he : 5≤e) (hen : e≤4*q) :
    CountAt ([AddFull.eval q .point]) e=tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (2*(q:Int)+3≤(e:Int) ∧ (e:Int)≤4*(q:Int)-2) ∨ (e:Int)=4*(q:Int)) := by
  have h0 : mark (AddFull.eval q .point e)=tailMark ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (2*(q:Int)+3≤(e:Int) ∧ (e:Int)≤4*(q:Int)-2) ∨ (e:Int)=4*(q:Int)) := fixed_tail_mark (AddFull.eval q .point e) ((5≤(e:Int) ∧ (e:Int)≤2*(q:Int)+1) ∨ (2*(q:Int)+3≤(e:Int) ∧ (e:Int)≤4*(q:Int)-2) ∨ (e:Int)=4*(q:Int)) (by
    simp [NFFull.eval,FullHead,NF134.eval,T134,Fresh134.eval,AddFull.eval,ZRow,BRow,ERow,ARow,CRow,I] <;> omega)
  try simp only [List.map_cons,List.map_cons,List.map_nil,count_at_cons,count_at_nil]
  rw [h0]
  omega

end
end LuRazThreeRow
