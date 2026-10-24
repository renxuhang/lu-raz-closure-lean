import LatticeWeightTools
import SixRowSpectrumPolynomial
namespace LuRazSixRowSpectrum
open LuRazLattice
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
theorem spectrum_coordinate_partition (q : Nat) (hq : 4≤q) :
    List.range' 1 (4*q)=(List.range' (0+1) (0+1)) ++ (List.range' (0+2) (0+1)) ++ (List.range' (0+3) (0+1)) ++ (List.range' (0+4) (0+1)) ++ (List.range' (0+5) (1*q-2)) ++ (List.range' (1*q+3) (0+1)) ++ (List.range' (1*q+4) (1*q-3)) ++ (List.range' (2*q+1) (0+1)) ++ (List.range' (2*q+2) (0+1)) ++ (List.range' (2*q+3) (1*q-2)) ++ (List.range' (3*q+1) (0+1)) ++ (List.range' (3*q+2) (1*q-3)) ++ (List.range' (4*q-1) (0+1)) ++ (List.range' (4*q+0) (0+1)) := by
  have h0 : List.range' (0+1) (4*q+1-(0+1))=
      List.range' (0+1) (0+1) ++ List.range' (0+2) (4*q+1-(0+2)) := by
    have hs : (0+1)+(0+1)=(0+2) := by omega
    have hn : (0+1)+(4*q+1-(0+2))=4*q+1-(0+1) := by omega
    simpa only [hs,hn] using (List.range'_append_1 (s:=(0+1)) (m:=(0+1)) (n:=4*q+1-(0+2))).symm
  have h1 : List.range' (0+2) (4*q+1-(0+2))=
      List.range' (0+2) (0+1) ++ List.range' (0+3) (4*q+1-(0+3)) := by
    have hs : (0+2)+(0+1)=(0+3) := by omega
    have hn : (0+1)+(4*q+1-(0+3))=4*q+1-(0+2) := by omega
    simpa only [hs,hn] using (List.range'_append_1 (s:=(0+2)) (m:=(0+1)) (n:=4*q+1-(0+3))).symm
  have h2 : List.range' (0+3) (4*q+1-(0+3))=
      List.range' (0+3) (0+1) ++ List.range' (0+4) (4*q+1-(0+4)) := by
    have hs : (0+3)+(0+1)=(0+4) := by omega
    have hn : (0+1)+(4*q+1-(0+4))=4*q+1-(0+3) := by omega
    simpa only [hs,hn] using (List.range'_append_1 (s:=(0+3)) (m:=(0+1)) (n:=4*q+1-(0+4))).symm
  have h3 : List.range' (0+4) (4*q+1-(0+4))=
      List.range' (0+4) (0+1) ++ List.range' (0+5) (4*q+1-(0+5)) := by
    have hs : (0+4)+(0+1)=(0+5) := by omega
    have hn : (0+1)+(4*q+1-(0+5))=4*q+1-(0+4) := by omega
    simpa only [hs,hn] using (List.range'_append_1 (s:=(0+4)) (m:=(0+1)) (n:=4*q+1-(0+5))).symm
  have h4 : List.range' (0+5) (4*q+1-(0+5))=
      List.range' (0+5) (1*q-2) ++ List.range' (1*q+3) (4*q+1-(1*q+3)) := by
    have hs : (0+5)+(1*q-2)=(1*q+3) := by omega
    have hn : (1*q-2)+(4*q+1-(1*q+3))=4*q+1-(0+5) := by omega
    simpa only [hs,hn] using (List.range'_append_1 (s:=(0+5)) (m:=(1*q-2)) (n:=4*q+1-(1*q+3))).symm
  have h5 : List.range' (1*q+3) (4*q+1-(1*q+3))=
      List.range' (1*q+3) (0+1) ++ List.range' (1*q+4) (4*q+1-(1*q+4)) := by
    have hs : (1*q+3)+(0+1)=(1*q+4) := by omega
    have hn : (0+1)+(4*q+1-(1*q+4))=4*q+1-(1*q+3) := by omega
    simpa only [hs,hn] using (List.range'_append_1 (s:=(1*q+3)) (m:=(0+1)) (n:=4*q+1-(1*q+4))).symm
  have h6 : List.range' (1*q+4) (4*q+1-(1*q+4))=
      List.range' (1*q+4) (1*q-3) ++ List.range' (2*q+1) (4*q+1-(2*q+1)) := by
    have hs : (1*q+4)+(1*q-3)=(2*q+1) := by omega
    have hn : (1*q-3)+(4*q+1-(2*q+1))=4*q+1-(1*q+4) := by omega
    simpa only [hs,hn] using (List.range'_append_1 (s:=(1*q+4)) (m:=(1*q-3)) (n:=4*q+1-(2*q+1))).symm
  have h7 : List.range' (2*q+1) (4*q+1-(2*q+1))=
      List.range' (2*q+1) (0+1) ++ List.range' (2*q+2) (4*q+1-(2*q+2)) := by
    have hs : (2*q+1)+(0+1)=(2*q+2) := by omega
    have hn : (0+1)+(4*q+1-(2*q+2))=4*q+1-(2*q+1) := by omega
    simpa only [hs,hn] using (List.range'_append_1 (s:=(2*q+1)) (m:=(0+1)) (n:=4*q+1-(2*q+2))).symm
  have h8 : List.range' (2*q+2) (4*q+1-(2*q+2))=
      List.range' (2*q+2) (0+1) ++ List.range' (2*q+3) (4*q+1-(2*q+3)) := by
    have hs : (2*q+2)+(0+1)=(2*q+3) := by omega
    have hn : (0+1)+(4*q+1-(2*q+3))=4*q+1-(2*q+2) := by omega
    simpa only [hs,hn] using (List.range'_append_1 (s:=(2*q+2)) (m:=(0+1)) (n:=4*q+1-(2*q+3))).symm
  have h9 : List.range' (2*q+3) (4*q+1-(2*q+3))=
      List.range' (2*q+3) (1*q-2) ++ List.range' (3*q+1) (4*q+1-(3*q+1)) := by
    have hs : (2*q+3)+(1*q-2)=(3*q+1) := by omega
    have hn : (1*q-2)+(4*q+1-(3*q+1))=4*q+1-(2*q+3) := by omega
    simpa only [hs,hn] using (List.range'_append_1 (s:=(2*q+3)) (m:=(1*q-2)) (n:=4*q+1-(3*q+1))).symm
  have h10 : List.range' (3*q+1) (4*q+1-(3*q+1))=
      List.range' (3*q+1) (0+1) ++ List.range' (3*q+2) (4*q+1-(3*q+2)) := by
    have hs : (3*q+1)+(0+1)=(3*q+2) := by omega
    have hn : (0+1)+(4*q+1-(3*q+2))=4*q+1-(3*q+1) := by omega
    simpa only [hs,hn] using (List.range'_append_1 (s:=(3*q+1)) (m:=(0+1)) (n:=4*q+1-(3*q+2))).symm
  have h11 : List.range' (3*q+2) (4*q+1-(3*q+2))=
      List.range' (3*q+2) (1*q-3) ++ List.range' (4*q-1) (4*q+1-(4*q-1)) := by
    have hs : (3*q+2)+(1*q-3)=(4*q-1) := by omega
    have hn : (1*q-3)+(4*q+1-(4*q-1))=4*q+1-(3*q+2) := by omega
    simpa only [hs,hn] using (List.range'_append_1 (s:=(3*q+2)) (m:=(1*q-3)) (n:=4*q+1-(4*q-1))).symm
  have h12 : List.range' (4*q-1) (4*q+1-(4*q-1))=
      List.range' (4*q-1) (0+1) ++ List.range' (4*q+0) (4*q+1-(4*q+0)) := by
    have hs : (4*q-1)+(0+1)=(4*q+0) := by omega
    have hn : (0+1)+(4*q+1-(4*q+0))=4*q+1-(4*q-1) := by omega
    simpa only [hs,hn] using (List.range'_append_1 (s:=(4*q-1)) (m:=(0+1)) (n:=4*q+1-(4*q+0))).symm
  have hz : 4*q+1-(0+1)=4*q := by omega
  have ht : 4*q+1-(4*q+0)=(0+1) := by omega
  rw [hz] at h0
  rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,ht]
  simp only [List.append_assoc]
theorem spectrum_piece0 (q e : Nat) (hq : 4≤q)
    (hl : (0+1)≤e) (hu : e≤(0+1)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((19)*(q:Int)*(q:Int)+(1)*(q:Int)+(0))) e := by
  unfold spectrumPolynomial2
  have h0 : (e:Int)=1 := by omega
  simp only [ite_eq_left h0]
  grind
#print axioms spectrum_piece0
theorem spectrum_piece1 (q e : Nat) (hq : 4≤q)
    (hl : (0+2)≤e) (hu : e≤(0+2)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((17)*(q:Int)*(q:Int)+(-1)*(q:Int)+(0))) e := by
  unfold spectrumPolynomial2
  have h0 : ¬((e:Int)=1) := by omega
  have h1 : (e:Int)=2 := by omega
  simp only [ite_eq_right h0,ite_eq_left h1]
  grind
#print axioms spectrum_piece1
theorem spectrum_piece2 (q e : Nat) (hq : 4≤q)
    (hl : (0+3)≤e) (hu : e≤(0+3)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((17)*(q:Int)*(q:Int)+(-1)*(q:Int)+(-2))) e := by
  unfold spectrumPolynomial2
  have h0 : ¬((e:Int)=1) := by omega
  have h1 : ¬((e:Int)=2) := by omega
  have h2 : (e:Int)=3 := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_left h2]
  grind
#print axioms spectrum_piece2
theorem spectrum_piece3 (q e : Nat) (hq : 4≤q)
    (hl : (0+4)≤e) (hu : e≤(0+4)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((16)*(q:Int)*(q:Int)+(10)*(q:Int)+(-22))) e := by
  unfold spectrumPolynomial2
  have h0 : ¬((e:Int)=1) := by omega
  have h1 : ¬((e:Int)=2) := by omega
  have h2 : ¬((e:Int)=3) := by omega
  have h3 : (e:Int)=4 := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_left h3]
  grind
#print axioms spectrum_piece3
theorem spectrum_piece4 (q e : Nat) (hq : 4≤q)
    (hl : (0+5)≤e) (hu : e≤(1*q+2)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (-1:Int)*(e:Int)*(e:Int)+((2)*(q:Int)+(5))*(e:Int)+((18)*(q:Int)*(q:Int)+(-4)*(q:Int)+(-4))) e := by
  unfold spectrumPolynomial2
  have h0 : ¬((e:Int)=1) := by omega
  have h1 : ¬((e:Int)=2) := by omega
  have h2 : ¬((e:Int)=3) := by omega
  have h3 : ¬((e:Int)=4) := by omega
  have h4 : (e:Int)≤(q:Int)+2 := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_left h4]
  grind
#print axioms spectrum_piece4
theorem spectrum_piece5 (q e : Nat) (hq : 4≤q)
    (hl : (1*q+3)≤e) (hu : e≤(1*q+3)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((18)*(q:Int)*(q:Int)+(-4)*(q:Int)+(4))) e := by
  unfold spectrumPolynomial2
  have h0 : ¬((e:Int)=1) := by omega
  have h1 : ¬((e:Int)=2) := by omega
  have h2 : ¬((e:Int)=3) := by omega
  have h3 : ¬((e:Int)=4) := by omega
  have h4 : ¬((e:Int)≤(q:Int)+2) := by omega
  have h5 : (e:Int)=(q:Int)+3 := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_left h5]
  grind
#print axioms spectrum_piece5
theorem spectrum_piece6 (q e : Nat) (hq : 4≤q)
    (hl : (1*q+4)≤e) (hu : e≤(2*q+0)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (-2:Int)*(e:Int)*(e:Int)+((4)*(q:Int)+(18))*(e:Int)+((16)*(q:Int)*(q:Int)+(-24)*(q:Int)+(-32))) e := by
  unfold spectrumPolynomial2
  have h0 : ¬((e:Int)=1) := by omega
  have h1 : ¬((e:Int)=2) := by omega
  have h2 : ¬((e:Int)=3) := by omega
  have h3 : ¬((e:Int)=4) := by omega
  have h4 : ¬((e:Int)≤(q:Int)+2) := by omega
  have h5 : ¬((e:Int)=(q:Int)+3) := by omega
  have h6 : (e:Int)≤2*(q:Int) := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_left h6]
  grind
#print axioms spectrum_piece6
theorem spectrum_piece7 (q e : Nat) (hq : 4≤q)
    (hl : (2*q+1)≤e) (hu : e≤(2*q+1)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((16)*(q:Int)*(q:Int)+(12)*(q:Int)+(-24))) e := by
  unfold spectrumPolynomial2
  have h0 : ¬((e:Int)=1) := by omega
  have h1 : ¬((e:Int)=2) := by omega
  have h2 : ¬((e:Int)=3) := by omega
  have h3 : ¬((e:Int)=4) := by omega
  have h4 : ¬((e:Int)≤(q:Int)+2) := by omega
  have h5 : ¬((e:Int)=(q:Int)+3) := by omega
  have h6 : ¬((e:Int)≤2*(q:Int)) := by omega
  have h7 : (e:Int)=2*(q:Int)+1 := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_left h7]
  grind
#print axioms spectrum_piece7
theorem spectrum_piece8 (q e : Nat) (hq : 4≤q)
    (hl : (2*q+2)≤e) (hu : e≤(2*q+2)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((16)*(q:Int)*(q:Int)+(10)*(q:Int)+(-20))) e := by
  unfold spectrumPolynomial2
  have h0 : ¬((e:Int)=1) := by omega
  have h1 : ¬((e:Int)=2) := by omega
  have h2 : ¬((e:Int)=3) := by omega
  have h3 : ¬((e:Int)=4) := by omega
  have h4 : ¬((e:Int)≤(q:Int)+2) := by omega
  have h5 : ¬((e:Int)=(q:Int)+3) := by omega
  have h6 : ¬((e:Int)≤2*(q:Int)) := by omega
  have h7 : ¬((e:Int)=2*(q:Int)+1) := by omega
  have h8 : (e:Int)=2*(q:Int)+2 := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_left h8]
  grind
#print axioms spectrum_piece8
theorem spectrum_piece9 (q e : Nat) (hq : 4≤q)
    (hl : (2*q+3)≤e) (hu : e≤(3*q+0)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (-1:Int)*(e:Int)*(e:Int)+((4)*(q:Int)+(-3))*(e:Int)+((12)*(q:Int)*(q:Int)+(16)*(q:Int)+(-14))) e := by
  unfold spectrumPolynomial2
  have h0 : ¬((e:Int)=1) := by omega
  have h1 : ¬((e:Int)=2) := by omega
  have h2 : ¬((e:Int)=3) := by omega
  have h3 : ¬((e:Int)=4) := by omega
  have h4 : ¬((e:Int)≤(q:Int)+2) := by omega
  have h5 : ¬((e:Int)=(q:Int)+3) := by omega
  have h6 : ¬((e:Int)≤2*(q:Int)) := by omega
  have h7 : ¬((e:Int)=2*(q:Int)+1) := by omega
  have h8 : ¬((e:Int)=2*(q:Int)+2) := by omega
  have h9 : (e:Int)≤3*(q:Int) := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_left h9]
  grind
#print axioms spectrum_piece9
theorem spectrum_piece10 (q e : Nat) (hq : 4≤q)
    (hl : (3*q+1)≤e) (hu : e≤(3*q+1)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((17)*(q:Int)*(q:Int)+(11)*(q:Int)+(-24))) e := by
  unfold spectrumPolynomial2
  have h0 : ¬((e:Int)=1) := by omega
  have h1 : ¬((e:Int)=2) := by omega
  have h2 : ¬((e:Int)=3) := by omega
  have h3 : ¬((e:Int)=4) := by omega
  have h4 : ¬((e:Int)≤(q:Int)+2) := by omega
  have h5 : ¬((e:Int)=(q:Int)+3) := by omega
  have h6 : ¬((e:Int)≤2*(q:Int)) := by omega
  have h7 : ¬((e:Int)=2*(q:Int)+1) := by omega
  have h8 : ¬((e:Int)=2*(q:Int)+2) := by omega
  have h9 : ¬((e:Int)≤3*(q:Int)) := by omega
  have h10 : (e:Int)=3*(q:Int)+1 := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_left h10]
  grind
#print axioms spectrum_piece10
theorem spectrum_piece11 (q e : Nat) (hq : 4≤q)
    (hl : (3*q+2)≤e) (hu : e≤(4*q-2)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (-2:Int)*(e:Int)*(e:Int)+((16)*(q:Int)+(-6))*(e:Int)+((-14)*(q:Int)*(q:Int)+(26)*(q:Int)+(0))) e := by
  unfold spectrumPolynomial2
  have h0 : ¬((e:Int)=1) := by omega
  have h1 : ¬((e:Int)=2) := by omega
  have h2 : ¬((e:Int)=3) := by omega
  have h3 : ¬((e:Int)=4) := by omega
  have h4 : ¬((e:Int)≤(q:Int)+2) := by omega
  have h5 : ¬((e:Int)=(q:Int)+3) := by omega
  have h6 : ¬((e:Int)≤2*(q:Int)) := by omega
  have h7 : ¬((e:Int)=2*(q:Int)+1) := by omega
  have h8 : ¬((e:Int)=2*(q:Int)+2) := by omega
  have h9 : ¬((e:Int)≤3*(q:Int)) := by omega
  have h10 : ¬((e:Int)=3*(q:Int)+1) := by omega
  have h11 : (e:Int)≤4*(q:Int)-2 := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_left h11]
  grind
#print axioms spectrum_piece11
theorem spectrum_piece12 (q e : Nat) (hq : 4≤q)
    (hl : (4*q-1)≤e) (hu : e≤(4*q-1)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((18)*(q:Int)*(q:Int)+(6)*(q:Int)+(-2))) e := by
  unfold spectrumPolynomial2
  have h0 : ¬((e:Int)=1) := by omega
  have h1 : ¬((e:Int)=2) := by omega
  have h2 : ¬((e:Int)=3) := by omega
  have h3 : ¬((e:Int)=4) := by omega
  have h4 : ¬((e:Int)≤(q:Int)+2) := by omega
  have h5 : ¬((e:Int)=(q:Int)+3) := by omega
  have h6 : ¬((e:Int)≤2*(q:Int)) := by omega
  have h7 : ¬((e:Int)=2*(q:Int)+1) := by omega
  have h8 : ¬((e:Int)=2*(q:Int)+2) := by omega
  have h9 : ¬((e:Int)≤3*(q:Int)) := by omega
  have h10 : ¬((e:Int)=3*(q:Int)+1) := by omega
  have h11 : ¬((e:Int)≤4*(q:Int)-2) := by omega
  have h12 : (e:Int)=4*(q:Int)-1 := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_right h11,ite_eq_left h12]
  grind
#print axioms spectrum_piece12
theorem spectrum_piece13 (q e : Nat) (hq : 4≤q)
    (hl : (4*q+0)≤e) (hu : e≤(4*q+0)) :
    spectrumPolynomial2 (q:Int) (e:Int)=(fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((18)*(q:Int)*(q:Int)+(2)*(q:Int)+(-4))) e := by
  unfold spectrumPolynomial2
  have h0 : ¬((e:Int)=1) := by omega
  have h1 : ¬((e:Int)=2) := by omega
  have h2 : ¬((e:Int)=3) := by omega
  have h3 : ¬((e:Int)=4) := by omega
  have h4 : ¬((e:Int)≤(q:Int)+2) := by omega
  have h5 : ¬((e:Int)=(q:Int)+3) := by omega
  have h6 : ¬((e:Int)≤2*(q:Int)) := by omega
  have h7 : ¬((e:Int)=2*(q:Int)+1) := by omega
  have h8 : ¬((e:Int)=2*(q:Int)+2) := by omega
  have h9 : ¬((e:Int)≤3*(q:Int)) := by omega
  have h10 : ¬((e:Int)=3*(q:Int)+1) := by omega
  have h11 : ¬((e:Int)≤4*(q:Int)-2) := by omega
  have h12 : ¬((e:Int)=4*(q:Int)-1) := by omega
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,ite_eq_right h4,ite_eq_right h5,ite_eq_right h6,ite_eq_right h7,ite_eq_right h8,ite_eq_right h9,ite_eq_right h10,ite_eq_right h11,ite_eq_right h12]
  grind
#print axioms spectrum_piece13
theorem spectrum_polynomial_sum (q : Nat) (hq : 4≤q) :
    ((List.range' 1 (4*q)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))).sum=
      69*(q:Int)*(q:Int)*(q:Int)+15*(q:Int)*(q:Int)-18*(q:Int)-34 := by
  have hm0 : (List.range' (0+1) (0+1)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (0+1) (0+1)).map (fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((19)*(q:Int)*(q:Int)+(1)*(q:Int)+(0))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (0+1) (0+1)).mp he
    exact spectrum_piece0 q e hq (by omega) (by omega)
  have hs0 := six_sum_quadratic (0:Int) ((0)*(q:Int)+(0)) ((19)*(q:Int)*(q:Int)+(1)*(q:Int)+(0)) (0+1) (0+1)
  have hm1 : (List.range' (0+2) (0+1)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (0+2) (0+1)).map (fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((17)*(q:Int)*(q:Int)+(-1)*(q:Int)+(0))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (0+2) (0+1)).mp he
    exact spectrum_piece1 q e hq (by omega) (by omega)
  have hs1 := six_sum_quadratic (0:Int) ((0)*(q:Int)+(0)) ((17)*(q:Int)*(q:Int)+(-1)*(q:Int)+(0)) (0+2) (0+1)
  have hm2 : (List.range' (0+3) (0+1)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (0+3) (0+1)).map (fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((17)*(q:Int)*(q:Int)+(-1)*(q:Int)+(-2))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (0+3) (0+1)).mp he
    exact spectrum_piece2 q e hq (by omega) (by omega)
  have hs2 := six_sum_quadratic (0:Int) ((0)*(q:Int)+(0)) ((17)*(q:Int)*(q:Int)+(-1)*(q:Int)+(-2)) (0+3) (0+1)
  have hm3 : (List.range' (0+4) (0+1)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (0+4) (0+1)).map (fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((16)*(q:Int)*(q:Int)+(10)*(q:Int)+(-22))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (0+4) (0+1)).mp he
    exact spectrum_piece3 q e hq (by omega) (by omega)
  have hs3 := six_sum_quadratic (0:Int) ((0)*(q:Int)+(0)) ((16)*(q:Int)*(q:Int)+(10)*(q:Int)+(-22)) (0+4) (0+1)
  have hm4 : (List.range' (0+5) (1*q-2)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (0+5) (1*q-2)).map (fun e : Nat => (-1:Int)*(e:Int)*(e:Int)+((2)*(q:Int)+(5))*(e:Int)+((18)*(q:Int)*(q:Int)+(-4)*(q:Int)+(-4))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (0+5) (1*q-2)).mp he
    exact spectrum_piece4 q e hq (by omega) (by omega)
  have hs4 := six_sum_quadratic (-1:Int) ((2)*(q:Int)+(5)) ((18)*(q:Int)*(q:Int)+(-4)*(q:Int)+(-4)) (0+5) (1*q-2)
  have hm5 : (List.range' (1*q+3) (0+1)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (1*q+3) (0+1)).map (fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((18)*(q:Int)*(q:Int)+(-4)*(q:Int)+(4))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (1*q+3) (0+1)).mp he
    exact spectrum_piece5 q e hq (by omega) (by omega)
  have hs5 := six_sum_quadratic (0:Int) ((0)*(q:Int)+(0)) ((18)*(q:Int)*(q:Int)+(-4)*(q:Int)+(4)) (1*q+3) (0+1)
  have hm6 : (List.range' (1*q+4) (1*q-3)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (1*q+4) (1*q-3)).map (fun e : Nat => (-2:Int)*(e:Int)*(e:Int)+((4)*(q:Int)+(18))*(e:Int)+((16)*(q:Int)*(q:Int)+(-24)*(q:Int)+(-32))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (1*q+4) (1*q-3)).mp he
    exact spectrum_piece6 q e hq (by omega) (by omega)
  have hs6 := six_sum_quadratic (-2:Int) ((4)*(q:Int)+(18)) ((16)*(q:Int)*(q:Int)+(-24)*(q:Int)+(-32)) (1*q+4) (1*q-3)
  have hm7 : (List.range' (2*q+1) (0+1)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (2*q+1) (0+1)).map (fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((16)*(q:Int)*(q:Int)+(12)*(q:Int)+(-24))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (2*q+1) (0+1)).mp he
    exact spectrum_piece7 q e hq (by omega) (by omega)
  have hs7 := six_sum_quadratic (0:Int) ((0)*(q:Int)+(0)) ((16)*(q:Int)*(q:Int)+(12)*(q:Int)+(-24)) (2*q+1) (0+1)
  have hm8 : (List.range' (2*q+2) (0+1)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (2*q+2) (0+1)).map (fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((16)*(q:Int)*(q:Int)+(10)*(q:Int)+(-20))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (2*q+2) (0+1)).mp he
    exact spectrum_piece8 q e hq (by omega) (by omega)
  have hs8 := six_sum_quadratic (0:Int) ((0)*(q:Int)+(0)) ((16)*(q:Int)*(q:Int)+(10)*(q:Int)+(-20)) (2*q+2) (0+1)
  have hm9 : (List.range' (2*q+3) (1*q-2)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (2*q+3) (1*q-2)).map (fun e : Nat => (-1:Int)*(e:Int)*(e:Int)+((4)*(q:Int)+(-3))*(e:Int)+((12)*(q:Int)*(q:Int)+(16)*(q:Int)+(-14))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (2*q+3) (1*q-2)).mp he
    exact spectrum_piece9 q e hq (by omega) (by omega)
  have hs9 := six_sum_quadratic (-1:Int) ((4)*(q:Int)+(-3)) ((12)*(q:Int)*(q:Int)+(16)*(q:Int)+(-14)) (2*q+3) (1*q-2)
  have hm10 : (List.range' (3*q+1) (0+1)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (3*q+1) (0+1)).map (fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((17)*(q:Int)*(q:Int)+(11)*(q:Int)+(-24))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (3*q+1) (0+1)).mp he
    exact spectrum_piece10 q e hq (by omega) (by omega)
  have hs10 := six_sum_quadratic (0:Int) ((0)*(q:Int)+(0)) ((17)*(q:Int)*(q:Int)+(11)*(q:Int)+(-24)) (3*q+1) (0+1)
  have hm11 : (List.range' (3*q+2) (1*q-3)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (3*q+2) (1*q-3)).map (fun e : Nat => (-2:Int)*(e:Int)*(e:Int)+((16)*(q:Int)+(-6))*(e:Int)+((-14)*(q:Int)*(q:Int)+(26)*(q:Int)+(0))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (3*q+2) (1*q-3)).mp he
    exact spectrum_piece11 q e hq (by omega) (by omega)
  have hs11 := six_sum_quadratic (-2:Int) ((16)*(q:Int)+(-6)) ((-14)*(q:Int)*(q:Int)+(26)*(q:Int)+(0)) (3*q+2) (1*q-3)
  have hm12 : (List.range' (4*q-1) (0+1)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (4*q-1) (0+1)).map (fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((18)*(q:Int)*(q:Int)+(6)*(q:Int)+(-2))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (4*q-1) (0+1)).mp he
    exact spectrum_piece12 q e hq (by omega) (by omega)
  have hs12 := six_sum_quadratic (0:Int) ((0)*(q:Int)+(0)) ((18)*(q:Int)*(q:Int)+(6)*(q:Int)+(-2)) (4*q-1) (0+1)
  have hm13 : (List.range' (4*q+0) (0+1)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))=
      (List.range' (4*q+0) (0+1)).map (fun e : Nat => (0:Int)*(e:Int)*(e:Int)+((0)*(q:Int)+(0))*(e:Int)+((18)*(q:Int)*(q:Int)+(2)*(q:Int)+(-4))) := by
    apply List.map_congr_left
    intro e he
    have hb := (LuRazEnumeration.range_mem e (4*q+0) (0+1)).mp he
    exact spectrum_piece13 q e hq (by omega) (by omega)
  have hs13 := six_sum_quadratic (0:Int) ((0)*(q:Int)+(0)) ((18)*(q:Int)*(q:Int)+(2)*(q:Int)+(-4)) (4*q+0) (0+1)
  have ht : 6*((List.range' 1 (4*q)).map (fun e : Nat => spectrumPolynomial2 (q:Int) (e:Int))).sum=
      6*(69*(q:Int)*(q:Int)*(q:Int)+15*(q:Int)*(q:Int)-18*(q:Int)-34) := by
    rw [spectrum_coordinate_partition q hq]
    simp only [List.map_append,List.sum_append]
    rw [hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
    simp only [Int.mul_add]
    rw [hs0,hs1,hs2,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11,hs12,hs13]
    unfold quadraticAnti
    have hc0 : (((0+1):Nat):Int)=((0)*(q:Int)+(1)) := by omega
    have hc1 : (((0+2):Nat):Int)=((0)*(q:Int)+(2)) := by omega
    have hc2 : (((0+3):Nat):Int)=((0)*(q:Int)+(3)) := by omega
    have hc3 : (((0+4):Nat):Int)=((0)*(q:Int)+(4)) := by omega
    have hc4 : (((0+5):Nat):Int)=((0)*(q:Int)+(5)) := by omega
    have hc5 : (((1*q-2):Nat):Int)=((1)*(q:Int)+(-2)) := by omega
    have hc6 : (((1*q+3):Nat):Int)=((1)*(q:Int)+(3)) := by omega
    have hc7 : (((1*q+4):Nat):Int)=((1)*(q:Int)+(4)) := by omega
    have hc8 : (((1*q-3):Nat):Int)=((1)*(q:Int)+(-3)) := by omega
    have hc9 : (((2*q+1):Nat):Int)=((2)*(q:Int)+(1)) := by omega
    have hc10 : (((2*q+2):Nat):Int)=((2)*(q:Int)+(2)) := by omega
    have hc11 : (((2*q+3):Nat):Int)=((2)*(q:Int)+(3)) := by omega
    have hc12 : (((3*q+1):Nat):Int)=((3)*(q:Int)+(1)) := by omega
    have hc13 : (((3*q+2):Nat):Int)=((3)*(q:Int)+(2)) := by omega
    have hc14 : (((4*q-1):Nat):Int)=((4)*(q:Int)+(-1)) := by omega
    have hc15 : (((4*q+0):Nat):Int)=((4)*(q:Int)+(0)) := by omega
    simp only [hc0,hc1,hc2,hc3,hc4,hc5,hc6,hc7,hc8,hc9,hc10,hc11,hc12,hc13,hc14,hc15]
    grind
  omega
#print axioms spectrum_coordinate_partition
#print axioms spectrum_polynomial_sum
end LuRazSixRowSpectrum
