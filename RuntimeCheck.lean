import LuRazTotalClosure
/-! Executable transcription check only; no theorem imports this file. -/
set_option synthInstance.maxSize 4096
namespace LuRazRuntime
open LuRazClosure
def dec14 (q : Nat) (z : NF14) (e : Nat) : Decidable (z.eval q e) := by
  cases z <;> simp only [NF14.eval,JRow,ARow,BRow,I] <;> infer_instance
def mask14 (q : Nat) (z : NF14) : Nat :=
  (List.range (4*q)).foldl (fun acc k =>
    letI := dec14 q z (k+1)
    if z.eval q (k+1) then acc ||| (Nat.shiftLeft 1 k) else acc) 0
def dec23 (q : Nat) (z : NF23) (e : Nat) : Decidable (z.eval q e) := by
  cases z <;> simp only [NF23.eval,LRow,LNormal,I] <;> infer_instance
def mask23 (q : Nat) (z : NF23) : Nat :=
  (List.range (4*q)).foldl (fun acc k =>
    letI := dec23 q z (k+1)
    if z.eval q (k+1) then acc ||| (Nat.shiftLeft 1 k) else acc) 0
def decSmall (q : Nat) (z : NFSmall) (e : Nat) : Decidable (z.eval q e) := by
  cases z <;> simp only [NFSmall.eval,ARow,BRow,CRow,DRow,ERow,I] <;> infer_instance
def maskSmall (q : Nat) (z : NFSmall) : Nat :=
  (List.range (4*q)).foldl (fun acc k =>
    letI := decSmall q z (k+1)
    if z.eval q (k+1) then acc ||| (Nat.shiftLeft 1 k) else acc) 0
def dec24 (q : Nat) (z : NF24) (e : Nat) : Decidable (z.eval q e) := by
  cases z <;> simp only [NF24.eval,K1Row,K2Row,DRow,BRow,I] <;> infer_instance
def mask24 (q : Nat) (z : NF24) : Nat :=
  (List.range (4*q)).foldl (fun acc k =>
    letI := dec24 q z (k+1)
    if z.eval q (k+1) then acc ||| (Nat.shiftLeft 1 k) else acc) 0
def dec124 (q : Nat) (z : NF124) (e : Nat) : Decidable (z.eval q e) := by
  cases z with
  | interval a k => simp only [NF124.eval,T124,I]; infer_instance
  | agap a k => simp only [NF124.eval,T124,ARow,I]; infer_instance
  | ak z => letI := dec24 q z e; simp only [NF124.eval,ARow,I]; infer_instance
def mask124 (q : Nat) (z : NF124) : Nat :=
  (List.range (4*q)).foldl (fun acc k =>
    letI := dec124 q z (k+1)
    if z.eval q (k+1) then acc ||| (Nat.shiftLeft 1 k) else acc) 0
def dec234 (q : Nat) (z : NF234) (e : Nat) : Decidable (z.eval q e) := by
  cases z <;> simp only [NF234.eval,T234,I] <;> infer_instance
def mask234 (q : Nat) (z : NF234) : Nat :=
  (List.range (4*q)).foldl (fun acc k =>
    letI := dec234 q z (k+1)
    if z.eval q (k+1) then acc ||| (Nat.shiftLeft 1 k) else acc) 0
def dec123 (q : Nat) (z : NF123) (e : Nat) : Decidable (z.eval q e) := by
  cases z <;> simp only [NF123.eval,NF123.body,NF23.eval,TwoPiece,LRow,LNormal,I] <;> infer_instance
def mask123 (q : Nat) (z : NF123) : Nat :=
  (List.range (4*q)).foldl (fun acc k =>
    letI := dec123 q z (k+1)
    if z.eval q (k+1) then acc ||| (Nat.shiftLeft 1 k) else acc) 0
def dec134 (q : Nat) (z : NF134) (e : Nat) : Decidable (z.eval q e) := by
  cases z <;> simp only [NF134.eval,T134,ZRow,BRow,ERow,I] <;> infer_instance
def mask134 (q : Nat) (z : NF134) : Nat :=
  (List.range (4*q)).foldl (fun acc k =>
    letI := dec134 q z (k+1)
    if z.eval q (k+1) then acc ||| (Nat.shiftLeft 1 k) else acc) 0
def decFull (q : Nat) (z : NFFull) (e : Nat) : Decidable (z.eval q e) := by
  cases z <;> simp only [NFFull.eval,FullHead,I] <;> infer_instance

def maskFull (q : Nat) (z : NFFull) : Nat :=
  (List.range (4*q)).foldl (fun acc k =>
    letI := decFull q z (k+1)
    if z.eval q (k+1) then acc ||| (Nat.shiftLeft 1 k) else acc) 0

def decSource (q i e : Nat) : Decidable (LuRazParametric.Row q i e) := by
  unfold LuRazParametric.Row
  infer_instance

def maskSource (q i : Nat) : Nat :=
  (List.range (4*q)).foldl (fun acc k =>
    letI := decSource q i (k+1)
    if LuRazParametric.Row q i (k+1) then acc ||| (Nat.shiftLeft 1 k) else acc) 0

def run : IO Unit := do
  let mut lines : List String := []
  let mut sources : List String := []
  for q in [4,6,13,33,65] do
    for k in [0,1,2,3,4,5] do
      let xs := (enumSmall k).map (maskSmall q)
      lines := lines ++ [s!"{q}\t{k}\t" ++ String.intercalate "," (xs.map toString)]
    let xs := (enum14 q).map (mask14 q)
    lines := lines ++ [s!"{q}\t9\t" ++ String.intercalate "," (xs.map toString)]
    let xs := (enum23 q).map (mask23 q)
    lines := lines ++ [s!"{q}\t6\t" ++ String.intercalate "," (xs.map toString)]
    let xs := (all24).map (mask24 q)
    lines := lines ++ [s!"{q}\t10\t" ++ String.intercalate "," (xs.map toString)]
    let xs := (enum124 q).map (mask124 q)
    lines := lines ++ [s!"{q}\t11\t" ++ String.intercalate "," (xs.map toString)]
    let xs := (enum234 q).map (mask234 q)
    lines := lines ++ [s!"{q}\t14\t" ++ String.intercalate "," (xs.map toString)]
    let xs := (enum123 q).map (mask123 q)
    lines := lines ++ [s!"{q}\t7\t" ++ String.intercalate "," (xs.map toString)]
    let xs := (enum134 q).map (mask134 q)
    lines := lines ++ [s!"{q}\t13\t" ++ String.intercalate "," (xs.map toString)]
    let xs := (enumFull q).map (maskFull q)
    lines := lines ++ [s!"{q}\t15\t" ++ String.intercalate "," (xs.map toString)]
    let rs := (List.range (4*q+3)).map (maskSource q)
    sources := sources ++ [s!"{q}\t" ++ String.intercalate "," (rs.map toString)]
    IO.println s!"q={q}: exported all 14 classes and {rs.length} source rows"
  IO.FS.writeFile "runtime-masks.tsv" (String.intercalate "\n" lines ++ "\n")
  IO.FS.writeFile "runtime-source-masks.tsv" (String.intercalate "\n" sources ++ "\n")
#eval run
end LuRazRuntime
