import Std

namespace LuRazSixRowSpectrum

/-- Exact point counts for the 43 disjoint difference groups. Generated
from the same integer interval expressions as pointwise_group_counts_ast.json. -/
def removedCountR2 (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then (1) else (if ((e) = (3)) then (0:Int) else (if ((e) = (4)) then (0:Int) else (if ((((2)*q + 1) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int))))))

def removedCountR3 (q e : Int) : Int :=
  (if ((e) = (1)) then (1) else (if ((e) = (2)) then (1) else (if ((e) = (3)) then (0:Int) else (if ((e) = (4)) then (0:Int) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)))) ∨ ((((if ((((2)*q + 1) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((2)*q + 1) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int))))) then (1) else (0:Int))))))

def removedCountR4 (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then (0:Int) else (if ((e) = (3)) then (2) else (if ((e) = (4)) then (0:Int) else (((2) * (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)))) ∨ ((e) = ((3)*q + 1))) then (1) else (0:Int))) + (if (((((if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)))) ∧ ((((1) ≤ ((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)) + (1))) ∧ (((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)) + (1)) ≤ (1))) ∧ (((e + 1) ≤ ((3)*q + 1)) ∨ (((3)*q + 2) ≤ (e))))) then (1) else (0:Int)))))))

def removedCountR5 (q e : Int) : Int :=
  (if ((e) = (1)) then (1) else (if ((e) = (2)) then (0:Int) else (if ((e) = (3)) then (1) else (if ((e) = (4)) then (0:Int) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)))) ∨ ((e) = ((3)*q + 1))) then (1) else (0:Int))))))

def removedCountR6C_regular (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then ((2)*q + -5) else (if ((e) = (3)) then ((2)*q + -5) else (if ((e) = (4)) then (0:Int) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)))) ∨ ((e) = ((3)*q + 1))) then ((2)*q + -5) else ((max (0:Int) (((min (q + 1) ((-2)*q + e)) - (4)) + (1))) + (max (0:Int) (((min ((2)*q) ((-2)*q + e + 1)) - (q + 4)) + (1)))))))))

def removedCountR6C_exception (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then (1) else (if ((e) = (3)) then (1) else (if ((e) = (4)) then (0:Int) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)))) ∨ ((((if ((((3)*q + 1) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((3)*q + 1) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int))))) then (1) else (0:Int))))))

def removedCountR6D (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then ((2)*q + -4) else (if ((e) = (3)) then ((2)*q + -4) else (if ((e) = (4)) then (0:Int) else (if ((((if ((((2)*q + 1) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((2)*q + 1) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)))) then ((2)*q + -4) else (((max (0:Int) (((q + 1) - (max (4) (e))) + (1))) + (max (0:Int) ((((2)*q + -1) - (max (q + 3) (e))) + (1)))) + (1)))))))

def removedCountR7fresh (q e : Int) : Int :=
  (if ((e) = (1)) then (3) else (if ((e) = (2)) then (3) else (if ((e) = (3)) then (3) else (if ((e) = (4)) then (0:Int) else ((((2) * (if (((((if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q + -2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q + -2))) then (1) else (0:Int)))) ∨ ((e) = ((4)*q))) then (1) else (0:Int))) + (if ((((if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)))) then (1) else (0:Int))) + (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((4)*q + -2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((4)*q + -2))) then (1) else (0:Int)))) ∨ ((e) = ((4)*q))) then (1) else (0:Int)))))))

def removedCountR7E (q e : Int) : Int :=
  (if ((e) = (1)) then (q + -2) else (if ((e) = (2)) then (q + -2) else (if ((e) = (3)) then (q + -2) else (if ((e) = (4)) then (0:Int) else (if ((((if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)))) then (q + -2) else (max (0:Int) (((q + 1) - (max (4) (e))) + (1))))))))

def removedCountR7D (q e : Int) : Int :=
  (if ((e) = (1)) then ((2)*q + -4) else (if ((e) = (2)) then ((2)*q + -4) else (if ((e) = (3)) then ((2)*q + -4) else (if ((e) = (4)) then (0:Int) else (if ((((if ((((2)*q + 1) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((2)*q + 1) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)))) then ((2)*q + -4) else (max (0:Int) ((((2)*q + -1) - (max (4) (e))) + (1))))))))

def removedCountR10 (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then (2) else (if ((e) = (3)) then (0:Int) else (if ((e) = (4)) then (2) else ((max (0:Int) (((min ((2)*q + 3) (e)) - ((2)*q + 2)) + (1))) * (if (((5) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int)))))))

def removedCountR11J (q e : Int) : Int :=
  (if ((e) = (1)) then ((2)*q + -3) else (if ((e) = (2)) then ((2)*q + -3) else (if ((e) = (3)) then (0:Int) else (if ((e) = (4)) then ((2)*q + -3) else ((max (0:Int) (((min ((2)*q + 1) (e)) - (5)) + (1))) * (if (((5) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int)))))))

def removedCountR11AJ (q e : Int) : Int :=
  (if ((e) = (1)) then (q + -2) else (if ((e) = (2)) then (q + -2) else (if ((e) = (3)) then (0:Int) else (if ((e) = (4)) then (q + -2) else (if ((((if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)))) then (q + -2) else ((max (0:Int) (((min ((2)*q + 1) (e)) - (q + 4)) + (1))) * (if (((5) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int))))))))

def removedCountR11AK (q e : Int) : Int :=
  (if ((e) = (1)) then (2) else (if ((e) = (2)) then (2) else (if ((e) = (3)) then (0:Int) else (if ((e) = (4)) then (2) else (if ((((if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)))) then (2) else ((max (0:Int) (((min ((2)*q + 3) (e)) - ((2)*q + 2)) + (1))) * (if (((5) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int))))))))

def removedCountR12 (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then (0:Int) else (if ((e) = (3)) then (4) else (if ((e) = (4)) then (4) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) ∨ ((e) = ((4)*q))) then (4) else (((2) * (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)))) ∨ ((e) = ((3)*q + 1))) then (1) else (0:Int))) + ((2) * (if ((((if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)))) then (1) else (0:Int)))))))))

def removedCountR13CJ (q e : Int) : Int :=
  (if ((e) = (1)) then (q + -2) else (if ((e) = (2)) then (0:Int) else (if ((e) = (3)) then (q + -2) else (if ((e) = (4)) then (q + -2) else (if ((e) = ((3)*q + 1)) then (q + -2) else (max (0:Int) ((((3)*q + -1) - (max ((2)*q + 2) (e))) + (1))))))))

def removedCountR13ZJ (q e : Int) : Int :=
  (if ((e) = (1)) then ((2)*q + -4) else (if ((e) = (2)) then (0:Int) else (if ((e) = (3)) then ((2)*q + -4) else (if ((e) = (4)) then ((2)*q + -4) else (if ((e) = ((4)*q)) then ((2)*q + -4) else (max (0:Int) ((((4)*q + -3) - (max ((2)*q + 2) (e))) + (1))))))))

def removedCountR13CZJ (q e : Int) : Int :=
  (if ((e) = (1)) then (q + -2) else (if ((e) = (2)) then (0:Int) else (if ((e) = (3)) then (q + -2) else (if ((e) = (4)) then (q + -2) else (if (((e) = ((3)*q + 1)) ∨ ((e) = ((4)*q))) then (q + -2) else (max (0:Int) ((((3)*q + -1) - (max ((2)*q + 2) (e))) + (1))))))))

def removedCountR13points (q e : Int) : Int :=
  (if ((e) = (1)) then (3) else (if ((e) = (2)) then (0:Int) else (if ((e) = (3)) then (3) else (if ((e) = (4)) then (3) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) ∨ ((e) = ((4)*q))) then (3) else ((if ((((if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)))) then (1) else (0:Int)) + (if ((e) = ((4)*q + -1)) then (1) else (0:Int))))))))

def removedCountR14points (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then (3) else (if ((e) = (3)) then (3) else (if ((e) = (4)) then (3) else ((((2) * (if (((5) ≤ (e)) ∧ ((e) ≤ ((4)*q + -2))) then (1) else (0:Int))) + (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ (q + 3))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ (q + 3))) then (1) else (0:Int)))) ∨ ((((if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int))))) then (1) else (0:Int))) + (if ((e) = ((4)*q)) then (1) else (0:Int)))))))

def removedCountR14line (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then ((2)*q + -4) else (if ((e) = (3)) then ((2)*q + -4) else (if ((e) = (4)) then ((2)*q + -4) else (if ((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) then ((2)*q + -4) else (max (0:Int) (((min ((4)*q + -1) (e)) - ((2)*q + 4)) + (1))))))))

def removedCountR14C (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then ((2)*q + -5) else (if ((e) = (3)) then ((2)*q + -5) else (if ((e) = (4)) then ((2)*q + -5) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)))) ∨ ((e) = ((3)*q + 1))) then ((2)*q + -5) else ((max (0:Int) (((min ((4)*q + -1) (e)) - ((2)*q + 4)) + (1))) - (if (((3)*q + 2) ≤ (e)) then (1) else (0:Int))))))))

def removedCountR15points (q e : Int) : Int :=
  (if ((e) = (1)) then (2) else (if ((e) = (2)) then (2) else (if ((e) = (3)) then (2) else (if ((e) = (4)) then (2) else ((if (((((if (((5) ≤ (e)) ∧ ((e) ≤ (q + 3))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ (q + 3))) then (1) else (0:Int)))) ∨ ((((if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int))))) then (1) else (0:Int)) + (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) ∨ ((((if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q + -2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q + -2))) then (1) else (0:Int)))) ∨ ((e) = ((4)*q))) then (1) else (0:Int)))))))

def removedCountR15right (q e : Int) : Int :=
  (if ((e) = (1)) then ((2)*q + -3) else (if ((e) = (2)) then ((2)*q + -3) else (if ((e) = (3)) then ((2)*q + -3) else (if ((e) = (4)) then ((2)*q + -3) else (if ((e) = ((4)*q)) then ((2)*q + -3) else ((max (0:Int) (((min ((2)*q + 2) (e)) - (6)) + (1))) * (if (((5) ≤ (e)) ∧ ((e) ≤ ((4)*q + -2))) then (1) else (0:Int))))))))

def removedCountR15gap (q e : Int) : Int :=
  (if ((e) = (1)) then (q + -1) else (if ((e) = (2)) then (q + -1) else (if ((e) = (3)) then (q + -1) else (if ((e) = (4)) then (q + -1) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)))) ∨ ((e) = ((4)*q))) then (q + -1) else ((max (0:Int) (((min ((2)*q + 2) (e)) - (q + 4)) + (1))) * (if (((5) ≤ (e)) ∧ ((e) ≤ ((4)*q + -2))) then (1) else (0:Int))))))))

def removedCountR15line (q e : Int) : Int :=
  (if ((e) = (1)) then ((2)*q + -4) else (if ((e) = (2)) then ((2)*q + -4) else (if ((e) = (3)) then ((2)*q + -4) else (if ((e) = (4)) then ((2)*q + -4) else (if ((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) then ((2)*q + -4) else (max (0:Int) (((min ((4)*q + -1) (e)) - ((2)*q + 4)) + (1))))))))

def removedCountR15short (q e : Int) : Int :=
  (if ((e) = (1)) then ((2)*q + -4) else (if ((e) = (2)) then ((2)*q + -4) else (if ((e) = (3)) then ((2)*q + -4) else (if ((e) = (4)) then ((2)*q + -4) else (((2) * (max (0:Int) (((q + 1) - (max (4) (e))) + (1)))) + ((max (0:Int) (((min ((2)*q + 3) (e)) - ((2)*q + 2)) + (1))) * (q + -2)))))))

def removedGroupCounts (q e : Int) : List Int :=
  [removedCountR2 q e,
   removedCountR3 q e,
   removedCountR4 q e,
   removedCountR5 q e,
   removedCountR6C_regular q e,
   removedCountR6C_exception q e,
   removedCountR6D q e,
   removedCountR7fresh q e,
   removedCountR7E q e,
   removedCountR7D q e,
   removedCountR10 q e,
   removedCountR11J q e,
   removedCountR11AJ q e,
   removedCountR11AK q e,
   removedCountR12 q e,
   removedCountR13CJ q e,
   removedCountR13ZJ q e,
   removedCountR13CZJ q e,
   removedCountR13points q e,
   removedCountR14points q e,
   removedCountR14line q e,
   removedCountR14C q e,
   removedCountR15points q e,
   removedCountR15right q e,
   removedCountR15gap q e,
   removedCountR15line q e,
   removedCountR15short q e]

def addedCountN4 (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then (0:Int) else (if ((e) = (3)) then (2) else (if ((e) = (4)) then (0:Int) else (((2) * (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) ∨ ((e) = ((3)*q + 1)) ∨ ((e) = ((4)*q + -1))) then (1) else (0:Int))) + (if (((((if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)))) ∧ ((((1) ≤ ((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1))) ∧ (((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (1))) ∧ (((e + 1) ≤ ((3)*q + 1)) ∨ (((3)*q + 2) ≤ (e))) ∧ (((e + 1) ≤ ((4)*q + -1)) ∨ (((4)*q) ≤ (e))))) then (1) else (0:Int)))))))

def addedCountN5 (q e : Int) : Int :=
  (if ((e) = (1)) then (7) else (if ((e) = (2)) then (0:Int) else (if ((e) = (3)) then (7) else (if ((e) = (4)) then (0:Int) else ((((((((0:Int) + (if ((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)))) then (1) else (0:Int))) + (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) ∨ ((e) = ((3)*q + 1)) ∨ ((e) = ((4)*q + -1))) then (1) else (0:Int))) + (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)))) ∨ (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) ∨ ((e) = ((3)*q + 1)) ∨ ((e) = ((4)*q + -1)))) then (1) else (0:Int))) + (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)))) ∨ (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q))) then (1) else (0:Int)))) ∨ (((e) = ((4)*q + -1)) ∨ ((e) = ((4)*q))))) then (1) else (0:Int))) + (if ((((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) ∨ ((e) = ((3)*q + 1)) ∨ ((e) = ((4)*q + -1))) ∨ (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q))) then (1) else (0:Int)))) ∨ (((e) = ((4)*q + -1)) ∨ ((e) = ((4)*q))))) then (1) else (0:Int))) + (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)))) ∨ ((((if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int))))) then (1) else (0:Int))) + (if ((((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) ∨ ((e) = ((3)*q + 1)) ∨ ((e) = ((4)*q + -1))) ∨ ((((if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int))))) then (1) else (0:Int)))))))

def addedCountN6C_regular (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then ((2)*q + -5) else (if ((e) = (3)) then ((2)*q + -5) else (if ((e) = (4)) then (0:Int) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) ∨ ((e) = ((3)*q + 1))) then ((2)*q + -5) else ((max (0:Int) (((min (q + 1) ((-2)*q + e)) - (4)) + (1))) + (max (0:Int) (((min ((2)*q) ((-2)*q + e + 1)) - (q + 4)) + (1)))))))))

def addedCountN6C_exception (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then (1) else (if ((e) = (3)) then (1) else (if ((e) = (4)) then (0:Int) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) ∨ ((((if ((((3)*q + 1) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((3)*q + 1) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int))))) then (1) else (0:Int))))))

def addedCountN6E (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then ((2)*q + -3) else (if ((e) = (3)) then ((2)*q + -3) else (if ((e) = (4)) then (0:Int) else (if ((((if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)))) then ((2)*q + -3) else ((max (0:Int) (((q + 1) - (max (4) (e))) + (1))) + (max (0:Int) ((((2)*q + 1) - (max (q + 3) (e))) + (1)))))))))

def addedCountN7C_regular (q e : Int) : Int :=
  (if ((e) = (1)) then ((2)*q + -5) else (if ((e) = (2)) then ((2)*q + -5) else (if ((e) = (3)) then ((2)*q + -5) else (if ((e) = (4)) then (0:Int) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) ∨ ((e) = ((3)*q + 1))) then ((2)*q + -5) else ((max (0:Int) (((min (q + 1) ((-2)*q + e)) - (4)) + (1))) + (max (0:Int) (((min ((2)*q) ((-2)*q + e + 1)) - (q + 4)) + (1)))))))))

def addedCountN7C_exception (q e : Int) : Int :=
  (if ((e) = (1)) then (1) else (if ((e) = (2)) then (1) else (if ((e) = (3)) then (1) else (if ((e) = (4)) then (0:Int) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) ∨ ((((if ((((3)*q + 1) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((3)*q + 1) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int))))) then (1) else (0:Int))))))

def addedCountN7right (q e : Int) : Int :=
  (if ((e) = (1)) then (q + -1) else (if ((e) = (2)) then (q + -1) else (if ((e) = (3)) then (q + -1) else (if ((e) = (4)) then (0:Int) else (if ((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 2))) then (1) else (0:Int)))) then (q + -1) else ((max (0:Int) (((min ((4)*q + -1) (e)) - ((3)*q + 2)) + (1))) + (if ((((if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((3)*q + 2) ≤ (e)) ∧ ((e) ≤ ((4)*q + -1))) then (1) else (0:Int)))) then (1) else (0:Int))))))))

def addedCountN7point (q e : Int) : Int :=
  (if ((e) = (1)) then (1) else (if ((e) = (2)) then (1) else (if ((e) = (3)) then (1) else (if ((e) = (4)) then (0:Int) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ ((2)*q + 1))) then (1) else (0:Int)))) ∨ ((((if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if ((((2)*q + 3) ≤ (e)) ∧ ((e) ≤ ((4)*q))) then (1) else (0:Int))))) then (1) else (0:Int))))))

def addedCountN10 (q e : Int) : Int :=
  (if ((e) = (1)) then (0:Int) else (if ((e) = (2)) then (3) else (if ((e) = (3)) then (0:Int) else (if ((e) = (4)) then (3) else (if ((e) = ((4)*q)) then (3) else ((max (0:Int) (((min ((2)*q + 3) (e)) - ((2)*q + 1)) + (1))) * (if (((5) ≤ (e)) ∧ ((e) ≤ ((4)*q + -2))) then (1) else (0:Int))))))))

def addedCountN11J (q e : Int) : Int :=
  (if ((e) = (1)) then ((2)*q + -3) else (if ((e) = (2)) then ((2)*q + -3) else (if ((e) = (3)) then (0:Int) else (if ((e) = (4)) then ((2)*q + -3) else (if ((e) = ((4)*q)) then ((2)*q + -3) else ((max (0:Int) (((min ((2)*q + 1) (e)) - (5)) + (1))) * (if (((5) ≤ (e)) ∧ ((e) ≤ ((4)*q + -2))) then (1) else (0:Int))))))))

def addedCountN11AJ (q e : Int) : Int :=
  (if ((e) = (1)) then (q + -2) else (if ((e) = (2)) then (q + -2) else (if ((e) = (3)) then (0:Int) else (if ((e) = (4)) then (q + -2) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)))) ∨ ((e) = ((4)*q))) then (q + -2) else ((max (0:Int) (((min ((2)*q + 1) (e)) - (q + 4)) + (1))) * (if (((5) ≤ (e)) ∧ ((e) ≤ ((4)*q + -2))) then (1) else (0:Int))))))))

def addedCountN11AK (q e : Int) : Int :=
  (if ((e) = (1)) then (2) else (if ((e) = (2)) then (2) else (if ((e) = (3)) then (0:Int) else (if ((e) = (4)) then (2) else (if (((((if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)) + (1)) ≤ (0:Int)) ∨ ((1) ≤ (if (((5) ≤ (e)) ∧ ((e) ≤ (q + 2))) then (1) else (0:Int)))) ∨ ((e) = ((4)*q))) then (2) else ((max (0:Int) (((min ((2)*q + 3) (e)) - ((2)*q + 2)) + (1))) * (if (((5) ≤ (e)) ∧ ((e) ≤ ((4)*q + -2))) then (1) else (0:Int))))))))

def addedCountN13plain (q e : Int) : Int :=
  (if ((e) = (1)) then (q + -1) else (if ((e) = (2)) then (0:Int) else (if ((e) = (3)) then (q + -1) else (if ((e) = (4)) then (q + -1) else (max (0:Int) ((((3)*q) - (max ((2)*q + 2) (e))) + (1)))))))

def addedCountN13isolated (q e : Int) : Int :=
  (if ((e) = (1)) then (q + -2) else (if ((e) = (2)) then (0:Int) else (if ((e) = (3)) then (q + -2) else (if ((e) = (4)) then (q + -2) else (if (((e) = ((3)*q + 1)) ∨ ((e) = ((4)*q + -1))) then (q + -2) else (max (0:Int) ((((3)*q + -1) - (max ((2)*q + 2) (e))) + (1))))))))

def addedCountN13right (q e : Int) : Int :=
  (if ((e) = (1)) then (q + -3) else (if ((e) = (2)) then (0:Int) else (if ((e) = (3)) then (q + -3) else (if ((e) = (4)) then (q + -3) else (if ((e) = ((4)*q + -1)) then (q + -3) else (max (0:Int) ((((4)*q + -3) - (max ((3)*q + 1) (e))) + (1))))))))

def addedGroupCounts (q e : Int) : List Int :=
  [addedCountN4 q e,
   addedCountN5 q e,
   addedCountN6C_regular q e,
   addedCountN6C_exception q e,
   addedCountN6E q e,
   addedCountN7C_regular q e,
   addedCountN7C_exception q e,
   addedCountN7right q e,
   addedCountN7point q e,
   addedCountN10 q e,
   addedCountN11J q e,
   addedCountN11AJ q e,
   addedCountN11AK q e,
   addedCountN13plain q e,
   addedCountN13isolated q e,
   addedCountN13right q e]

end LuRazSixRowSpectrum
