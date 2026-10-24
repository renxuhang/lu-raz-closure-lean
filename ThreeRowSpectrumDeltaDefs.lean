import ThreeRowSpectrumPolynomial

namespace LuRazThreeRow
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- A one-parameter family `[a,last]`, with `lo ≤ a ≤ hi`, and a fixed part. -/
def tailLower (lo hi last e : Int) (fixed : Prop) [Decidable fixed] : Int :=
  if fixed then hi-lo+1 else
  if e≤last then max 0 (min hi e-lo+1) else 0

/-- A one-parameter family `[first,b]`, with `lo ≤ b ≤ hi`, and a fixed part. -/
def tailUpper (lo hi first e : Int) (fixed : Prop) [Decidable fixed] : Int :=
  if fixed then hi-lo+1 else
  if first≤e then max 0 (hi-max lo e+1) else 0

def tailMark (P : Prop) [Decidable P] : Int := if P then 1 else 0

/-- The twelve removed groups, in the order of the explicit symmetric-difference table. -/
def removedTailGroups (q e : Int) : List Int :=
  [ -- R5: E, A∪E, [5,n].
    tailMark (2*q+3≤e ∧ e≤4*q) +
      tailMark ((5≤e ∧ e≤q+2) ∨ (2*q+3≤e ∧ e≤4*q)) +
      tailMark (5≤e ∧ e≤4*q),
    -- R6_line, R6_point.
    tailLower (2*q+4) (4*q) (4*q) e (5≤e ∧ e≤2*q+1),
    tailMark ((5≤e ∧ e≤2*q+2) ∨ e=3*q+1 ∨ e=4*q),
    -- R7_line, R7_points.
    tailLower (2*q+4) (4*q) (4*q) e (5≤e ∧ e≤2*q+1),
    tailMark ((5≤e ∧ e≤2*q+2) ∨ e=3*q+1 ∨ e=4*q) +
      tailMark ((5≤e ∧ e≤2*q+1) ∨ (2*q+3≤e ∧ e≤4*q)),
    -- R13_right, R13_gap, R13_points.
    tailLower 6 (2*q+1) (4*q) e False,
    tailLower (q+4) (2*q+1) (4*q) e (5≤e ∧ e≤q+2),
    tailMark ((5≤e ∧ e≤2*q) ∨ e=4*q) +
      tailMark ((5≤e ∧ e≤2*q) ∨ (3*q+2≤e ∧ e≤4*q)) +
      tailMark ((5≤e ∧ e≤2*q) ∨ (2*q+3≤e ∧ e≤4*q)),
    -- R15_left, R15_points, R15_right, R15_isolated.
    tailLower (2*q+4) (4*q-1) (4*q) e (5≤e ∧ e≤2*q),
    tailMark ((5≤e ∧ e≤2*q) ∨ (2*q+2≤e ∧ e≤4*q-2) ∨ e=4*q) +
      tailMark ((5≤e ∧ e≤2*q+1) ∨ e=4*q),
    tailUpper (2*q+2) (4*q-3) 5 e (e=4*q),
    tailUpper (2*q+2) (3*q-1) 5 e (e=3*q+1 ∨ e=4*q)
  ]

/-- The eleven added groups, in the order of the explicit symmetric-difference table. -/
def addedTailGroups (q e : Int) : List Int :=
  [ -- N5: Z', Z'∪B, Z'∪C.
    tailMark ((5≤e ∧ e≤2*q) ∨ (4*q-1≤e ∧ e≤4*q)) +
      tailMark ((5≤e ∧ e≤2*q) ∨ (3*q+2≤e ∧ e≤4*q)) +
      tailMark ((5≤e ∧ e≤2*q+2) ∨ e=3*q+1 ∨ (4*q-1≤e ∧ e≤4*q)),
    -- N7: E', A∪E', [5,n−2]∪{n}.
    tailMark ((2*q+3≤e ∧ e≤4*q-2) ∨ e=4*q) +
      tailMark ((5≤e ∧ e≤q+2) ∨ (2*q+3≤e ∧ e≤4*q-2) ∨ e=4*q) +
      tailMark ((5≤e ∧ e≤4*q-2) ∨ e=4*q),
    -- N12: L', L'∪B, L'∪C, L'∪C∪B.
    tailMark ((5≤e ∧ e≤2*q+1) ∨ e=4*q) +
      tailMark ((5≤e ∧ e≤2*q+1) ∨ (3*q+2≤e ∧ e≤4*q)) +
      tailMark ((5≤e ∧ e≤2*q+2) ∨ e=3*q+1 ∨ e=4*q) +
      tailMark ((5≤e ∧ e≤2*q+2) ∨ (3*q+1≤e ∧ e≤4*q)),
    -- N13_points, N13_line, N13_isolated.
    tailMark ((5≤e ∧ e≤2*q+1) ∨ e=4*q) +
      tailMark ((5≤e ∧ e≤2*q+1) ∨ (3*q+2≤e ∧ e≤4*q)),
    tailUpper (2*q+1) (4*q-3) 5 e (4*q-1≤e ∧ e≤4*q),
    tailUpper (2*q+2) (3*q-1) 5 e (e=3*q+1 ∨ (4*q-1≤e ∧ e≤4*q)),
    -- N14_line, N14_isolated (the t=3q+2 member is deleted).
    tailLower (2*q+4) (4*q-1) (4*q) e (5≤e ∧ e≤2*q+1),
    tailLower (2*q+4) (4*q-1) (4*q) e ((5≤e ∧ e≤2*q+2) ∨ e=3*q+1) -
      tailMark ((5≤e ∧ e≤2*q+2) ∨ (3*q+1≤e ∧ e≤4*q)),
    -- N15_right, N15_gap, N15_point.
    tailLower 6 (2*q+2) (4*q-2) e (e=4*q),
    tailLower (q+4) (2*q+2) (4*q-2) e ((5≤e ∧ e≤q+2) ∨ e=4*q),
    tailMark ((5≤e ∧ e≤2*q+1) ∨ (2*q+3≤e ∧ e≤4*q-2) ∨ e=4*q)
  ]

def tailDelta (q e : Int) : Int := (addedTailGroups q e).sum - (removedTailGroups q e).sum

end LuRazThreeRow
