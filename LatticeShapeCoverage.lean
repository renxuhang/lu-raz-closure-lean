import LatticeShapeProperties
import ShapeSurjectivity_NFSmall
import ShapeSurjectivity_NF23
import ShapeSurjectivity_NF123
import ShapeSurjectivity_NF14
import ShapeSurjectivity_NF24
import ShapeSurjectivity_NF124
import ShapeSurjectivity_NF134
import ShapeSurjectivity_NF234
import ShapeSurjectivity_NFFull
namespace LuRazClosure.SourcePieces
theorem identify_valid (q : Nat) (hq : 4≤q) (z : Shape) (hz : z.Valid q) :
    let p := identify q z
    Domain q p.1 p.2.1 p.2.2 ∧ decode q p.1 p.2.1 p.2.2=z := by
  cases z with
  | small z => exact inverse_valid_NFSmall q hq z
  | c23 z => exact inverse_valid_NF23 q hq z hz
  | c123 z => exact inverse_valid_NF123 q hq z hz
  | c14 z => exact inverse_valid_NF14 q hq z hz
  | c24 z => exact inverse_valid_NF24 q hq z
  | c124 z => exact inverse_valid_NF124 q hq z hz
  | c134 z => exact inverse_valid_NF134 q hq z hz
  | c234 z => exact inverse_valid_NF234 q hq z hz
  | full z => exact inverse_valid_NFFull q hq z hz
#print axioms identify_valid
end LuRazClosure.SourcePieces
