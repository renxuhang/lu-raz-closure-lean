import SixRowDifferenceMemberDefs
import SixRowDifferenceUnique

namespace LuRazSixRowClosure
open LuRazClosure LuRazEnumeration Difference
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem removed_members_nodup (q : Nat) (hq : 4≤q) : (RemovedMembers q).Nodup := by
  apply nodup_map_on _ _ (removedList_nodup q hq)
  intro z hz w hw he
  exact removed_form_unique q hq z w ((removedList_exact q hq z).mp hz)
    ((removedList_exact q hq w).mp hw) (fun e => Iff.of_eq (congrFun he e))

theorem added_members_nodup (q : Nat) (hq : 4≤q) : (AddedMembers q).Nodup := by
  apply nodup_map_on _ _ (addedList_nodup q hq)
  intro z hz w hw he
  exact added_form_unique q hq z w ((addedList_exact q hq z).mp hz)
    ((addedList_exact q hq w).mp hw) (fun e => Iff.of_eq (congrFun he e))


end LuRazSixRowClosure
