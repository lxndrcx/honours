open HolKernel boolLib bossLib Parse;

open listTheory optionTheory;

val _ = new_theory"buffer_search";

Definition thingy_def:
  (thingy [] b d = []) ∧
  (thingy s [] d = []) ∧
  (thingy (s::ss) (b::bb) d =
   if (s = b)
   then (d::(thingy (s::ss) bb (d+1)))
   else ((thingy (s::ss) bb (d+1))))
End

Triviality thingy_none:
  thingy [] [] 0 = []
Proof
  simp[thingy_def]
QED

Triviality single_prefix_thingy:
  thingy [1] [1;2] 0 = [0]
Proof
  simp[thingy_def]
QED
        
Triviality double_prefix_thingy:
  thingy [1;3] [1;2;1] 0 = [0;2]
Proof
  simp[thingy_def]
QED

Triviality thingy_tests:
  (thingy [] [] n = []) ∧
  (thingy [] b 0 = []) ∧
  (thingy s [] 0 = []) ∧
  (thingy [1] [1;2] 0 = [0]) ∧
  (thingy [1] [] 0 = []) ∧
  (thingy [1;3] [1;2;1] 0 = [0;2]) ∧
  (thingy [1;3] [1;2;1] 1 = [1;3])
Proof
  Cases_on ‘s’ >>
  simp[thingy_def]
QED

Definition whatsit_def:
  (whatsit s [] = 0) ∧
  (whatsit [] b = 0) ∧
  (whatsit (s::ss) (b::bb) =
   if (s = b)
   then (1 + (whatsit ss bb))
   else 0)
End

Triviality whatsit_tests:
  (whatsit [] [] = 0) ∧
  (whatsit [1] [] = 0) ∧
  (whatsit [1] [1] = 1) ∧
  (whatsit [1] [2] = 0) ∧
  (whatsit [1;2] [1;2] = 2) ∧
  (whatsit [1;2] [1;3] = 1) ∧
  (whatsit [1] [1;2] = 1)
Proof
  simp[whatsit_def]
End

val _ = export_theory();
