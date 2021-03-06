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
QED

Definition oojah_def:
  (oojah [] b d = []) ∧
  (oojah s [] d = []) ∧
  (oojah (s::ss) (b::bb) d =
   if (s = b)
   then (((1 + whatsit ss bb), d)::(oojah (s::ss) bb (d+1)))
   else ((oojah (s::ss) bb (d+1))))
End

Triviality oojah_tests:
  (oojah [] [] n = []) ∧
  (oojah [] b 0 = []) ∧
  (oojah s [] 0 = []) ∧
  (oojah [1] [1;2] 0 = [(1,0)]) ∧
  (oojah [1] [] 0 = []) ∧
  (oojah [1;3] [1;2;1] 0 = [(1,0);(1,2)]) ∧
  (oojah [1;3] [1;2;1] 1 = [(1,1);(1,3)]) ∧
  (oojah [1;2] [1;2;1] 0 = [(2,0);(1,2)])
Proof
  Cases_on ‘s’ >>
  simp[oojah_def,whatsit_def]
QED

val [oo1,oo2,oo3] = CONJUNCTS oojah_def;

Definition findMatches_def:
  findMatches s b = oojah s b 0
End

Triviality findMatches_test:
  findMatches [1;3;4] [1;1;1;1;3;4;2] =  [(1,0); (1,1); (1,2); (3,3)]
Proof
  simp[findMatches_def, oojah_def, whatsit_def]
QED

val _ = export_theory();
