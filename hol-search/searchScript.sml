open HolKernel boolLib bossLib Parse;

open listTheory optionTheory;

val _ = new_theory"buffer_search";

Definition matchLength_def:
  (matchLength s [] = 0) ∧
  (matchLength [] b = 0) ∧
  (matchLength (s::ss) (b::bb) =
   if (s = b)
   then (1 + (matchLength ss bb))
   else 0)
End

Triviality matchLength_tests:
  (matchLength [] [] = 0) ∧
  (matchLength [1] [] = 0) ∧
  (matchLength [] [1] = 0) ∧
  (matchLength [1] [1] = 1) ∧
  (matchLength [1] [2] = 0) ∧
  (matchLength [1;2] [1;2] = 2) ∧
  (matchLength [1;2] [1;3] = 1) ∧
  (matchLength [1] [1;2] = 1)
Proof
  simp[matchLength_def]
QED

Definition longestMatch_def:
  (longestMatch [] t d b = b) ∧
  (longestMatch s [] d b = b) ∧
  (longestMatch (s::ss) (t::ts) d (bl,bd) =
   if (s=t)
   then 
     let ml = (1 + (matchLength ss ts))
     in if ml > bl then (longestMatch (s::ss) ts (d+1) (ml,d))
        else (longestMatch (s::ss) ts (d+1) (bl,bd))
   else (longestMatch (s::ss) ts (d+1) (bl,bd)))
End

Definition findMatch_def:
  findMatch s t = let m = (longestMatch s t 0 (0,0))
                  in
                    if m = (0,0)
                    then NONE
                    else SOME m
End

Triviality findMatch_test1:
  findMatch [1;3;4] [1;1;1;1;3;4;2] = SOME (3,3)
Proof
  rpt (simp[findMatch_def, Once longestMatch_def,matchLength_def])
QED 

Triviality findMatch_tests:
  (findMatch [] [] = NONE) ∧
  (findMatch [] b  = NONE) ∧
  (findMatch s []  = NONE) ∧
  (findMatch [1] [1;2] = SOME (1,0)) ∧
  (findMatch [1] []    = NONE) ∧
  (findMatch [1;3] [1;2;1] = SOME (1,0)) ∧
  (findMatch [1;2] [1;2;1] = SOME (2,0))
Proof
  Cases_on ‘s’ >>
  simp[findMatch_def,longestMatch_def, matchLength_def]
QED

Theorem findMatch_some_nonempty:
  (s = [] ∨ t = []) ⇒ (findMatch s t = NONE)
Proof
  rw[findMatch_def,longestMatch_def] >>
  rw[findMatch_def,longestMatch_def] >>
  Cases_on ‘s’ >> rw[longestMatch_def]
QED

Theorem findMatch_findsMatches:
  (findMatch s t = SOME (l,d)) = ((TAKE l s) = (TAKE l (DROP d t)))
Proof
  eq_tac
  >- oh no                              

(* TODO: correctness statement *)
(* prove it's actually a match, maybe that it's the longest match *)
(* eventually: use CakeML vectors or array type *)

val _ = export_theory();
