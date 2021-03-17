open HolKernel boolLib bossLib Parse;

open listTheory optionTheory;
open arithmeticTheory;

val _ = new_theory"buffer_search";

Definition matchLength_def[simp]:
  (matchLength s [] = 0) ∧
  (matchLength [] b = 0) ∧
  (matchLength (s::ss) (b::bb) =
   if (s = b)
   then (1 + (matchLength ss bb))
   else 0)
End

(* TODO can i define them just with EL + LENGTH *)

Theorem matchLength_empty_nil[simp]: matchLength [] t = 0
Proof
  Cases_on ‘t’ >>
  simp[]
QED

Theorem matchLength_empty_nil2[simp]: matchLength s [] = 0
Proof EVAL_TAC
QED

Theorem matchLengthWorks:
  ∀n s t. matchLength s t = n ⇒ (TAKE n s) = (TAKE n t)
Proof
  Induct_on ‘t’ >- simp[] >>
  Cases_on ‘s’ >- simp[] >>
  rw[]
QED

Triviality matchLength_tests:
  (matchLength [] [] = 0) ∧
  (matchLength [1] [] = 0) ∧
  (matchLength [] [1] = 0) ∧
  (matchLength [1] [1] = 1) ∧
  (matchLength [1] [2] = 0) ∧
  (matchLength [1;2] [1;2] = 2) ∧
  (matchLength [1;2] [1;3] = 1) ∧
  (matchLength [1] [1;2] = 1)
Proof EVAL_TAC
QED

Definition longestMatch_def[simp]:
  (longestMatch [] t = (0,0)) ∧
  (longestMatch s [] = (0,0)) ∧
  (longestMatch (s::ss) (t::ts) =
   let ml = matchLength (s::ss) (t::ts);
       (bl,bd) = longestMatch (s::ss) ts
   in if bl ≤ ml then (ml,0)
      else (bl,bd+1))
End

Theorem longestMatch_nil2[simp]:
  longestMatch s [] = (0,0)
Proof
  Cases_on ‘s’ >> simp[]
QED

Theorem longestMatchWorks:
  ∀ bl bd. longestMatch s t = (bl,bd) ⇒
           ((TAKE bl s) = (TAKE bl (DROP bd t)))
Proof
  Induct_on ‘t’
  >- simp[] >>
  Cases_on ‘s’ >>
  simp[] >>
  rename [‘longestMatch (s::ss) t’] >>
  Cases_on ‘longestMatch (s::ss) t’ >>
  gs[] >>
  rw[] >- (
  simp[] >>
  metis_tac[matchLengthWorks]) >>
  simp[]
QED

Definition matches_def:
  matches s t = {(bl,bd)| TAKE bl s = TAKE bl $ DROP bd t}
End

Theorem longestMatchMatches:
  longestMatch s t IN matches s t
Proof
  simp[matches_def] >>
  Cases_on ‘longestMatch s t’ >>
  metis_tac[matches_def, longestMatchWorks]
QED

(* TODO define longest match predicate *)
        
Definition findMatch_def:
  findMatch s t = let (bl,bd) = longestMatch s t
                  in
                    if bl ≤ 2
                    then NONE
                    else SOME (bl,bd)
End

Triviality findMatch_test1:
  findMatch [1;3;4] [1;1;1;1;3;4;2] = SOME (3,3)
Proof EVAL_TAC
QED 

Triviality findMatch_tests:
  (findMatch [] [] = NONE) ∧
  (findMatch [] b  = NONE) ∧
  (findMatch s []  = NONE) ∧
  (findMatch [1;2] [1;2] = NONE) ∧
  (findMatch [1;2;3] [1;2;3] = SOME (3,0)) ∧
  (findMatch [1;2;3] [1;1;2;3] = SOME (3,1))
Proof
  Cases_on ‘s’ >>
  EVAL_TAC
QED

Theorem findMatch_some_nonempty:
  (s = [] ∨ t = []) ⇒ (findMatch s t = NONE)
Proof
  rw[findMatch_def,longestMatch_def] >>
  rw[findMatch_def,longestMatch_def] >>
  Cases_on ‘s’ >> rw[longestMatch_def]
QED

(* TODO: correctness statement *)
(* prove it's actually a match, maybe that it's the longest match *)

Theorem findMatch_findsMatches:
  (findMatch s t = SOME (l,d)) ==> (l,d) IN matches s t
Proof
  simp[findMatch_def] >>
  pairarg_tac >>
  simp[]>>
  metis_tac[longestMatchMatches]
QED

Theorem matches_infinite_zeros:
  (0,a) IN matches s t
Proof
  simp[matches_def]
QED
        
(* length in 3-258 ; buffer up to 32K*)
Definition staticWindow:
  staticWindow s =
  let
    lookahead = TAKE 258 s ∧
    remainder = DROP 258 s
  in 
        
                                     
End
        


(* eventually: use CakeML vectors or array type *)

val _ = export_theory();
