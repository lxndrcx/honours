open HolKernel boolLib bossLib Parse;

open listTheory optionTheory;
open arithmeticTheory;

val _ = new_theory"buffer_search";

Definition matchLength_def:
  (matchLength s [] = 0) ∧
  (matchLength [] b = 0) ∧
  (matchLength (s::ss) (b::bb) =
   if (s = b)
   then (1 + (matchLength ss bb))
   else 0)
End

Definition matchLength2_def:
  (matchLength2 s t =
   if (s=[] ∨ t=[])
   then 0
   else
     if (HD s = HD t)
     then (1 + (matchLength2 (TL s) (TL t)))
     else 0)
Termination
  WF_REL_TAC‘measure ((UNCURRY $+) o (LENGTH ## LENGTH))’ >>
  rw[] >>
  ‘0 < LENGTH s’ by metis_tac[NOT_NIL_EQ_LENGTH_NOT_0] >>
  ‘0 < LENGTH t’ by metis_tac[NOT_NIL_EQ_LENGTH_NOT_0] >>
  simp[LENGTH_TL]
End

Triviality matchLength_empty_nil[simp]: matchLength2 [] t = 0
Proof EVAL_TAC
QED

Triviality matchLength_empty_nil2[simp]: matchLength2 s [] = 0
Proof EVAL_TAC
QED
       

(* Theorem matchLengthMaxLength: *)
(*   matchLength2 s t ≤ (MIN (LENGTH s) (LENGTH t)) *)
(* Proof *)
(*   fs[Once matchLength2_def,NOT_NIL_EQ_LENGTH_NOT_0,MIN_LE] >> *)
(*   rw[] *)
(*   >- (fs[NOT_NIL_EQ_LENGTH_NOT_0] >> *)
(*       ‘LENGTH (TL s) = (LENGTH s) - 1’ by simp[LENGTH_TL] >> *)
(*       ‘LENGTH (TL t) = (LENGTH t) - 1’ by simp[LENGTH_TL] >> *)
(* QED *)

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

Triviality matchLength2_tests:
  (matchLength2 [] [] = 0) ∧
  (matchLength2 [1] [] = 0) ∧
  (matchLength2 [] [1] = 0) ∧
  (matchLength2 [1] [1] = 1) ∧
  (matchLength2 [1] [2] = 0) ∧
  (matchLength2 [1;2] [1;2] = 2) ∧
  (matchLength2 [1;2] [1;3] = 1) ∧
  (matchLength2 [1] [1;2] = 1)
Proof EVAL_TAC
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

Definition longestMatch2_def:
  (longestMatch2 s t d (bl,bd) =
   if (s=[] ∨ t=[])
   then (bl,bd)
   else
        if (HD s = HD t)
        then 
          let ml = (matchLength2 s t)
          in if (ml < 3) ∨ (ml ≤ bl) then (longestMatch2 s (TL t) (d+1) (bl,bd))
             else (longestMatch2 s (TL t) (d+1) (ml,d))
        else (longestMatch2 s (TL t) (d+1) (bl,bd)))
Termination
  WF_REL_TAC‘measure (LENGTH o (FST o SND))’ >>
  rw[] >>
  (
  ‘0 < LENGTH t’ by metis_tac[NOT_NIL_EQ_LENGTH_NOT_0] >>
  simp[LENGTH_TL])
End

(* Theorem longestMatchMaxLength: *)
(*   FST (longestMatch2 s t 0 (2,0)) ≤ (MAX (MIN (LENGTH s) (LENGTH t)) 2) *)
(* Proof *)
(*   Induct_on ‘s’ *)
(*   rw[longestMatch2_def] *)
        


Definition findMatch_def:
  findMatch s t = let m = (longestMatch s t 0 (2,0))
                  in
                    if m = (2,0)
                    then NONE
                    else SOME m
End

Definition findMatch2_def:
  findMatch2 s t = let m = (longestMatch2 s t 0 (2,0))
                  in
                    if m = (2,0)
                    then NONE
                    else SOME m
End

Triviality findMatch_test1:
  findMatch [1;3;4] [1;1;1;1;3;4;2] = SOME (3,3)
Proof EVAL_TAC
QED 

Triviality findMatch2_test1:
  findMatch2 [1;3;4] [1;1;1;1;3;4;2] = SOME (3,3)
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

Triviality findMatch2_tests:
  (findMatch2 [] [] = NONE) ∧
  (findMatch2 [] b  = NONE) ∧
  (findMatch2 s []  = NONE) ∧
  (findMatch2 [1;2] [1;2] = NONE) ∧
  (findMatch2 [1;2;3] [1;2;3] = SOME (3,0)) ∧
  (findMatch2 [1;2;3] [1;1;2;3] = SOME (3,1))
Proof EVAL_TAC
QED

Theorem findMatch_some_nonempty:
  (s = [] ∨ t = []) ⇒ (findMatch s t = NONE)
Proof
  rw[findMatch_def,longestMatch_def] >>
  rw[findMatch_def,longestMatch_def] >>
  Cases_on ‘s’ >> rw[longestMatch_def]
QED

Theorem findMatch2_some_nonempty:
  (s = [] ∨ t = []) ⇒ (findMatch2 s t = NONE)
Proof
  rw[findMatch_def,longestMatch2_def] >>
  rw[findMatch_def,longestMatch2_def] >>
  EVAL_TAC
QED

(* Theorem findMatch2_short_none: *)
(*   ((LENGTH s < 3) ∨ (LENGTH t < 3)) ⇒ (findMatch2 s t = NONE) *)
(* Proof *)
(*   rw[findMatch2_def,Once longestMatch2_def] >> *)
                         
(* QED *)


(* TODO: correctness statement *)
(* prove it's actually a match, maybe that it's the longest match *)
(* Theorem findMatch_findsMatches: *)
(*   (findMatch s t = SOME (l,d)) = ((TAKE l s) = (TAKE l (DROP d t))) *)
(* Proof *)
(*   eq_tac *)
(*   >- oh no                               *)
(* QED *)

(* length in 3-258 ; buffer up to 32K*)
(* Definition staticWindow: *)
(*   (staticWindow s *)
(* End *)
        


(* eventually: use CakeML vectors or array type *)

val _ = export_theory();
