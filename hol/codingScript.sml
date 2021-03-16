open HolKernel boolLib bossLib Parse;

open listTheory optionTheory;

val _ = new_theory"buffer_search";

(* note to self: use sensible names and documentation for thing because reading other people's definitions/proofs is ridiculous when it's like "ad hhs jjs -> jjsad () jsjd 2" *)


val _ = export_theory();
