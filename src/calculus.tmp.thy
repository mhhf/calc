theory (*calc_name_se-BEGIN*)calculus_se(*calc_name_se-END*)
imports Main (*calc_name_core_se-BEGIN*)calculus_core_se(*calc_name_core_se-END*)
begin

inductive derivable :: "Sequent \<Rightarrow> bool" where
(*ccc*)


(* TODO - substitution
primrec subst :: "Structure \<Rightarrow> Structure" where
  "subst (Structure_Term_Formula T F) = (Structure_Term_Formula T F)"
 |"subst (Structure_Formula F) = (Structure_Formula F)"
 |"subst Structure_Neutral = Structure_Neutral"
 |"subst (Structure_Comma X Y) = (Structure_Comma X Y)"
*)


end
