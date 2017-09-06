theory (*calc_name_se-BEGIN*)theories(*calc_name_se-END*)
  imports Main (*calc_name_core_se-BEGIN*)"out/thy/calculus_se"(*calc_name_core_se-END*)
begin                                         


lemma "derivable (I\<^sub>S \<turnstile>\<^sub>S( ( ( ( ''S'' \<^sub>T )\<^sub>A\<^sub>T )\<cdot>\<^sub>T( ( ( ''S'' \<^sub>T )\<^sub>A\<^sub>T )\<cdot>\<^sub>T( ( ''Z'' \<^sub>T )\<^sub>A\<^sub>T ) ) ):\<^sub>T\<^sub>F( ( ''Nat'' \<^sub>F )\<^sub>A\<^sub>F ) ))"
  apply (rule nat_s)
  apply (rule nat_s)
  apply (rule nat_0)
 done

lemma "derivable (I\<^sub>S \<turnstile>\<^sub>S( I\<^sub>T :\<^sub>T\<^sub>F( ''Even'' \<lparr>( ( ( ( ''S'' \<^sub>T )\<^sub>A\<^sub>T )\<cdot>\<^sub>T( ( ( ''S'' \<^sub>T )\<^sub>A\<^sub>T )\<cdot>\<^sub>T( ( ( ''S'' \<^sub>T )\<^sub>A\<^sub>T )\<cdot>\<^sub>T( ( ( ''S'' \<^sub>T )\<^sub>A\<^sub>T )\<cdot>\<^sub>T( ( ''Z'' \<^sub>T )\<^sub>A\<^sub>T ) ) ) ) )\<^sub>T\<^sub>S ) \<rparr> \<^sub>A\<^sub>F ) ))"
  apply (rule even_s)
  apply (rule even_s)
  apply (rule even_b)
  apply (rule nat_0)
 done

(*
lemma "derivable (I\<^sub>S \<turnstile>\<^sub>S( ( (S \<^sub>A\<^sub>T) \<cdot>\<^sub>T( S \<cdot>\<^sub>T Z ) ):\<^sub>T\<^sub>F( NNat \<^sub>A\<^sub>F ) ))"
  sledgehammer


lemma "derivable (( I\<^sub>T :\<^sub>T\<^sub>F( A ) )\<turnstile>\<^sub>S( I\<^sub>T :\<^sub>T\<^sub>F( A ) ))"
  apply (induction A)
    apply simp
   apply (rule I_L_L)
   apply (rule xx_L)
   apply (rule I_L_L2)
   apply simp
  sorry
*)


end