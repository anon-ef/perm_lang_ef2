theory AltFlatLemma
  imports AltDropEnv AltCutEnv
begin
    
definition infl_use_env where
  "infl_use_env r_s r_x = (\<lambda> x. if r_s x = OwnPerm \<and> r_x x = NoPerm then OwnPerm else NoPerm)"    
  
lemma infl_disj_use_env: "\<lbrakk> leq_use_env r_ex r_x \<rbrakk> \<Longrightarrow> disj_use_env r_ex (infl_use_env r_s r_x)"  
  apply (simp add: leq_use_env_def)
  apply (simp add: disj_use_env_def)
  apply (simp add: infl_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
   apply (erule_tac x="x" in allE)
   apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_ex x")
    apply (auto)
  done
    
    
  
lemma self_infl_leq_use_env: "leq_use_env (infl_use_env r_s r_x) r_s"       
  apply (simp add: leq_use_env_def)
  apply (simp add: infl_use_env_def)
  done
    
lemma infl_leq_use_env: "\<lbrakk> leq_use_env r_x (diff_use_env r_s r_ex); leq_use_env r_ex r_s \<rbrakk> \<Longrightarrow> leq_use_env (cut_use_env r_ex) (infl_use_env r_s r_x)"   
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (simp add: infl_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: cut_use_env_def)
  apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
   apply (case_tac "r_s x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  apply (case_tac "r_x x")
    apply (auto)
  done 
    
lemma dist_infl_leq_use_env: "\<lbrakk> leq_use_env r_sb r_sa; leq_use_env r_xb r_xa \<rbrakk> \<Longrightarrow> leq_use_env (infl_use_env r_sb r_xa) (infl_use_env r_sa r_xb)"       
  apply (simp add: leq_use_env_def)
  apply (simp add: infl_use_env_def)
  apply (auto)
   apply (erule_tac x="x" in allE)
   apply (erule_tac x="x" in allE)
   apply (case_tac "r_sa x")
     apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_xb x")
    apply (auto)
  done
    


lemma diff_infl_leq_use_env: "leq_use_env (diff_use_env (infl_use_env r_s r_x) (infl_use_env r_s r_x)) r_c"
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: infl_use_env_def)
  done    

 

lemma infl_lift_use_env: "lift_use_env (infl_use_env r_s r_x) r = infl_use_env r_s r_x"    
  apply (case_tac "\<forall> x. lift_use_env (infl_use_env r_s r_x) r x = infl_use_env r_s r_x x")
   apply (auto)
  apply (case_tac r)
    apply (auto)
  apply (simp add: infl_use_env_def)
  apply (auto)
  done    
    

definition refl_use_env where
  "refl_use_env r_s r_x r = (\<lambda> x. if r_s x = OwnPerm \<and> r_x x = NoPerm then r else NoPerm)"

lemma refl_leq_use_env: "leq_use_env (refl_use_env r_s r_x r) r_s"    
  apply (simp add: leq_use_env_def)
  apply (simp add: refl_use_env_def)
  done  

lemma dist_refl_leq_use_env: "\<lbrakk> leq_use_env r_sb r_sa; leq_use_env r_xb r_xa \<rbrakk> \<Longrightarrow> leq_use_env (refl_use_env r_sb r_xa r) (refl_use_env r_sa r_xb r)"         
  apply (simp add: leq_use_env_def)
  apply (simp add: refl_use_env_def)
  apply (auto)
    apply (case_tac r)
      apply (auto)
   apply (erule_tac x="x" in allE)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (case_tac "r_sa x")
     apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "r_xb x")
    apply (auto)
  done

lemma dist_refl_leq_use_env_perm: "\<lbrakk> leq_perm q r \<rbrakk> \<Longrightarrow> leq_use_env (refl_use_env r_s r_x q) (refl_use_env r_s r_x r)"     
  apply (simp add: leq_use_env_def)
  apply (simp add: refl_use_env_def)
  done

lemma dist_refl_leq_use_env_gen: "\<lbrakk> leq_use_env r_sb r_sa; leq_use_env r_xb r_xa; leq_perm q r \<rbrakk> \<Longrightarrow>
  leq_use_env (refl_use_env r_sb r_xa q) (refl_use_env r_sa r_xb r)"         
  apply (rule_tac r_sb="refl_use_env r_sa r_xb q" in trans_leq_use_env)
   apply (rule_tac dist_refl_leq_use_env_perm)
   apply (simp)
  apply (rule_tac dist_refl_leq_use_env)
   apply (auto)
  done
 
lemma refl_lift_use_env: "\<lbrakk> leq_perm r q \<rbrakk> \<Longrightarrow> lift_use_env (refl_use_env r_s r_x q) r = refl_use_env r_s r_x q"    
  apply (case_tac "\<forall> x. lift_use_env (refl_use_env r_s r_x q) r x = refl_use_env r_s r_x q x")
   apply (auto)
  apply (case_tac r)
    apply (auto)
  apply (simp add: refl_use_env_def)
  apply (case_tac q)
    apply (auto)
  done          
    
lemma refl_diff_comp_leq_use_env: "\<lbrakk> safe_use_lift rxa ra; leq_perm ra r;
  leq_use_env (diff_use_env (lift_use_env rxa ra) (infl_use_env r_s1 r_s2)) rx \<rbrakk> \<Longrightarrow> 
  leq_use_env (lift_use_env rxa ra) (comp_use_env rx (refl_use_env r_s1 r_s2 r))"    
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (simp add: diff_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (simp add: infl_use_env_def)
  apply (simp add: refl_use_env_def)
  apply (auto)
    apply (case_tac ra)
      apply (auto)
     apply (case_tac "rxa x")
       apply (auto)
     apply (case_tac r)
       apply (auto)
      apply (case_tac "rx x")
        apply (auto)
     apply (case_tac "rx x")
       apply (auto)
    apply (case_tac r)
      apply (auto)
    apply (case_tac "rx x")
      apply (auto)
    apply (case_tac "lift_use_env rxa ra x")
      apply (auto)
    apply (case_tac "rx x")
      apply (auto)
   apply (case_tac "rx x")
     apply (auto)
   apply (case_tac "lift_use_env rxa ra x")
     apply (auto)
   apply (case_tac "rx x")
     apply (auto)
  apply (case_tac "rx x")
    apply (auto)
  done
 
lemma refl_diff_comp_leq_use_env_x: "\<lbrakk> safe_use_lift rxa ra; leq_perm ra r;
  leq_use_env (diff_use_env rxa (infl_use_env r_s1 r_s2)) rx \<rbrakk> \<Longrightarrow> 
  leq_use_env rxa (comp_use_env rx (refl_use_env r_s1 r_s2 r))"
  apply (case_tac ra)
    apply (auto)
    apply (rule_tac r_sb="lift_use_env rxa ra" in trans_leq_use_env)
     apply (rule_tac refl_diff_comp_leq_use_env)
       apply (auto)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac r_sb="lift_use_env rxa ra" in trans_leq_use_env)
    apply (rule_tac refl_diff_comp_leq_use_env)
      apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (simp add: infl_use_env_def)
  apply (simp add: refl_use_env_def)
  apply (case_tac r)
    apply (auto)
  apply (rule_tac st_diff_comp_leq_use_env)
  apply (simp)
  done
  
lemma refl_disj_use_env: "\<lbrakk> leq_use_env r_ex r_x \<rbrakk> \<Longrightarrow> disj_use_env r_ex (refl_use_env r_s r_x r)"  
  apply (simp add: leq_use_env_def)
  apply (simp add: disj_use_env_def)
  apply (simp add: refl_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
   apply (erule_tac x="x" in allE)
   apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_ex x")
    apply (auto)
  done  
  
lemma safe_lift_refl_use_env: "\<lbrakk> safe_use_lift r_ex r \<rbrakk> \<Longrightarrow> safe_use_lift (refl_use_env r_s r_x r) r"    
  apply (case_tac r)
    apply (auto)
   apply (simp add: refl_use_env_def)
  apply (simp add: refl_use_env_def)
  apply (case_tac "r_s x = OwnPerm \<and> r_x x = NoPerm")
   apply (auto)
  done
  
lemma rswp_gen_leq_use_env: "\<lbrakk> leq_use_env r_ex r_s1; leq_use_env r_s2 (diff_use_env r_s1 r_ex);
  leq_use_env (diff_use_env r_x r_ex) rx; (\<forall> x. leq_perm (r_x x) r) \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (comp_use_env rx (refl_use_env r_s1 r_s2 r))"
  apply (case_tac "(\<forall> x. leq_perm (r_x x) (comp_use_env rx (refl_use_env r_s1 r_s2 r) x))")
   apply (simp add: leq_use_env_def)
    apply (auto)
    (* in all cases, if EX \<noteq> Own, the case is trivial *)
  apply (case_tac "r_ex x \<noteq> OwnPerm")
   apply (cut_tac r_x="diff_use_env r_x r_ex" and r_s="comp_use_env rx (refl_use_env r_s1 r_s2 r)" and x="x" in spec_leq_perm)
    apply (rule_tac comp_leq_use_env1)
    apply (simp)
   apply (cut_tac r_s="r_x" and r_x="r_ex" and x="x" in diff_use_eq)
    apply (auto)
    (* otherwise, split on r_s1 x1a = Own *)
  apply (case_tac "r_s1 x \<noteq> OwnPerm")
   apply (cut_tac r_x="r_ex" and r_s="r_s1" and x="x" in leq_use_own)
     apply (auto)
    (* - if r_s1 x1a = Own, and EX = Own, r_s2 x1a = None, meaning the reflective case is guaranteed to have a value. *)
  apply (cut_tac r_x="r_s2" and r_s="diff_use_env r_s1 r_ex" and x="x" in leq_use_none)
    apply (simp)
   apply (rule_tac diff_use_none_ex)
   apply (auto)
  apply (cut_tac r_x="r_x" and r_s="comp_use_env rx (refl_use_env r_s1 r_s2 r)" and x="x" in spec_leq_perm)
   apply (cut_tac p="r_x x" and q="refl_use_env r_s1 r_s2 r x" and r="comp_use_env rx (refl_use_env r_s1 r_s2 r) x" in trans_leq_perm)
     apply (simp add: refl_use_env_def)
    apply (rule_tac r_x="refl_use_env r_s1 r_s2 r" in spec_leq_perm)
    apply (rule_tac self_comp_leq_use_env2)
   apply (auto)
  done  

    (*
lemma rswp_var_leq_use_env: "\<lbrakk> leq_use_env (ereq_use_env x1a tau) r_s1; leq_use_env r_ex r_s1; var_val_type rf tau_r tau;
  leq_use_env r_s2 (diff_use_env r_s1 (comp_use_env (ereq_use_env x1a tau) r_ex)); safe_type_x tau r; rf \<noteq> NoRef;
  leq_use_env (diff_use_env (ereq_use_env x1a tau) (comp_use_env (ereq_use_env x1a tau) r_ex)) rx \<rbrakk> \<Longrightarrow>
  leq_use_env (ereq_use_env x1a tau) (comp_use_env rx (refl_use_env r_s1 r_s2 r))"
  apply (rule_tac r_x="ereq_use_env x1a tau" and r_ex="comp_use_env (ereq_use_env x1a tau) r_ex" in rswp_gen_leq_use_env)    
     apply (rule_tac dist_comp_leq_use_env)
      apply (auto)
  apply (simp add: ereq_use_env_def)
  apply (simp add: one_use_env_def)
  apply (auto)
  apply (simp add: end_req_perm_def)
  apply (case_tac "req_type tau")
    apply (auto)
  apply (case_tac r)
    apply (auto)
  done
*)
    
lemma safe_lift_drop_use_env: "safe_use_lift (drop_use_env_dep r_s r) r" 
  apply (case_tac r)
    apply (auto)
   apply (simp add: empty_use_env_def)
  apply (simp add: drop_use_env_def)
  apply (case_tac "r_s x")
    apply (auto)
  done
    
lemma self_drop_dep_leq_use_env: "leq_use_env (drop_use_env_dep r_s r) r_s"    
  apply (case_tac r)
    apply (auto)
    apply (rule_tac leq_empty_use_env)
   apply (rule_tac self_drop_leq_use_env)
  apply (rule_tac id_leq_use_env)
  done
    
lemma drop_dep_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (drop_use_env_dep r_x r) r_s"   
  apply (rule_tac r_sb="r_x" in trans_leq_use_env)
   apply (simp)
  apply (rule_tac self_drop_dep_leq_use_env)
  done
    
lemma dist_drop_dep_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (drop_use_env_dep r_x r) (drop_use_env_dep r_s r)"    
  apply (case_tac r)
    apply (auto)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac dist_drop_leq_use_env)
  apply (simp)
  done

  
  
  (*
    ### if we're going to re-prove this, we need to re-think the approach.
    intuitively this lemma is true because rx + [r_s1 - r_s2] should contain the full set of requirements.

    the hard part is - say that we had a pair. now it may have originally been typed with rx1 / rx2 that do
    not fit within [r_s1 - r_s2].r. additionally, if we have a primitive pair, rx has no requirements over it.
 
  *)
  
lemma rswp_coerce: "\<lbrakk> \<lbrakk>well_typed env r_s1 e1 tau r_s2 rx; is_sexp e1; safe_type_x tau r\<rbrakk>
           \<Longrightarrow> well_typed env (comp_use_env rx (refl_use_env r_s1 r_s2 r)) e1 tau (comp_use_env rx (refl_use_env r_s1 r_s2 r))
                (comp_use_env rx (refl_use_env r_s1 r_s2 r)); well_typed env r_s1 e1 tau r_s2 rx; is_sexp e1; safe_type_x tau r \<rbrakk> \<Longrightarrow>
  well_typed env (comp_use_env rx (refl_use_env r_s1 r_s2 r)) e1 tau (comp_use_env rx (refl_use_env r_s1 r_s2 r))
                (comp_use_env rx (refl_use_env r_s1 r_s2 r))"
  apply (auto)
  done
    
lemma refl_infl_use_env: "infl_use_env r_s r_x = refl_use_env r_s r_x OwnPerm"    
  apply (case_tac "\<forall> x. infl_use_env r_s r_x x = refl_use_env r_s r_x OwnPerm x")
   apply (auto) 
  apply (simp add: infl_use_env_def)
  apply (simp add: refl_use_env_def)
  done    
    
  
  (** ## THE MOST GENERAL VERSION OF THIS LEMMA **)
    
  
lemma infl_sexp_wp: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; is_sexp e \<rbrakk> \<Longrightarrow> well_typed env (comp_use_env rx (infl_use_env r_s1 r_s2)) e tau
  (comp_use_env rx (infl_use_env r_s1 r_s2)) (comp_use_env rx (infl_use_env r_s1 r_s2))"
  apply (induct e arbitrary: r_s1 tau r_s2 rx)
        apply (auto)
    (* const + op cases *)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac id_leq_use_env)
    (* var cases p1. *)
      apply (rule_tac st_diff_comp_leq_use_env)
      apply (rule_tac r_sb="diff_use_env (ereq_use_env (owner_name x) tau_x) (comp_use_env (ereq_use_env (owner_name x) tau_x) r_ex)" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac dist_diff_leq_use_env_cut)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac infl_leq_use_env)
       apply (simp)
      apply (rule_tac dist_comp_leq_use_env)
       apply (simp_all)
    (* var cases p2. *)
     apply (rule_tac x="empty_use_env" in exI)
     apply (auto)
        apply (rule_tac rhs_weak_leq_use_env)
         apply (rule_tac dist_weak_comp_use_env)
          apply (rule_tac weak_ereq_use_env)
          apply (simp add: unlim_def)
          apply (case_tac x)
           apply (auto)
         apply (simp add: weak_use_env_def)
         apply (simp add: empty_use_env_def)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac leq_empty_use_env)
     apply (rule_tac r_ex="r_ex" in lhs_diff_leq_use_env)
      apply (rule_tac comp_leq_use_env1)
      apply (rule_tac lhs_fold_dcl_use_env)
      apply (rule_tac lhs_flip_use_env)
      apply (rule_tac lhs_unroll_dcl_use_env)
      apply (rule_tac lhs_unroll_dcl_use_env)
      apply (rule_tac diff_leq_use_env)
      apply (rule_tac lhs_fold_dcl_use_env)
      apply (rule_tac lhs_flip_use_env)
      apply (simp)
     apply (rule_tac comp_leq_use_env2)
     apply (rule_tac infl_leq_use_env)
      apply (rule_tac r_sb="diff_use_env r_s1 (comp_use_env (ereq_use_env (owner_name x) tau_x) r_ex)" in trans_leq_use_env)
       apply (rule_tac dist_diff_leq_use_env_gen)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac self_comp_leq_use_env2)
      apply (simp_all)
    (* pair case. prim case *)
    apply (case_tac "req_type (PairTy t1 t2 r) = Prim")
     apply (rule_tac x="comp_use_env rx (infl_use_env r_s1 r_s2)" in exI)
     apply (rule_tac x="comp_use_env rx (infl_use_env r_s1 r_s2)" in exI)
     apply (rule_tac x="empty_use_env" in exI)
     apply (auto)
      apply (rule_tac r_s="empty_use_env" in well_typed_incr_simul_perm)
       apply (rule_tac leq_empty_use_env)
      apply (rule_tac wt_sexp_no_all)
        apply (auto)
       apply (case_tac r)
        apply (auto)
       apply (case_tac "req_type t1")
         apply (auto)
       apply (case_tac "req_type t2")
         apply (auto)
      apply (rule_tac value_is_sexp)
      apply (simp)
     apply (rule_tac x="empty_use_env" in exI)
     apply (auto)
        apply (rule_tac r_s="empty_use_env" in well_typed_incr_simul_perm)
         apply (rule_tac leq_empty_use_env)
        apply (rule_tac wt_sexp_no_all)
          apply (auto)
         apply (case_tac "r")
          apply (auto)
         apply (case_tac "req_type t1")
           apply (auto)
          apply (case_tac "req_type t2")
            apply (auto)
         apply (case_tac "req_type t2")
           apply (auto)
        apply (cut_tac e="e2" in value_is_sexp)
         apply (auto)
       apply (simp add: lift_empty_use_env)
       apply (rule_tac leq_empty_use_env)
      apply (simp add: lift_empty_use_env)
      apply (rule_tac disj_empty_use_env2)
     apply (simp add: lift_empty_use_env)
     apply (case_tac "\<not> weak_use_env empty_use_env")
      apply (simp add: weak_use_env_def)
      apply (simp add: empty_use_env_def)
     apply (rule_tac x="empty_use_env" in exI)
     apply (auto)
        apply (rule_tac rhs_weak_leq_use_env)
         apply (simp)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac leq_empty_use_env)
     apply (simp add: pair_req_def)
     apply (rule_tac leq_empty_use_env)
    (* pair case. non-primitve case *)
    apply (simp add: pair_req_def)
    (* - prelim: r_s3 \<le> r_s1 *)
    apply (cut_tac r_sc="r_s3" and r_sb="r_s2a" and r_sa="r_s1" in trans_leq_use_env)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    (* - prelim: rx1 + EX \<le> rx + EX *)
    apply (cut_tac r_xa="lift_use_env rx1 r" and r_xb="infl_use_env r_s1 r_s2a" and r_s="comp_use_env rx (infl_use_env r_s1 r_s2)" in dist_comp_leq_use_env)
      apply (rule_tac st_diff_comp_leq_use_env)
      apply (rule_tac r_sb="diff_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac dist_diff_leq_use_env_cut)
       apply (rule_tac self_comp_leq_use_env1)
      apply (rule_tac infl_leq_use_env)
       apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
        apply (rule_tac dist_diff_leq_use_env)
        apply (simp_all)
     apply (rule_tac comp_leq_use_env2)
     apply (rule_tac dist_infl_leq_use_env)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
      apply (rule_tac diff_leq_use_env)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
    (* - prelim: rx2 + EX \<le> rx + EX *)
    apply (cut_tac r_xa="lift_use_env rx2 r" and r_xb="infl_use_env r_s2a r_s3" and r_s="comp_use_env rx (infl_use_env r_s1 r_s2)" in dist_comp_leq_use_env)
      apply (rule_tac st_diff_comp_leq_use_env)
      apply (rule_tac r_sb="diff_use_env (comp_use_env (lift_use_env rx1 r) (lift_use_env rx2 r)) r_ex" in trans_leq_use_env)
       apply (simp)
      apply (rule_tac dist_diff_leq_use_env_cut)
       apply (rule_tac self_comp_leq_use_env2)
      apply (rule_tac infl_leq_use_env)
       apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
        apply (rule_tac dist_diff_leq_use_env)
        apply (simp_all)
     apply (rule_tac comp_leq_use_env2)
     apply (rule_tac dist_infl_leq_use_env)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
      apply (rule_tac self_diff_leq_use_env)
     apply (auto)
    (* - well-typedness for e1 *)
    apply (rule_tac x="comp_use_env rx (infl_use_env r_s1 r_s2)" in exI)
    apply (rule_tac x="comp_use_env rx (infl_use_env r_s1 r_s2)" in exI)
    apply (rule_tac x="comp_use_env rx1 (infl_use_env r_s1 r_s2a)" in exI)
    apply (auto)
     apply (rule_tac r_s="comp_use_env rx1 (infl_use_env r_s1 r_s2a)" in well_typed_incr_simul_perm)
      apply (rule_tac r_sb="comp_use_env (lift_use_env rx1 r) (infl_use_env r_s1 r_s2a)" in trans_leq_use_env)
       apply (auto)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac self_lift_leq_use_env)
      apply (rule_tac self_comp_leq_use_env2)
     apply (cut_tac e="e1" in value_is_sexp)
      apply (auto)
    (* - well-typedness for e2 *)
    apply (rule_tac x="comp_use_env rx2 (infl_use_env r_s2a r_s3)" in exI)
    apply (auto)
        apply (rule_tac r_s="comp_use_env rx2 (infl_use_env r_s2a r_s3)" in well_typed_incr_simul_perm)
         apply (rule_tac r_sb="comp_use_env (lift_use_env rx2 r) (infl_use_env r_s2a r_s3)" in trans_leq_use_env)
          apply (auto)
         apply (rule_tac dist_comp_leq_use_env)
          apply (rule_tac comp_leq_use_env1)
          apply (rule_tac self_lift_leq_use_env)
         apply (rule_tac self_comp_leq_use_env2)
        apply (cut_tac e="e2" in value_is_sexp)
         apply (auto)
    (* - first boundaries *)
       apply (simp add: lift_comp_use_env)
       apply (simp add: infl_lift_use_env)
      apply (simp add: lift_comp_use_env)
      apply (simp add: infl_lift_use_env)
     apply (simp add: lift_comp_use_env)
     apply (simp add: infl_lift_use_env)
     apply (rule_tac disj_comp_use_env1)
      apply (rule_tac disj_comp_use_env2)
       apply (simp)
      apply (rule_tac infl_disj_use_env)
      apply (simp)
     apply (rule_tac disj_comp_use_env2)
      apply (rule_tac comm_disj_use_env)
      apply (rule_tac infl_disj_use_env)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
     apply (rule_tac comm_disj_use_env)
     apply (rule_tac infl_disj_use_env)
     apply (rule_tac self_infl_leq_use_env)
    (* - secondary boundaries *)
    apply (case_tac "\<not> weak_use_env empty_use_env")
     apply (simp add: weak_use_env_def)
     apply (simp add: empty_use_env_def)
    apply (rule_tac x="empty_use_env" in exI)
    apply (auto)
       apply (rule_tac rhs_weak_leq_use_env)
        apply (simp)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac leq_empty_use_env)
    apply (rule_tac diff_leq_use_env)
    apply (simp add: lift_comp_use_env)
    apply (simp add: infl_lift_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (auto)
    (* lam case  *)
   apply (rule_tac x="rxa" in exI)
   apply (auto)
    apply (rule_tac st_diff_comp_leq_use_env)
    apply (rule_tac r_sb="diff_use_env rxa r_ex" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac dist_diff_leq_use_env_cut)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac infl_leq_use_env)
     apply (simp_all)
   apply (rule_tac x="empty_use_env" in exI)
   apply (auto)
      apply (rule_tac rhs_weak_leq_use_env)
       apply (simp add: weak_use_env_def)
       apply (simp add: empty_use_env_def)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac leq_empty_use_env)
   apply (rule_tac diff_leq_use_env)
   apply (rule_tac st_diff_comp_leq_use_env)
   apply (rule_tac r_sb="diff_use_env rxa r_ex" in trans_leq_use_env)
    apply (simp)
   apply (rule_tac dist_diff_leq_use_env_cut)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac infl_leq_use_env)
    apply (simp_all)
    (* app case. primitive case *)
  apply (case_tac "req_type tau = Prim")
   apply (rule_tac x="t1" in exI)
   apply (rule_tac x="r" in exI)
   apply (rule_tac x="a" in exI)
   apply (rule_tac x="comp_use_env rx (infl_use_env r_s1 r_s2)" in exI)
   apply (rule_tac x="empty_use_env" in exI)
   apply (auto)
    apply (case_tac e1)
          apply (auto)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac leq_empty_use_env)
   apply (rule_tac x="empty_use_env" in exI)
   apply (rule_tac x="comp_use_env rx (infl_use_env r_s1 r_s2)" in exI)
   apply (auto)
    apply (rule_tac r_s="empty_use_env" in well_typed_incr_simul_perm)
     apply (rule_tac leq_empty_use_env)
    apply (rule_tac wt_sexp_no_all)
      apply (auto)
     apply (case_tac e1)
           apply (auto)
     apply (case_tac x1)
                 apply (auto)
          apply (simp_all add: pure_fun_def)
    apply (case_tac "\<not> is_value e2")
     apply (case_tac e1)
           apply (auto)
     apply (case_tac x1)
                 apply (auto)
     apply (case_tac e2)
           apply (auto)
    apply (rule_tac value_is_sexp)
    apply (simp)
   apply (case_tac "\<not> weak_use_env empty_use_env")
    apply (simp add: weak_use_env_def)
    apply (simp add: empty_use_env_def)
   apply (simp add: lift_empty_use_env)
   apply (rule_tac x="empty_use_env" in exI)
   apply (auto)
        apply (rule_tac rhs_weak_leq_use_env)
         apply (rule_tac dist_weak_comp_use_env)
          apply (rule_tac dist_weak_comp_use_env)
           apply (simp_all)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac dist_comp_leq_use_env)
        apply (rule_tac leq_empty_use_env)
       apply (rule_tac leq_empty_use_env)
      apply (rule_tac disj_empty_use_env2)
     apply (rule_tac id_leq_use_env)
    apply (rule_tac leq_empty_use_env)
   apply (simp add: app_req_def)
   apply (rule_tac leq_empty_use_env)
    (* app case. non-primitive case *)
  apply (simp add: app_req_def)
    (* - prelim: r_s3 \<le> r_s1 *)
  apply (cut_tac r_sc="r_s3" and r_sb="r_s2a" and r_sa="r_s1" in trans_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
    (* - prelim: rx1 + EX \<le> rx + EX *)(*
  apply (cut_tac r_xa="rx1" and r_xb="infl_use_env r_s1 r_s2a" and r_s="comp_use_env rx (infl_use_env r_s1 r_s2)" in dist_comp_leq_use_env)
    apply (rule_tac st_diff_comp_leq_use_env)
    apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac dist_diff_leq_use_env_cut)
     apply (rule_tac self_comp_leq_use_env1)
    apply (rule_tac infl_leq_use_env)
     apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
      apply (rule_tac dist_diff_leq_use_env)
      apply (simp_all)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (auto)
   apply (rule_tac comp_leq_use_env2)
   apply (rule_tac dist_infl_leq_use_env)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
    apply (rule_tac diff_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)*)
    (* - prelim: rx2 + EX \<le> rx + EX *)
  apply (cut_tac r_xa="rx2" and r_xb="infl_use_env r_s2a r_s3" and r_s="comp_use_env rx (infl_use_env r_s1 r_s2)" in dist_comp_leq_use_env)
    apply (rule_tac st_diff_comp_leq_use_env)
    apply (rule_tac r_sb="diff_use_env (comp_use_env rx1 rx2) (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
     apply (simp)
    apply (rule_tac dist_diff_leq_use_env_cut)
     apply (rule_tac self_comp_leq_use_env2)
    apply (rule_tac infl_leq_use_env)
     apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
      apply (rule_tac dist_diff_leq_use_env)
      apply (simp_all)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
      apply (auto)
   apply (rule_tac comp_leq_use_env2)
   apply (rule_tac dist_infl_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
   apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
    apply (rule_tac self_diff_leq_use_env)
   apply (auto)    
    (* - well-typedness for e1. *)
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="r" in exI)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="comp_use_env rx (infl_use_env r_s1 r_s2)" in exI)
  apply (rule_tac x="empty_use_env" in exI)
  apply (auto)
   apply (case_tac e1)
         apply (auto)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac leq_empty_use_env)
    (* - e2 is an sexp *)
   apply (case_tac "\<not> is_sexp e2")
    apply (case_tac "\<not> is_value e2")
     apply (case_tac e1)
           apply (auto)
    apply (case_tac x1)
                apply (auto)
    apply (case_tac e2)
          apply (auto)
   apply (cut_tac e="e2" in value_is_sexp)
    apply (auto)
    (* - r \<noteq> Own *)
  apply (case_tac "is_own r")
   apply (simp add: is_own_def)
   apply (case_tac e1)
         apply (auto)
   apply (case_tac x1)
               apply (auto)
       apply (simp_all add: pure_fun_def)
    (* - well-typedness for e2. *)
  apply (rule_tac x="drop_use_env (comp_use_env rx2 (infl_use_env r_s2a r_s3))" in exI)
  apply (rule_tac x="comp_use_env rx (infl_use_env r_s1 r_s2)" in exI)
  apply (auto)
   apply (rule_tac wt_sexp_drop_req)
     apply (rule_tac r_s="comp_use_env rx2 (infl_use_env r_s2a r_s3)" in well_typed_incr_simul_perm)
      apply (auto)
   apply (case_tac e1)
         apply (auto)
   apply (case_tac x1)
               apply (auto)
       apply (simp_all add: pure_fun_def)
   apply (simp add: unlim_def)
    (* - boundaries *)
  apply (case_tac "\<not> weak_use_env empty_use_env")
   apply (simp add: weak_use_env_def)
   apply (simp add: empty_use_env_def)
  apply (rule_tac t="lift_use_env (drop_use_env (comp_use_env rx2 (infl_use_env r_s2a r_s3))) r" and
          s="drop_use_env (comp_use_env rx2 (infl_use_env r_s2a r_s3))" in subst)
   apply (simp add: is_own_def)
   apply (case_tac r)
     apply (auto)
  apply (rule_tac x="empty_use_env" in exI)
  apply (auto)
       apply (rule_tac rhs_weak_leq_use_env)
        apply (rule_tac dist_weak_comp_use_env)
         apply (rule_tac dist_weak_comp_use_env)
          apply (simp_all)
        apply (rule_tac drop_weak_use_env)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac leq_empty_use_env)
      apply (rule_tac drop_leq_use_env)
      apply (simp)
     apply (rule_tac disj_empty_use_env2)
    apply (rule_tac id_leq_use_env)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac diff_leq_use_env)
  apply (rule_tac dist_comp_leq_use_env)
   apply (rule_tac leq_empty_use_env)
  apply (rule_tac drop_leq_use_env)
  apply (simp)
  done
  
  
  (*
    - sample ideal flow of inequalities for infl_use_env
    leq_use_env (req_use_env x1a tau) (comp_use_env rx (infl_use_env r_s1 r_s2))
    leq_use_env (diff_use_env (req_use_env x1a tau) (infl_use_env r_s1 r_s2)) rx
    leq_use_env (diff_use_env (req_use_env x1a tau) (infl_use_env r_s1 r_s2)) (diff_use_env (req_use_env x1a tau) (comp_use_env (req_use_env x1a tau) r_ex))
      -- fails at this step --
    leq_use_env (comp_use_env (req_use_env x1a tau) r_ex) (infl_use_env r_s1 r_s2)
    leq_use_env r_s2 (diff_use_env r_s1 (comp_use_env (req_use_env x1a tau) r_ex))
  *)

  
lemma dist_infl_leq_use_envr: "\<lbrakk> leq_use_env r_xb r_xa \<rbrakk> \<Longrightarrow> leq_use_env (infl_use_env r_s r_xa) (infl_use_env r_s r_xb)"    
  apply (simp add: leq_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (simp add: infl_use_env_def)
  apply (auto)  
  apply (case_tac "r_xb x")
    apply (auto)
  done

    
lemma lhs_infl_leq_use_env: "\<lbrakk> leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> leq_use_env (infl_use_env r_x r_ex) r_s"    
  apply (simp add: leq_use_env_def)
  apply (simp add: infl_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_s x")
    apply (auto)
  done
    

lemma infl_full_sexp_wp: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; is_sexp e \<rbrakk> \<Longrightarrow> well_typed env r_s1 e tau r_s1 (comp_use_env rx (infl_use_env r_s1 r_s2))"    
  apply (rule_tac t="well_typed env r_s1 e tau r_s1 (comp_use_env rx (infl_use_env r_s1 r_s2))" and
        s="well_typed env (comp_use_env (comp_use_env rx (infl_use_env r_s1 r_s2)) (diff_use_env r_s1 (comp_use_env rx (infl_use_env r_s1 r_s2)))) e tau
          (comp_use_env (comp_use_env rx (infl_use_env r_s1 r_s2)) (diff_use_env r_s1 (comp_use_env rx (infl_use_env r_s1 r_s2))))
          (comp_use_env rx (infl_use_env r_s1 r_s2))" in subst)
   apply (cut_tac r_x="comp_use_env rx (infl_use_env r_s1 r_s2)" and r_s="r_s1" in msum_diff_comp_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac r_sb="r_s2" in trans_leq_use_env)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
    apply (rule_tac well_typed_perm_leqx)
    apply (auto)
   apply (rule_tac lhs_infl_leq_use_env)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac well_typed_comp_perms_gen)
   apply (rule_tac infl_sexp_wp)
    apply (auto)
  apply (rule_tac mini_disj_diff_use_env)
  done
     
  
lemma wt_sexp_req_use: "\<lbrakk> well_typed env r_s1 e tau r_s2 rx; is_sexp e; x \<in> non_prim_vars env e; r_s2 x \<noteq> NoPerm \<rbrakk> \<Longrightarrow> rx x \<noteq> NoPerm"    
    (* we utilize the value typing of e1 (x1) *)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and e="e" and tau="tau" and ?r_s2.0="r_s2" and rx="rx" in infl_sexp_wp)
    apply (auto)
    (* - rx x has a value, proven by showing that rx + [r_s1 - r_s2a] has a value *)
  apply (case_tac "rx x = NoPerm")
   apply (cut_tac r_sa="rx" and r_sb="infl_use_env r_s1 r_s2" and x="x" in comp_use_none)
     apply (simp)
    apply (simp add: infl_use_env_def)
   apply (cut_tac env="env" and ?r_s1.0="comp_use_env rx (infl_use_env r_s1 r_s2)" and x="x" in well_typed_no_npv_use)
     apply (auto)
  done    

end