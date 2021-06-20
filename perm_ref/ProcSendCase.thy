theory ProcSendCase
  imports ResMapValid ReduceWTS ProcDef ProcCVars
begin
  
lemma cancel_strong_leq_use_env: "\<lbrakk> strong_use_env r_x \<rbrakk> \<Longrightarrow> leq_use_env (diff_use_env r_x r_x) r_s"  
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: strong_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
  done
  
lemma sfl_diff_use_env: "\<lbrakk> strong_use_env r_ex; leq_use_env r_ex r_s; is_own r \<rbrakk> \<Longrightarrow> diff_use_env r_s (diff_use_env (lift_use_env r_s r) r_ex) = r_ex"
  apply (case_tac "\<forall> x. diff_use_env r_s (diff_use_env (lift_use_env r_s r) r_ex) x = r_ex x")
   apply (auto)
  apply (simp add: strong_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: is_own_def)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_ex x")
    apply (auto)  
   apply (case_tac "r_s x")
    apply (auto)
  apply (case_tac "r_s x")
    apply (auto)
  done    
    
    (* the question right now is, how do we make these types line up? *)
  
lemma safe_val_exp: "\<lbrakk> well_typed env r_s1 (app_hole h (AppExp (AppExp (ConstExp SendConst) (VarExp (LocType a b))) v)) tau r_s2 rx;
  env (Loc a) = Some (ChanTy t SEnd); is_value c; is_value v \<rbrakk> \<Longrightarrow>
  well_typed env (np_dom_use_env env v) v t (np_dom_use_env env v) (np_dom_use_env env v)"    
  apply (induct h arbitrary: env r_s1 tau r_s2 rx)
       apply (auto)
    (* base case *)
  apply (case_tac "t \<noteq> t1")
   apply (simp add: pure_fun_def)
  apply (cut_tac env="env" and ?r_s1.0="r_s2a" and e="v" and tau="t" and ?r_s2.0="r_s3" and rx="rx2" in infl_sexp_wp)
    apply (simp)
   apply (rule_tac value_is_sexp)
   apply (auto)
    (* r = rb *)
  apply (case_tac "rb \<noteq> r")
   apply (simp add: pure_fun_def)
    (* the idea is that the infl_sexp_wp requirements are strictly greater than np_dom. since np_dom is strong, there is an exact way of
        subtracting to get to np_dom. (we do cheat a little by lifting rx2). *)
  apply (rule_tac t="np_dom_use_env env v" and s="diff_use_env (comp_use_env (lift_use_env rx2 r) (infl_use_env r_s2a r_s3))
    (diff_use_env (lift_use_env (comp_use_env (lift_use_env rx2 r) (infl_use_env r_s2a r_s3)) rb) (np_dom_use_env env v))" in subst)
   apply (rule_tac sfl_diff_use_env)
     apply (simp add: np_dom_use_env_def)
     apply (rule_tac strong_dom_use_env)
    (* to prove that the infl_sexp_wp reqs are greater than np_dom, we use the fact that any npv must have a permission *)
    apply (simp add: np_dom_use_env_def)
    apply (simp add: dom_use_env_def)
    apply (auto)
   apply (simp add: leq_use_env_def)
   apply (auto)
   apply (case_tac "comp_use_env (lift_use_env rx2 r) (infl_use_env r_s2a r_s3) x \<noteq> OwnPerm")
    apply (case_tac "comp_use_env rx2 (infl_use_env r_s2a r_s3) x = NoPerm")
     apply (cut_tac x="x" and env="env" and e="v" and ?r_s1.0="comp_use_env rx2 (infl_use_env r_s2a r_s3)" in well_typed_no_npv_use)
       apply (auto)
   apply (cut_tac r_sa="lift_use_env rx2 r" and r_sb="infl_use_env r_s2a r_s3" and x="x" in comp_use_no_own_both)
    apply (auto)
   apply (case_tac "rx2 x \<noteq> NoPerm")
    apply (simp add: is_own_def)
   apply (auto)
   apply (case_tac "infl_use_env r_s2a r_s3 x \<noteq> NoPerm")
    apply (simp add: infl_use_env_def)
    apply (case_tac "r_s2a x = OwnPerm \<and> r_s3 x = NoPerm")
     apply (auto)
   apply (cut_tac r_sa="rx2" and r_sb="infl_use_env r_s2a r_s3" and x="x" in comp_use_none)
     apply (auto)
    (* with that in mind, we manipulate until we match the infl sexp lemma *)
  apply (rule_tac well_typed_diff_perms)
   apply (rule_tac rx="comp_use_env rx2 (infl_use_env r_s2a r_s3)" in well_typed_incr_req)
     apply (rule_tac r_s="comp_use_env rx2 (infl_use_env r_s2a r_s3)" in well_typed_incr_simul_perm)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac comp_leq_use_env1)
       apply (rule_tac self_lift_leq_use_env)
      apply (rule_tac self_comp_leq_use_env2)
     apply (simp)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac comp_leq_use_env1)
     apply (rule_tac self_lift_leq_use_env)
    apply (rule_tac self_comp_leq_use_env2)
   apply (rule_tac id_leq_use_env)
    (* next, we must show that the differential is actually subtractible, which is true since it removes all non-prim vars *)
  apply (auto)
  apply (case_tac "np_dom_use_env env v x \<noteq> OwnPerm")
   apply (simp add: np_dom_use_env_def)
   apply (simp add: dom_use_env_def)
   apply (cut_tac r_s="lift_use_env (comp_use_env (lift_use_env rx2 r) (infl_use_env r_s2a r_s3)) r" and
       r_ex="np_dom_use_env env v" and x="x" in diff_use_none_ex)
    apply (simp)
  apply (simp add: own_env_vars_def)
  done
    
  
lemma safe_recv_exp: "\<lbrakk> well_typed env r_s1 (app_hole h (AppExp (ConstExp RecvConst) (VarExp (LocType a b)))) tau r_s2 rx;
  env (Loc a) = Some (ChanTy t REnd); well_typed env r_x v t r_x r_x; disj_use_env r_s1 r_x; 
  strong_use_env r_x; is_value c; is_value v; is_own r \<rbrakk> \<Longrightarrow>
  well_typed env (comp_use_env r_s1 r_x) (app_hole h v) tau r_s2 rx"  
  apply (induct h arbitrary: env r_s1 tau r_s2 rx)
       apply (auto)
    (* base case *)
       apply (cut_tac r_sc="r_s2" and r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 ra)) r_exa)" and
          r_sa="r_s1" in trans_leq_use_env)
         apply (rule_tac diff_leq_use_env)
         apply (rule_tac r_sb="diff_use_env r_s2a (comp_use_env (ereq_use_env (Loc b) tau_x) r_ex)" in trans_leq_use_env)
          apply (rule_tac diff_leq_use_env)
          apply (auto)
       apply (rule_tac ?r_s2.0="diff_use_env (comp_use_env r_s1 r_x) r_x"
        and rx="diff_use_env r_x r_x" in well_typed_simul_end_perm)
          apply (rule_tac well_typed_diff_end_perm)
           apply (rule_tac well_typed_comp_perms2)
            apply (simp add: pure_fun_def)
           apply (auto)
          apply (rule_tac comm_disj_use_env)
          apply (simp)
         apply (rule_tac self_comp_leq_use_env2)
        apply (rule_tac disj_diff_leq_use_env)
         apply (rule_tac r_s="r_s1" in disj_leq_use_env2)
          apply (rule_tac comm_disj_use_env)
          apply (simp_all)
        apply (rule_tac comp_leq_use_env1)
        apply (simp)
       apply (rule_tac cancel_strong_leq_use_env)
       apply (simp)
    (* lhs pair case. *)
      apply (rule_tac x="t1" in exI)
      apply (rule_tac x="ra" in exI)
      apply (rule_tac x="aa" in exI)
      apply (rule_tac x="r_s2a" in exI)
      apply (rule_tac x="rx1" in exI)
      apply (auto)
      apply (rule_tac x="rx2" in exI)
      apply (rule_tac x="r_s3" in exI)
      apply (auto)
      apply (rule_tac x="r_ex" in exI)
      apply (auto)
      apply (rule_tac comp_leq_use_env1)
      apply (simp)
    (* rhs pair case. *)
     apply (rule_tac x="t1" in exI)
     apply (rule_tac x="ra" in exI)
     apply (rule_tac x="aa" in exI)
     apply (rule_tac x="comp_use_env r_s2a r_x" in exI)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
      apply (rule_tac well_typed_comp_perms)
       apply (simp_all)
     apply (rule_tac x="rx2" in exI)
     apply (rule_tac x="r_s3" in exI)
     apply (auto)
      apply (cut_tac r_x="r_s2a" and r_s="r_s1" and r_ex="r_x" in disj_leq_use_env1)
        apply (simp)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
     apply (rule_tac x="r_ex" in exI)
     apply (auto)
     apply (rule_tac comp_leq_use_env1)
     apply (simp)
    (* if case. *)
    apply (rule_tac x="rx'" in exI)
    apply (rule_tac x="r_s2a" in exI)
    apply (auto)
    (* lhs pair case. *)
   apply (rule_tac x="r_s2a" in exI)
   apply (rule_tac x="r_s3" in exI)
   apply (rule_tac x="rx1" in exI)
   apply (auto)
   apply (rule_tac x="rx2" in exI)
   apply (auto)
   apply (rule_tac x="r_ex" in exI)
   apply (auto)
   apply (rule_tac comp_leq_use_env1)
   apply (simp)
    (* rhs pair case. *)
  apply (rule_tac x="comp_use_env r_s2a r_x" in exI)
  apply (rule_tac x="r_s3" in exI)
  apply (rule_tac x="rx1" in exI)
   apply (auto)
   apply (rule_tac well_typed_comp_perms)
    apply (simp_all)
  apply (rule_tac x="rx2" in exI)
   apply (auto)
   apply (cut_tac r_x="r_s2a" and r_s="r_s1" and r_ex="r_x" in disj_leq_use_env1)
     apply (simp)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
  apply (rule_tac x="r_ex" in exI)
  apply (auto)
  apply (rule_tac comp_leq_use_env1)
  apply (simp)
  done
    
lemma safe_own_npv_use: "\<lbrakk> well_typed env r_s1 (app_hole h (AppExp f v)) tau r_s2 rx; is_value f; strong_fun f;
  a \<noteq> NoRef; is_value v; x \<in> non_prim_vars env v \<rbrakk> \<Longrightarrow> r_s1 x = OwnPerm"
  apply (induct h arbitrary: env r_s1 r_s2 tau rx)
       apply (auto)
    (* base case *)
    apply (cut_tac f="f" and r="r" in strong_fun_own)
      apply (auto)
    apply (cut_tac env="env" and ?r_s1.0="r_s2a" and e="v" and ?r_s2.0="r_s3" and rx="rx2" in infl_sexp_wp)
      apply (auto)
     apply (rule_tac value_is_sexp)
     apply (simp)
    apply (case_tac "comp_use_env rx2 (infl_use_env r_s2a r_s3) x = NoPerm")
     apply (cut_tac env="env" and x="x" and e="v" and ?r_s1.0="comp_use_env rx2 (infl_use_env r_s2a r_s3)" in well_typed_no_npv_use)
       apply (auto)
    apply (case_tac "rx2 x \<noteq> NoPerm")
     apply (cut_tac r_x="lift_use_env rx2 r" and r_s="r_s1" and x="x" in leq_use_own)
      apply (simp add: is_own_def)
     apply (rule_tac r_sb="comp_use_env rx1 (lift_use_env rx2 r)" in trans_leq_use_env)
      apply (rule_tac r_sb="r_s3" in trans_leq_use_env)
       apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
        apply (auto)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
      apply (rule_tac well_typed_perm_leq)
      apply (auto)
     apply (rule_tac self_comp_leq_use_env2)
    apply (case_tac "infl_use_env r_s2a r_s3 x \<noteq> NoPerm")
     apply (simp add: infl_use_env_def)
     apply (case_tac "r_s2a x = OwnPerm \<and> r_s3 x = NoPerm")
      apply (auto)
     apply (rule_tac r_x="r_s2a" in leq_use_own)
      apply (auto)
     apply (rule_tac well_typed_perm_leq)
     apply (auto)
    apply (cut_tac r_sa="rx2" and r_sb="infl_use_env r_s2a r_s3" and x="x" in comp_use_none)
      apply (auto)
    (* rhs induct *)
   apply (rule_tac r_x="r_s2a" in leq_use_own)
    apply (simp)
   apply (rule_tac well_typed_perm_leq)
   apply (auto)
    (* rhs pair *)
  apply (rule_tac r_x="r_s2a" in leq_use_own)
   apply (simp)
  apply (rule_tac well_typed_perm_leq)
  apply (auto)
  done    
  
    
lemma safe_send_exp_ih: "\<lbrakk> well_typed env r_s1 (app_hole h (AppExp (AppExp (ConstExp SendConst) c) v)) tau r_s2 rx; is_value c; is_value v \<rbrakk> \<Longrightarrow>
  well_typed env r_s1 (app_hole h (ConstExp UnitConst)) tau r_s2 rx"  
  apply (induct h arbitrary: env r_s1 tau r_s2 rx)
       apply (auto)
    (* base case *)
        apply (simp add: pure_fun_def)
       apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 r)) r_ex)" in trans_leq_use_env)
        apply (rule_tac diff_leq_use_env)
        apply (rule_tac r_sb="r_s2a" in trans_leq_use_env)
         apply (rule_tac r_sb="diff_use_env r_s3a (comp_use_env (comp_use_env rx1a (lift_use_env rx2a ra)) r_exa)" in trans_leq_use_env)
          apply (rule_tac diff_leq_use_env)
          apply (rule_tac r_sb="r_s2b" in trans_leq_use_env)
           apply (simp_all)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)
    (* lhs app case *)
      apply (rule_tac x="t1" in exI)
      apply (rule_tac x="r" in exI)
      apply (rule_tac x="a" in exI)
      apply (rule_tac x="r_s2a" in exI)
      apply (rule_tac x="rx1" in exI)
      apply (auto)
    (* rhs app case *)
     apply (rule_tac x="t1" in exI)
     apply (rule_tac x="r" in exI)
     apply (rule_tac x="a" in exI)
     apply (rule_tac x="r_s2a" in exI)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
     apply (rule_tac x="rx2" in exI)
     apply (rule_tac x="r_s3" in exI)
     apply (auto) 
    (* if case *)
    apply (rule_tac x="rx'" in exI)
    apply (rule_tac x="r_s2a" in exI)
    apply (auto)
    (* lhs pair case *)
   apply (rule_tac x="r_s2a" in exI)
   apply (rule_tac x="r_s3" in exI)
   apply (rule_tac x="rx1" in exI)
   apply (auto)
    (* rhs pair case *)
  apply (rule_tac x="r_s2a" in exI)
  apply (rule_tac x="r_s3" in exI)
  apply (rule_tac x="rx1" in exI)
  apply (auto)
  apply (rule_tac x="rx2" in exI)
  apply (auto)
  done
    
    
lemma safe_send_exp: "\<lbrakk> well_typed env r_s1 (app_hole h (AppExp (AppExp (ConstExp SendConst) (VarExp (LocType a b))) v)) tau r_s2 rx;
  valid_nres_map s rs_map; valid_exp_use_env s rs_map r_s1; wf_hole h; is_value v \<rbrakk> \<Longrightarrow>
  well_typed env (diff_use_env r_s1 (full_dom_use_env env rs_map v)) (app_hole h (ConstExp UnitConst)) tau
    (diff_use_env r_s2 (full_dom_use_env env rs_map v)) (diff_use_env rx (full_dom_use_env env rs_map v))"  
  apply (rule_tac well_typed_diff_perms)
   apply (rule_tac c="VarExp (LocType a b)" in safe_send_exp_ih)
     apply (auto)
    (* we want to show that if xa is in the dominator, it is not an np-var in h.
        > if xa is an np-var itself, it cannot be in e by lemma *)
  apply (case_tac "x \<in> non_prim_vars env v")
   apply (cut_tac h="h" and x="x" and e="ConstExp UnitConst" in app_hole_res_vars_rev)
    apply (auto)
    apply (simp add: non_prim_vars_def)
   apply (cut_tac h="h" and x="x" and env="env" and ?r_s1.0="r_s1" and v="VarExp (LocType a b)" and e="v" in safe_send_hole_npv_use)
        apply (auto)
    (* otherwise, xa is in the completion. we identify its ancestor z. *)
  apply (simp add: own_env_vars_def)
  apply (simp add: full_dom_use_env_def)
  apply (simp add: dom_use_env_def)
  apply (case_tac "\<exists>xa. x = Loc xa \<and> (\<exists>l z. Loc z \<in> non_prim_vars env v \<and> path_lookup rs_map z l xa)")
   apply (auto)
    (* we note that z is a np-var of e therefore r_s1 z = Own *)
  apply (cut_tac x="Loc z" and env="env" and f="AppExp (ConstExp SendConst) (VarExp (LocType a b))" in safe_own_npv_use)
        apply (auto)
   apply (simp add: pure_fun_def)
   apply (simp add: is_own_def)
    (* xa then is in the lookup map of some parent y. *)
  apply (cut_tac rs_map="rs_map" and z="z" and x="xa" in path_lookup_parent)
     apply (auto)
    (* with that in mind, by separation, x is disjoint from r_s1. *)
  apply (case_tac "r_s1 (Loc xa) \<noteq> NoPerm")
   apply (simp add: valid_exp_use_env_def)
   apply (simp add: sep_nres_map_def)
   apply (auto)
   apply (erule_tac x="y" in allE)
   apply (simp add: nres_lookup_def)
   apply (simp add: strong_disj_use_env_def)
   apply (erule_tac x="Loc xa" in allE)
   apply (auto)
    (* by extension, x is not in 'h (send c v)' *)
  apply (cut_tac env="env" and ?r_s1.0="r_s1" and x="Loc xa" in well_typed_no_npv_use)
    apply (auto)
  apply (simp add: non_prim_vars_def)    
    (* the very last part is showing that x not in 'h (send c v)' implies x not in 'h ()'. *)
  apply (cut_tac x="Loc xa" and h="h" and e="ConstExp UnitConst" in app_hole_res_vars_rev)
   apply (auto)
  apply (cut_tac x="Loc xa" and h="h" and e="AppExp (AppExp (ConstExp SendConst) (VarExp (LocType a b))) v" in app_hole_res_vars2)
   apply (auto)
  done
    
lemma disj_lift_use_envr_rev: "\<lbrakk> strong_disj_use_env r_s r_x \<rbrakk> \<Longrightarrow> disj_use_env r_s (lift_use_env r_x r)"    
  apply (simp add: strong_disj_use_env_def)
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (auto)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (case_tac r)
     apply (auto)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac r)
    apply (auto)
  done
    
lemma lift_strong_disj_use_env1: "\<lbrakk> strong_disj_use_env r_x r_s \<rbrakk> \<Longrightarrow> strong_disj_use_env (lift_use_env r_x r) r_s"    
  apply (simp add: strong_disj_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac r)
    apply (auto)
  done
  
lemma send_disj_nres_map: "\<lbrakk> disj_nres_map p_map; p_map u1 = Some r_sa; p_map u2 = Some r_sb; is_own r;
  leq_use_env r_xa (lift_use_env r_sa r); leq_use_env r_xb (comp_use_env (lift_use_env r_sa r) (lift_use_env r_sb r));
  strong_disj_use_env r_xa r_xb \<rbrakk> \<Longrightarrow> disj_nres_map (add_env (add_env p_map u1 r_xa) u2 r_xb)"    
  apply (rule_tac disj_add_nres_map)  
   apply (rule_tac disj_add_nres_map)  
    apply (simp)
    (* proving disjointness for the send thread's material *)
   apply (rule_tac r_s="lift_use_env r_sa r" in leq_sep_nres_map)
    apply (simp)
   apply (simp add: disj_nres_map_def)
   apply (simp add: sep_nres_map_def)
   apply (auto)
   apply (case_tac "x = u1")
    apply (simp add: nres_lookup_def)
    apply (simp add: rem_env_def)
    apply (rule_tac empty_strong_disj_use_env2)
   apply (rule_tac lift_strong_disj_use_env1)
   apply (erule_tac x="u1" in allE)
   apply (erule_tac x="x" in allE)
   apply (simp add: nres_lookup_def)
   apply (simp add: rem_env_def)
    (* proving disjointness for the recv thread *)
  apply (simp add: sep_nres_map_def)
  apply (auto)
  apply (case_tac "u2 = x")
   apply (simp add: nres_lookup_def)
   apply (simp add: rem_env_def)
   apply (rule_tac empty_strong_disj_use_env2)
  apply (case_tac "u1 = x")
   apply (simp add: nres_lookup_def)
   apply (simp add: rem_env_def)
   apply (simp add: add_env_def)
   apply (rule_tac comm_strong_disj_use_env)
   apply (simp)
  apply (simp add: nres_lookup_def)
  apply (simp add: rem_env_def)
  apply (simp add: add_env_def)
  apply (simp add: disj_nres_map_def)
  apply (rule_tac r_s="comp_use_env (lift_use_env r_sa r) (lift_use_env r_sb r)" in strong_disj_leq_use_env1)
   apply (rule_tac strong_disj_comp_use_env2)
    apply (rule_tac lift_strong_disj_use_env1)
    apply (erule_tac x="u1" in allE)
    apply (erule_tac x="x" in allE)
    apply (simp add: nres_lookup_def)
   apply (rule_tac lift_strong_disj_use_env1)
   apply (erule_tac x="u2" in allE)
   apply (erule_tac x="x" in allE)
   apply (simp add: nres_lookup_def)
  apply (simp)
  done
  
fun proper_hole where
  "proper_hole rs_map ExpHole = True"
| "proper_hole rs_map (AppHole1 h e) = (proper_hole rs_map h \<and> proper_exp rs_map e)"    
| "proper_hole rs_map (AppHole2 v h) = (proper_exp rs_map v \<and> proper_hole rs_map h)"
| "proper_hole rs_map (IfHole h e1 e2) = (proper_hole rs_map h \<and> proper_exp rs_map e1 \<and> proper_exp rs_map e2)"  
| "proper_hole rs_map (PairHole1 h e) = (proper_hole rs_map h \<and> proper_exp rs_map e)"    
| "proper_hole rs_map (PairHole2 v h) = (proper_exp rs_map v \<and> proper_hole rs_map h)"
 
lemma proper_app_hole_split1: "\<lbrakk> proper_exp rs_map (app_hole h e) \<rbrakk> \<Longrightarrow> proper_hole rs_map h" 
  apply (induct h)
       apply (auto)
            apply (simp_all add: proper_exp_def)
  done

lemma proper_app_hole_split2: "\<lbrakk> proper_exp rs_map (app_hole h e) \<rbrakk> \<Longrightarrow> proper_exp rs_map e" 
  apply (induct h)
       apply (auto)
      apply (simp_all add: proper_exp_def)
  done
    
lemma proper_app_hole_recon: "\<lbrakk> proper_hole rs_map h; proper_exp rs_map e \<rbrakk> \<Longrightarrow> proper_exp rs_map (app_hole h e)"    
  apply (induct h)
       apply (auto)
      apply (simp_all add: proper_exp_def)
  done
  
lemma proper_app_hole: "\<lbrakk> proper_exp rs_map (app_hole h e1); proper_exp rs_map e2 \<rbrakk> \<Longrightarrow> proper_exp rs_map (app_hole h e2)"    
  apply (cut_tac rs_map="rs_map" and h="h" and e="e1" in proper_app_hole_split1)
   apply (auto)
  apply (rule_tac proper_app_hole_recon)
   apply (auto)
  done
  
lemma srps_send_case: "\<lbrakk>well_typed_system env rs_map p_map s2 ps1; valid_reduct app_red_exp; r_ax = SendAct;
        ps1 u1 = Some (app_hole h1 (AppExp (AppExp (ConstExp SendConst) (VarExp (LocType x_s a_s))) v));
        ps1 u2 = Some (app_hole h2 (AppExp (ConstExp RecvConst) (VarExp (LocType x_r a_r)))); u1 \<noteq> u2; wf_hole h1;
        wf_hole h2; is_value v; s2 x_s = Some ChanSValue;
        s2 x_r = Some (ChanRValue x_s); s1 = s2;
        ps2 = add_env (add_env ps1 u1 (app_hole h1 (ConstExp UnitConst))) u2 (app_hole h2 v)\<rbrakk>
       \<Longrightarrow> \<exists>r_s g_ax.
              (\<exists>p_map'. well_typed_system (red_env env g_ax) (red_nres_map rs_map g_ax) p_map' s2
                         (add_env (add_env ps1 u1 (app_hole h1 (ConstExp UnitConst))) u2 (app_hole h2 v))) \<and>
              safe_act s2 r_s g_ax"
      (* send case. no resources are generated in this step *)
  apply (rule_tac x="empty_use_env" in exI)
  apply (rule_tac x="NoResAct" in exI)
  apply (auto)
  apply (simp add: well_typed_system_def)
  apply (auto)
    (* we have to get the well-typedness statement for h1 [send c v] *)
  apply (case_tac "\<not> (case ps1 u1 of None \<Rightarrow> True | Some e \<Rightarrow> (case p_map u1 of None \<Rightarrow> False | Some r_s \<Rightarrow> \<exists>rx r_s2. well_typed env r_s e UnitTy r_s2 rx \<and> proper_exp rs_map e))")
   apply (simp add: well_typed_proc_set_def)
   apply (auto)
   apply (erule_tac x="u1" in allE)
   apply (erule_tac x="u1" in allE)
   apply (auto)
  apply (case_tac "p_map u1")
   apply (auto)
    (* we also get the well-typedness statement for h2 [recv c v] *)
  apply (case_tac "\<not> (case ps1 u2 of None \<Rightarrow> True | Some e \<Rightarrow> (case p_map u2 of None \<Rightarrow> False | Some r_s \<Rightarrow> \<exists>rx r_s2. well_typed env r_s e UnitTy r_s2 rx \<and> proper_exp rs_map e))")
   apply (simp add: well_typed_proc_set_def)
   apply (auto)
   apply (erule_tac x="u2" in allE)
   apply (erule_tac x="u2" in allE)
   apply (auto)
  apply (case_tac "p_map u2")
   apply (auto)
    (* next we get the send channel's type *)
  apply (case_tac "\<not> (\<exists> t. env (Loc x_s) = Some (ChanTy t SEnd))")
   apply (simp add: well_typed_state_def)
   apply (auto)
   apply (erule_tac x="x_s" in allE)
   apply (erule_tac x="x_s" in allE)
   apply (auto)
   apply (case_tac "env (Loc x_s)")
    apply (auto)
    (* and the recv channel's type *)
  apply (case_tac "\<not> env (Loc x_r) = Some (ChanTy t REnd)")
   apply (simp add: well_typed_state_def)
   apply (auto)
   apply (erule_tac x="x_r" in allE)
   apply (erule_tac x="x_r" in allE)
   apply (auto)
   apply (case_tac "env (Loc x_r)")
    apply (auto)
    (* prelim: we prove the dominator of v \<le> lift a r (the permission map of u1) *)
  apply (cut_tac eq_own)
  apply (auto)
  apply (cut_tac r_sc="np_dom_use_env env v" and r_sb="np_dom_use_env env (app_hole h1 (AppExp (AppExp (ConstExp SendConst) (VarExp (LocType x_s a_s))) v))"
      and r_sa="lift_use_env a r" in trans_leq_use_env)
    apply (rule_tac wt_np_leq_use_env)
     apply (auto)
   apply (simp add: np_dom_use_env_def)
   apply (rule_tac dist_dom_leq_use_env)
   apply (auto)
   apply (simp add: non_prim_vars_def)
   apply (rule_tac app_hole_res_vars)
   apply (auto)
    (* we can generate a type for h1 () *)
  apply (cut_tac env="env" and v="v" and ?r_s1.0="a" and tau="UnitTy" and h="h1" and ?r_s2.0="r_s2" and rx="rx" and s="s2" and rs_map="rs_map" in safe_send_exp)
        apply (auto)
    apply (simp add: well_typed_state_def)
    (* - complete proof that a is still valid *)
   apply (simp add: valid_exp_use_env_def)
   apply (simp add: well_typed_proc_set_def)
   apply (simp add: sub_nres_map_def)
   apply (erule_tac x="u1" in allE)
   apply (erule_tac x="u1" in allE)
   apply (simp add: nres_lookup_def)
    (* we can also generate a type for h2 v, first by getting a type for v, and then by putting it in the hole *)
  apply (cut_tac env="env" and v="v" and h="h1" and a="x_s" and a="a_s" and t="t" in safe_val_exp)
      apply (auto)
  apply (cut_tac env="env" and ?r_s1.0="aa" and h="h2" and r_x="np_dom_use_env env v" in safe_recv_exp)
          apply (auto)
    (* - p_map disjointness proves that the permissions being added are disjoint *)
    apply (rule_tac r_s="lift_use_env a r" in disj_leq_use_env2)
     apply (case_tac "\<forall>x y. x \<noteq> y \<longrightarrow> strong_disj_use_env (nres_lookup p_map x) (nres_lookup p_map y)")
      apply (erule_tac x="u1" in allE)
      apply (erule_tac x="u2" in allE)
      apply (erule_tac x="u1" in allE)
      apply (auto)
     apply (simp add: nres_lookup_def)
     apply (rule_tac disj_lift_use_envr_rev)
     apply (simp)
    apply (simp add: well_typed_proc_set_def)
    apply (simp add: disj_nres_map_def)
    (* - proving the dominator is strong *)
   apply (simp add: np_dom_use_env_def)
   apply (rule_tac strong_dom_use_env)
    (* lastly it remains to prove the new process map is well-formed *)
  apply (rule_tac x="add_env (add_env p_map u1 (diff_use_env a (full_dom_use_env env rs_map v)))
    u2 (comp_use_env aa (np_dom_use_env env v))" in exI)
  apply (simp add: well_typed_proc_set_def)
  apply (auto)
    (* completeness *)
      apply (rule_tac add_full_nres_map)
      apply (rule_tac add_full_nres_map)
      apply (simp)
    (* disjointness, assisted by lemma *)
     apply (rule_tac r_sa="a" and r_sb="aa" in send_disj_nres_map)
           apply (simp_all)
       apply (rule_tac diff_leq_use_env)
       apply (rule_tac self_lift_leq_use_env)
      apply (rule_tac dist_comp_leq_use_env)
       apply (rule_tac comp_leq_use_env2)
       apply (rule_tac self_lift_leq_use_env)
      apply (rule_tac comp_leq_use_env1)
      apply (simp)
     apply (rule_tac strong_disj_comp_use_env1)
      apply (rule_tac r_s="a" in strong_disj_leq_use_env1)
       apply (simp add: disj_nres_map_def)
       apply (erule_tac x="u1" in allE)
       apply (erule_tac x="u1" in allE)
       apply (erule_tac x="u1" in allE)
       apply (erule_tac x="u2" in allE)
       apply (simp add: nres_lookup_def)
      apply (rule_tac self_diff_leq_use_env)
     apply (rule_tac r_s="full_dom_use_env env rs_map v" in strong_disj_leq_use_env2)
      apply (rule_tac diff_strong_disj_use_env)
      apply (simp add: full_dom_use_env_def)
      apply (rule_tac strong_dom_use_env)
     apply (rule_tac full_dom_leq_use_env)
    (* proving that the processes are well-typed *)
    apply (case_tac "u = u1")
     apply (simp add: add_env_def)
     apply (auto)
     apply (rule_tac proper_app_hole)
      apply (simp)
     apply (simp add: proper_exp_def)
    apply (case_tac "u = u2")
     apply (simp add: add_env_def)
     apply (auto)
     apply (rule_tac proper_app_hole)
      apply (simp)
     apply (cut_tac rs_map="rs_map" and h="h1" and e="AppExp (AppExp (ConstExp SendConst) (VarExp (LocType x_s a_s))) v" in proper_app_hole_split2)
      apply (simp)
     apply (simp add: proper_exp_def)
    apply (simp add: add_env_def)
    apply (erule_tac x="u" in allE)
    apply (erule_tac x="u" in allE)
    apply (case_tac "ps1 u")
     apply (auto)
    apply (simp add: add_env_def)
    (* proving res_map element containment *)
   apply (rule_tac add_sub_nres_map1)
    apply (rule_tac add_sub_nres_map1)
     apply (simp)
    apply (rule_tac r_s="a" in trans_sub_use_env)
     apply (simp add: sub_nres_map_def)
     apply (erule_tac x="u1" in allE)
     apply (simp add: nres_lookup_def)
    apply (rule_tac self_diff_leq_use_env)
   apply (rule_tac comp_sub_use_env)
    apply (simp add: sub_nres_map_def)
    apply (erule_tac x="u2" in allE)
    apply (simp add: nres_lookup_def)
   apply (rule_tac r_s="lift_use_env a r" in trans_sub_use_env)
    apply (rule_tac lift_sub_use_env)
    apply (simp add: sub_nres_map_def)
    apply (erule_tac x="u1" in allE)
    apply (simp add: nres_lookup_def)
   apply (simp)
    (* poriving the separation of the new maps *)
  apply (case_tac "u = u1")
   apply (simp add: add_env_def)
   apply (rule_tac r_s="a" in leq_sep_nres_map)
    apply (rule_tac self_diff_leq_use_env)
   apply (erule_tac x="u1" in allE)
   apply (auto)
  apply (case_tac "u = u2")
   apply (simp add: add_env_def)
   apply (rule_tac comp_sep_nres_map)
    apply (erule_tac x="u2" in allE)
    apply (auto)
   apply (erule_tac x="u1" in allE)
   apply (auto)
   apply (rule_tac r_s="lift_use_env a r" in leq_sep_nres_map)
    apply (simp)
   apply (simp add: sep_nres_map_def)
    apply (auto)
   apply (rule_tac lift_strong_disj_use_env1)
   apply (simp)
  apply (simp add: add_env_def)
  done
    
    
end