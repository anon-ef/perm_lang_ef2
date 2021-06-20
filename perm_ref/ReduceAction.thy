theory ReduceAction
  imports ReduceProper ReduceWTS
begin
  
  (* ###### constructive permission definitions.
      the idea here is that i want to constructively state which permissions are being consumed.
      the difficult part is that because the "permissions consumed" involves 
  *)
    
datatype gen_act =
  NoResAct
  | AddResAct string p_type perm_use_env
  | Add2ResAct string string p_type
  | ReadResAct
  | WriteResAct string perm_use_env
    
fun red_env :: "pt_env \<Rightarrow> gen_act \<Rightarrow> pt_env" where
  "red_env env NoResAct = env"
| "red_env env (AddResAct x tau r_s) = add_env env (Loc x) tau"
| "red_env env (Add2ResAct x1 x2 tau) = add_env (add_env env (Loc x1) (ChanTy tau SEnd)) (Loc x2) (ChanTy tau REnd)"
| "red_env env ReadResAct = env"
| "red_env env (WriteResAct x r_s) = env"

fun exp_red_use_env where
  "exp_red_use_env r_s NoResAct = r_s"
  (* remove resources used to create the value, add the new perm *)
| "exp_red_use_env r_s (AddResAct x tau r_s') = add_use_env r_s (Loc x) OwnPerm"
| "exp_red_use_env r_s (Add2ResAct x1 x2 tau) = add_use_env (add_use_env r_s (Loc x1) OwnPerm) (Loc x2) OwnPerm"
| "exp_red_use_env r_s ReadResAct = r_s"  
| "exp_red_use_env r_s (WriteResAct x r_s') = (diff_use_env r_s r_s')"
  
fun end_red_use_env where  
  "end_red_use_env r_s (WriteResAct x r_s') = (diff_use_env r_s r_s')"
| "end_red_use_env r_s r_ax = r_s"
  
fun red_nres_map :: "nres_map \<Rightarrow> gen_act \<Rightarrow> nres_map" where
  "red_nres_map rs_map NoResAct = rs_map"  
| "red_nres_map rs_map (AddResAct x tau r_s) = add_env rs_map x r_s"
| "red_nres_map rs_map (Add2ResAct x1 x2 tau) = add_env (add_env rs_map x1 empty_use_env) x2 empty_use_env"
| "red_nres_map rs_map ReadResAct = rs_map"
| "red_nres_map rs_map (WriteResAct x r_s) = add_env rs_map x (comp_use_env (nres_lookup rs_map x) r_s)"
  
fun safe_act where
  "safe_act s r_s NoResAct = True"
| "safe_act s r_s (AddResAct x tau r_x) = (s x = None \<and> leq_use_env r_x r_s)"
| "safe_act s r_s (Add2ResAct x1 x2 tau) = (s x1 = None \<and> s x2 = None \<and> x1 \<noteq> x2)"
| "safe_act s r_s ReadResAct = True"
| "safe_act s r_s (WriteResAct x r_x) = (s x \<noteq> None \<and> leq_use_env r_x r_s)"
  
fun corr_act where
  "corr_act ax NoResAct = (ax = NoAct)"
| "corr_act ax (AddResAct x tau r_s) = (ax = MakeAct x)"
| "corr_act ax (Add2ResAct x1 x2 tau) = (ax = Mk2Act x1 x2)"
| "corr_act ax ReadResAct = (\<exists> x. ax = UseAct x)"
| "corr_act ax (WriteResAct x r_s) = (\<exists> x. ax = UseAct x)"  
  
    
lemma leq_safe_act: "\<lbrakk> safe_act s r_x g_ax; leq_use_env r_x r_s \<rbrakk> \<Longrightarrow> safe_act s r_s g_ax"    
  apply (case_tac g_ax)
      apply (auto)
   apply (rule_tac r_sb="r_x" in trans_leq_use_env)
    apply (auto)
  apply (rule_tac r_sb="r_x" in trans_leq_use_env)
   apply (auto)
  done  
  
  
definition valid_reduct where
  "valid_reduct r_exp = (\<forall> are s1 rs_map env r_f r_s1 e1 tau r_s2 rx ax s2 e2. (
    r_exp are (s1, e1) ax (s2, e2) \<and> well_typed env r_s1 e1 tau r_s2 rx \<and> proper_exp rs_map e1 \<and>
    well_typed_state s1 env rs_map \<and> valid_exp_use_env s1 rs_map r_f \<and> leq_use_env r_s1 r_f) \<longrightarrow>
    (\<exists> g_ax. well_typed (red_env env g_ax) (exp_red_use_env r_s1 g_ax) e2 tau (end_red_use_env r_s2 g_ax) (end_red_use_env rx g_ax) \<and>
      proper_exp (red_nres_map rs_map g_ax) e2 \<and> well_typed_state s2 (red_env env g_ax) (red_nres_map rs_map g_ax) \<and>
      valid_exp_use_env s2 (red_nres_map rs_map g_ax) (exp_red_use_env r_f g_ax) \<and> safe_act s1 (infl_use_env r_f r_s2) g_ax \<and> corr_act ax g_ax)
  )"  
  
  
lemma red_contain_env: "\<lbrakk> safe_act s r_s g_ax; sub_env s env \<rbrakk> \<Longrightarrow> contain_env (red_env env g_ax) env"
  apply (case_tac g_ax)
      apply (auto)
      apply (rule_tac id_contain_env)
     apply (rule_tac add_contain_env)
     apply (simp add: sub_env_def)
     apply (erule_tac x="Loc x21" in allE)
     apply (auto)
    apply (rule_tac env_b="add_env env (Loc x31) (ChanTy x33 SEnd)" in trans_contain_env)
     apply (rule_tac add_contain_env)
     apply (simp add: add_env_def)
     apply (case_tac "env (Loc x32)")
      apply (auto)
     apply (simp add: sub_env_def)
     apply (erule_tac x="Loc x32" in allE)
     apply (auto)
    apply (rule_tac add_contain_env)
    apply (case_tac "env (Loc x31)")
     apply (auto)
    apply (simp add: sub_env_def)
    apply (erule_tac x="Loc x31" in allE)
    apply (auto)
   apply (rule_tac id_contain_env)
  apply (rule_tac id_contain_env)
  done  
    
    (* ##### safe-reduction specific validity lemmas ##### *)
  
lemma red_sep_nres_map: "\<lbrakk> p_map u = Some r_s; disj_nres_map p_map; sub_nres_map s1 p_map;
  safe_act s1 r_s g_ax; sub_use_env s1 r_s \<rbrakk> \<Longrightarrow> sep_nres_map (exp_red_use_env r_s g_ax) (rem_env p_map u)"
  apply (simp add: sep_nres_map_def)
  apply (auto)
    (* we dont have to check x = u, since u has been removed from the map *)
  apply (case_tac "u = x")
   apply (auto)
   apply (simp add: nres_lookup_def)
   apply (simp add: rem_env_def)
   apply (rule_tac empty_strong_disj_use_env2)
    (* otherwise, the lookup is the same as it was in p_map *)
  apply (cut_tac rs_map="p_map" and x="u" and y="x" in nres_rem_diff)
   apply (auto)
    (* from here we do case analysis on the possible ways that r_s has been modified *)
    (* if it has not been modified the case is simple *)
  apply (case_tac "exp_red_use_env r_s g_ax = r_s")
   apply (simp add: disj_nres_map_def)
   apply (erule_tac x="u" in allE)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (simp add: nres_lookup_def)
    (* make case: if x21 has been added, the rest of r_s is disjoint from p_map x *)
  apply (case_tac g_ax)
     apply (auto)
    apply (rule_tac add_strong_disj_use_env)
     apply (simp add: disj_nres_map_def)
     apply (erule_tac x="u" in allE)
     apply (erule_tac x="x" in allE)
     apply (auto)
     apply (simp add: nres_lookup_def)
    (* now we have to prove that x21 was not in p_map, which should be true since p_map is sub-ordinate to s *)
    apply (case_tac "p_map x")
     apply (simp add: nres_lookup_def)
     apply (simp add: empty_use_env_def)
    apply (simp add: sub_nres_map_def)
    apply (erule_tac x="x" in allE)
    apply (simp add: sub_use_env_def)
    apply (erule_tac x="Loc x21" in allE)
    apply (auto)
    (* make 2 case: start by assuming we have p_map x *)
   apply (case_tac "p_map x")
    apply (simp add: nres_lookup_def)
    apply (rule_tac empty_strong_disj_use_env2)
    (* otherwise, prove r_s disjoint from p_map x *)
   apply (rule_tac add_strong_disj_use_env)
    apply (rule_tac add_strong_disj_use_env)
     apply (simp add: disj_nres_map_def)
     apply (erule_tac x="u" in allE)
     apply (erule_tac x="x" in allE)
     apply (auto)
     apply (simp add: nres_lookup_def)
    (* after this, prove x31 / x32 do not appear in p_map x *)
    apply (simp add: sub_nres_map_def)
    apply (erule_tac x="x" in allE)
    apply (simp add: sub_use_env_def)
    apply (erule_tac x="Loc x31" in allE)
    apply (auto)
   apply (simp add: sub_nres_map_def)
   apply (erule_tac x="x" in allE)
   apply (simp add: sub_use_env_def)
   apply (erule_tac x="Loc x32" in allE)
    apply (auto)
    (* write case: otherwise, x42 was removed from r_s, so disjointness should be simple *)
  apply (rule_tac r_s="r_s" in strong_disj_leq_use_env1)
   apply (simp add: disj_nres_map_def)
   apply (erule_tac x="u" in allE)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (simp add: nres_lookup_def)
  apply (rule_tac self_diff_leq_use_env)
  done  

lemma red_sep_nres_map2: "\<lbrakk> p_map v = Some r_p; p_map u = Some r_s; u \<noteq> v; disj_nres_map p_map;
  safe_act s1 r_s g_ax; sep_nres_map r_p rs_map \<rbrakk> \<Longrightarrow> sep_nres_map r_p (red_nres_map rs_map g_ax)"    
  apply (case_tac g_ax)
      apply (auto)
    (* make case *)
    apply (rule_tac add_sep_nres_map)
     apply (simp)
    apply (rule_tac r_s="r_s" in strong_disj_leq_use_env2)
     apply (simp add: disj_nres_map_def)
     apply (auto)
    apply (erule_tac x="v" in allE)
    apply (erule_tac x="u" in allE)
    apply (simp add: nres_lookup_def)
    (* make 2 case *)
   apply (rule_tac add_sep_nres_map)
    apply (rule_tac add_sep_nres_map)
     apply (simp)
    apply (rule_tac empty_strong_disj_use_env2)
   apply (rule_tac empty_strong_disj_use_env2)
    (* write case *)
  apply (rule_tac add_sep_nres_map)
   apply (simp)
  apply (rule_tac strong_disj_comp_use_env1)
   apply (simp add: sep_nres_map_def)
  apply (rule_tac r_s="r_s" in strong_disj_leq_use_env2)
   apply (simp add: disj_nres_map_def)
   apply (erule_tac x="v" in allE)
   apply (erule_tac x="u" in allE)
   apply (simp add: nres_lookup_def)
  apply (simp)
  done    
  
end