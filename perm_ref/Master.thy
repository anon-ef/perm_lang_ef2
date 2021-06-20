theory Master
  imports RedSafeAppLemma ProcLemma ExclLemma WellTypedAlt SolverInfer
begin
  
lemma safe_red_all: "\<lbrakk> well_typed_system env rs_map p_map s1 ps1; red_proc_set (s1, ps1) r_ax (s2, ps2) \<rbrakk> \<Longrightarrow>
  (\<exists> r_s g_ax p_map'. well_typed_system (red_env env g_ax) (red_nres_map rs_map g_ax) p_map' s2 ps2 \<and> safe_act s1 r_s g_ax)"  
  apply (rule_tac safe_red_proc_set)
    apply (auto)
  apply (rule_tac sares_valid)
  done

end