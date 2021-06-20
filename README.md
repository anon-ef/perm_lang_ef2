# perm_lang_ax2

This repository contains Isabelle theory files that formalize the definitions and proofs given in "Types for Race Freedom in an Imperative Concurrent Programming Language."

These theory files are presented primarily as proof of concept for the correctness of our results, but no promises are made with respect to their readability. Definitions are generally not organized in the same way as they are in the paper, and in some cases our definitions differ slightly (with non-trivial changes proven to be equialvent). Many of these differences are not significant, but an artifact of how the proofs were originally constructed.

This document serves as an index describing where definitions from the paper correspond to definitions in the theory, as well as any differences that may exist.

# 1 Overview

This section gives a general guide to the organization of the theory files. Skip to Section 2 for how definitions and theorems from the paper correspond to theories.

All theory files can be loaded from loading `Master.thy`, which imports all other relevant theory files.

## 1.1 General definitions
Contain general definitions of permissions, types, permission + type environments, and various properties and lemmas over them.

- GenEnv.thy: A generalized environment type used to define type environments and memories.
- PermEnv.thy: Basic permission and permission environment related definitions.
- GenSubEnv.thy: Definitions for whether environments have domains that are subsets of one another.
- PermEnvEq.thy: Lemmas about equality for permission environments operations.
- PermEnvLeq.thy: Lemmas about ordering for permission environments operations.
- LiftEnv.thy: Definition and lemmas of permission environment lifting.
- PermEnvMisc.thy: Lemmas about lifting and disjointness for permission environments operations.
- TypeEnv.thy: Definitions of types and type environments.

## 1.2 Type definitions
Definitions and lemmas for the type system.

- WTMiscEnv.thy: Miscellaneous definitions used for the typing rules, as well as lemmas concerning function affinity.
- WellTypedExp.thy: Contains rules for our type system that differ from the typing rules given in the paper.
- WellTypedAlt.thy: The rules of our type system exactly as given in the paper (and a proof that our two rule constructions are equivalent).
- WTLemma.thy: General lemmas about well-typedness.

## 1.3 Flat permissions lemma
Definitions which are used to prove the "flat permissions lemma" (`infl_sexp_wp` in `AltFlatLemma.thy`), an important lemma about typing values (a value can be typed with end permissions equal to the start permissions).

- AltNormEnv.thy: Defines `norm_use_env`, which restricts the domain of one permission environment to another.
- AltDropEnv.thy: Defines `drop_use_env`, which defines permission environment dropping, an operation analogous to permission environment lifting.
- AltCutEnv.thy: Defines `cut_use_env`, which removes use permissions from a permission environment.
- AltFlatLemma.thy: The flat permission lemma.

## 1.4 "End permissions lower bound" lemma
Definitions which are used to prove the "end permissions lower bound lemma" (`well_typed_end_perm_lbound` in `AltLBoundLemma.thy`), a minor lemma which given an arbitrary well-typed expression, demonstrates that it can be typed in a form required for certain proofs.

- AltSuperNormEnv.thy: Defines `super_norm_use_env`, a stricter version of `norm_use_env`.
- AltLBoundLemma.thy: The end permissions lower bound lemma.

## 1.5 Safe substitution type preservation lemma
Definitions for the proof that substitution maintains well-typedness.

- SubstExp.thy: Defines substitution and related concepts (free variables, lambda variables, etc).
- SubstDropEnv.thy: Lemmas about well-typedness and permission environment dropping.
- SubstTPX.thy: Defines the main inductive hypothesis for our safe substitution proof.
- SafeSubRename.thy: Proves that renaming an expression in safe ways maintains well-typedness.
- SafeSubTPX.thy: The main proof that substitution with "safe" renaming maintains well-typedness.

## 1.6 Memory map definitions
General definitions for memory maps

- ResMap.thy: Defines memory maps and short lemmas.
- ResMapDisj.thy: Exclusivity related definitions for memory maps.
- ResMapValid.thy: Specialized definitions used for defining a well-typed system.

## 1.7 Safe reduction of expressions
Case analysis proving that expression reductions that don't involve holes preserve well-typedness.

- ReduceProper.thy: Defines memory location ownership / proper expressions.
- ReduceExp.thy: Defines the rules for reduction besides reduction in holes.
- ReduceSetOwn.thy: Proves that the re-labelling of memory location owners performed during array reads preserves well-typedness.
- ReduceWTS.thy: Defines well-typedness for memory.
- ReduceAction.thy: Auxiliary definitions used to define the induction hypothesis for safe reduction.
- RedSafeUnpack.thy: The case for pair unpacking of safe reduction.
- RedSafeCV.thy: The case for all partially applied constant functions of safe reduction (uses the unpacking case).
- RedSafeCase.thy: The case for all constants of safe reduction.
- RedSafeAppLemma.thy: The main proof that reduction of expressions maintains well-typedness.
- RedSafeHoleLemma.thy: Proves reduction preserves well-typedness for the case of reduction in a hole.

## 1.8 Safe reduction of process sets
Case analysis proving that process set reduction preserve well-typedness.

- ProcCVars.thy: Defines `np_dom_use_env` which generates a permission environment based on variables contained in expressions, and `full_dom_use_env` which generates a permission environment based on expression variables and the memory locations owned by them.
- ProcHoleVars.thy: Defines a notion of free variables for holes.
- ProcDef.thy: Defines reduction and well-typedness for process sets.
- ProcSendCase.thy: The case for sending / receiving memory locations for safe reduction of process sets.
- ProcLemma.thy: The main proof that reduction of process sets maintains well-typedness.

## 1.9 Mutual Exclusion
Short proof for the correctness of mutual exclusion

- ExclLemma.thy: The proof of the correctness of mutual exclusion.

## 1.10 Inference algorithm
Definition of inference algorithm and its proofs of correctness.

- InferVar.thy: Extends permissions and types with variables.
- InferRange.thy: Definitions of ranges / domains for type / permission expression environments.
- InferDef.thy: The definition of the inference algorithm.
- InferSound.thy: The proof of soundness for the inference algorithm.
- InferComplete.thy: The proof of completeness for the inference algorithm.

## 1.11 Solver algorithm
Definition of the constraint solver for the algorithm.

- SolverP1.thy: The definition of phase 1a of the constraint solver (type unification) and proofs of correctness.
- SolverP1b.thy: The definition of phase 1b of the constraint solver (permission unification for permissions in types), used to convert the constraints into the intermediate constraints, together with proofs of correctness.
- SolverP2.thy: The definition of phase 2 of the constraint solver, and its proof of correctness.
- SolverP3.thy: The definition of phase 3 of the constraint solver, together with proofs of correctness.
- SolverInfer.thy: Combines the proofs of correctness for the inference algorithm and solver to prove fully that the inference algorithm is correct.

# 2 Language Syntax and Semantics

## 2.1 Constants
In our language constants `c` are presented as a single syntactic category. In our theory they are split into "constants" (which include primitive constant values and special function constants) and "operators" (function constants for primitive values) so that primitive constant functions can be added without disturbing certain proofs related to the other constants. However, they behave the same way semantically and when types as the other primitive constant values.

Specifically, constants are defined through `p_const` and `p_op` in `WellTypedExp.thy`.

## 2.2 Expressions
Expressions `e` are defined by `p_exp` in `WellTypedExp.thy`. Unlike the paper, no specific syntactic category is given for memory location values. Memory location values are similar enough to variables that they are both considered to be cases of `VarExp v`, differentiated based on whether `v` is a `VarType` or ` LocType`.

## 2.3 Semantics for Expressions
Values `v` are defined by the predicate `is_value` in `WellTypedExp.thy`, where the `bin_op` function is formalized as `bin_const`. Another predicate `is_sexp` is defined as a useful superset of `is_value` that denotes expressions that may be applied in a substitution while preserving well-typedness.

Memory values `m` are defined as a datatype `mem_value` in `ReduceExp.thy`. Memories `M` are defined as `p_state` in `ReduceExp.thy`.

Holes `h` are defined by `p_hole` in `RedSafeHoleLemma.thy`.

The semantics for reduction are defined by `full_red_exp` in `RedSafeHoleLemma.thy`. The definition of `full_red_exp` makes heavy use of `app_red_exp`, which defines every reduction rule besides the rule for reduction on holes. `app_red_exp` is defined in `ReduceExp.thy`.

The `set_own` function for array reads is defined by `set_own` in `ReduceSetOwn.thy`.

## 2.4 Semantics for Process Sets

Process sets are defined by `proc_set` in `ProcDef.thy`. It makes use of `gen_env`, a general datatype defined in `GenEnv.thy` for mapping strings to datatypes, in this case to expressions.

The semantics for reduction on process sets is given by `red_proc_set` in `ProcDef.thy`.

# 3 Type System

## 3.1 Permissions

All relevant definitions for this section are contained in `PermEnv.thy`. Permissions `p` are defined by `p_perm`. Our ordering on permissions is defined by `leq_perm`. Permissions composition is defined by `union_perm`. Permission environments are defined by `perm_use_env`.

Our ordering on permission environments is defined as `leq_use_env` and joining of permission environments is defined by `comp_use_env`. Subtraction of permission environment is defined by `diff_use_env`.

## 3.2 Types

The definition of a type `tau` is given by `p_type` in `TypeEnv.thy`. One difference from the paper of the datatype `p_aff` instead of a permission (`p_perm`) to define the affinity of a function. There is a direct correlation between affinities and permissions given by `as_perm`. This distinction is unnecessary, and exists as a matter of coding style to force explicit conversion when comparing affinities to other permissions.

Type environments are given by `pt_env`.

## 3.3 Typing Expressions

The rules of our type system are given by `well_typed` in `WellTypedExp.thy`. Note that these rules are different from the rules given in the paper in that the rules for weakening / strengthening the end permissions / requirements are not explicit, but directly baked into the rules. A definition of the rules exactly as given in the paper is given by `well_typed_alt` in `WellTypedAlt.thy`, and a proof of their equivalence to each other is given through `well_typed_equiv1` and `well_typed_equiv2`.

The definition of constant type signatures is given through `const_type` and `op_type`, and the definition of `req` (the minimal permission environments for types) is given by `req_type`. These definitions are also in `WellTypedExp.thy`.

Disjointness of permission environments is given by `disj_use_env` in `PermEnv.thy`. Disjointness of individual permissions is not defined directly, but it can be shown that the definition of `disj_use_env` matches the one given in the paper.

Lifting of permission environments is given by `lift_use_env` in `LiftEnv.thy`.

## 3.4 Typing Memory

The rules for typing memory values are given by `well_typed_mem_value` in `ReduceWTS.thy`. Permission environment exclusivity is defined by `strong_disj_use_env` in `ResMapDisj.thy`. Exclusivity of array permission maps is defined by `disj_res_list` in `ReduceWTS.thy`.

A memory map `f` is defined by `res_map` in `ResMap.thy`. Exclusivity for resource maps is defined by `disj_nres_map` in `ResMapDisj.thy`.

Permission environment containment in memory is defined by `sub_use_env` in `GenSubEnv.thy`. The `well_typed_mem` definition given in the paper is defined as `well_typed_state` in `ReduceWTS.thy`. This definition differs from the definition given in the paper in that it includes the requirement that memory values be proper.

## 3.5 Typing Process Sets and Systems

The `well_typed_pset` definition given in the paper is defined as `well_typed_proc_set` in `ProcDef.thy`. It differs from the definition given in the paper in that it also includes the requirement that process bodies are proper.

Separation of a permission environment from a memory map is defined by `sep_nres_map` in `ResMapDisj.thy`. Memory ownership is defined by `path_lookup` in `DerefVars.thy`. The definition of a proper expression is given by `proper_exp` in `DerefVars.thy`, and the definition of a proper memory value is given by `proper_mem_value` in `ReduceWTS.thy`. 

The `well_typed_sys` definition given in the paper is defined as `well_typed_system` in `ProcDef.thy`. Note that the requirements that the memory value and process bodies be proper were already included in `well_typed_state` and `well_typed_pset`, and the requirement that all permission environments be contained within the memory `M` is given by `sub_nres_map`, defined in `ResMapDisj.thy`.

# 4. Results

## 4.1 Race Freedom
The proof of Theorem 1 (Race Freedom) is given by `excl_safe_lemma` in `ExclLemma.thy`. This proof is relatively simple in concept, although it does make use of several additional auxiliary definitions. It is suggested that the proof of Theorem 2 is examined before looking at the proof of Theorem 1.

## 4.2 Type Preservation
The bulk of our theory is the proof of Theorem 2 (Type Preservation) is given by `safe_red_all` in `Master.thy`. This theorem makes use of two major lemmas.

The first is `sares_valid` in `SafeRedAppLemma.thy`, the proof of `sares_valid` is based on `safe_app_red_exp_strict`, a proof that reductions on expressions not involving holes preserves well-typedness (with respect to several inductive constraints). Two of its cases, proven in lemmas `sares_lam_case` and `sares_fix_case` make substantial use of the lemma `safe_subst_type_preserve_x` defined in `SafeSubTPX.thy`, which asserts that substitution (defined with variables renamed to prevent lambda capture) preserves well-typedness.

The main inductive hypothesis is defined for `safe_subst_type_preserve_x` is given by `subst_type_preserve_x` defined in `SubstTPX.thy`.

The second major lemma is `safe_red_proc_set` in `ProcLemma.thy`, which proves that process reduction is well-typed under the assumption proved by `sares_valid`.

## 4.3 Type Inference
Permission terms are defined by `s_perm` in `InferVar.thy`. Permission expressions are defined by `x_perm` and extended types are defined by `s_type` also in `InferVar.thy`. Constraints `kappa` are given by `perm_crn` in `InferDef.thy`. Semi-disjointness is defined by `mini_disj_use_env` in `PermEnv.thy`.

Two types of type substitutions are defined in `InferVar.thy`, `type_subst` returns types extended with type variables, `dir_type_subst` assumes types returned by substitution do not have type variables. Solvability is defined for `dir_type_subst`, however `type_subst` is used in other places as appropriate. Permission substitutions are defined by `perm_subst` in `InferVar.thy`.

The solvability of a set of constraints is given by `dir_sol_sat` in `InferDef.thy`. Our type inference algorithm is defined by `infer_type` in `InferDef.thy`. The const_scheme function is given together by `const_scheme` and `op_scheme` in `InferDef.thy`.

The proof of Theorem 3 (Inferencing Soundness) is given by `infer_valid_left` in `InferSound.thy`. The proof of Theorem 4 (Inferencing Completeness) is given by `infer_valid_right` in `InferComplete.thy`.

Our constraint solving algorithm is defined by `solve_crn_list` in `SolverP3.thy`, with its soundness and completeness proven by `solve_crn_list_sat` and `solve_crn_list_unsat` respectively, which can also be found in `SolverP3.thy`. 

Constraint solving is split into two steps. The first step is defined by `reduce_crn_list` and removes type variables from the list of constraints. The second step is defined by `full_sol_crn2`, which solves constraints containing only permissions. As noted in our paper, this step could be replaced with SMT solving.

We have defined `full_sol_crn2` because it runs in polynomial time over the number of constraints (we have only proven this result informally, and it may be used in a future work). The correctness of `full_sol_crn2` relies on the predicate `no_mv_crn`, which indicates that the constraint set does not contain any constraints generated from memory location values. In practice, this isn't an issue, since location values can only be typed if the type environment is non-empty (if a program starts execution with memory already allocated).






