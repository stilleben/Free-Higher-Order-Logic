theory NgFHOL_pol imports Main
begin 

(* A polymorphic Embedding of Negative Free Higher-Order Logic (NgFHOL) in HOL *)


text \<open> Negative Free Higher-Order Logic \<close>

  typedecl i (* — Type for individuals *)

  consts fExistence :: "'a \<Rightarrow> bool" ("E") (* — Existence/definedness predicate *)

  consts fUndef :: "'a" ("\<^bold>e") (* Distinguished symbol for undefinedness *)
  axiomatization where fUndefIAxiom: "\<not>E (\<^bold>e::i)"
  axiomatization where fFalsehoodBAxiom: "(\<^bold>e::bool) = False"
  axiomatization where fTrueAxiom: "E True"
  axiomatization where fFalseAxiom: "E False"

  (* axiomatization where fNonemptyDomains: "\<exists>x. E x" *)

  definition fIdentity :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<^bold>=" 56) (* — Free identity *)
    where "\<phi> \<^bold>= \<psi> \<equiv> E \<phi> \<and> E \<psi> \<and> (\<phi> = \<psi>)"

  definition fNot :: "bool \<Rightarrow> bool" ("\<^bold>\<not>_" [52]53) (* — Free negation *)
    where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
  definition fOr :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<^bold>\<or>" 51) (* — Free disjunction *)
    where "\<phi> \<^bold>\<or> \<psi> \<equiv> \<phi> \<or> \<psi>" 

  definition fForall :: "('a \<Rightarrow> bool) \<Rightarrow> bool" ("\<^bold>\<forall>") (* — Free universal quantification guarded by predicate E *)
    where "\<^bold>\<forall>\<Phi> \<equiv> \<forall>x. E x \<longrightarrow> \<Phi> x"   
  definition fForallBinder:: "('a \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<^bold>\<forall>" [8]9) (* — Binder notation *)
    where "\<^bold>\<forall>x. \<phi> x \<equiv> \<^bold>\<forall>\<phi>"

  definition fThat :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" ("\<^bold>I") (* — Free definite description guarded by predicate E *)  
    where "\<^bold>I\<Phi> \<equiv> if \<exists>x. E x \<and> \<Phi> x \<and> (\<forall>y. (E y \<and> \<Phi> y) \<longrightarrow> (y = x)) 
                 then THE x. E x \<and> \<Phi> x
                 else \<^bold>e"
  definition fThatBinder:: "('a \<Rightarrow> bool) \<Rightarrow> 'a" (binder "\<^bold>I" [8]9) (* — Binder notation *) 
    where "\<^bold>Ix. \<phi> x \<equiv> \<^bold>I\<phi>"

  definition fPredicate1 :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("\<^sup>n") (* — Free predicate guarded by predicate E *)
    where "\<^sup>nP x \<equiv> E x \<and> P x"
  definition fPredicate2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" ("\<^sup>n\<^sup>n") (* — Free predicate guarded by predicate E *)
    where "\<^sup>n\<^sup>nP x y \<equiv> E x \<and> E y \<and> P x y"

  text \<open> Further logical constants can be defined as usual \<close>

  definition fAnd :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<^bold>\<and>" 52) (* — Free conjunction *)
    where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi> \<^bold>\<or> \<^bold>\<not>\<psi>)"   
  definition fImp :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<^bold>\<rightarrow>" 49) (* — Free implication *)
    where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<^bold>\<not>\<phi> \<^bold>\<or> \<psi>"
  definition fEquiv :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<^bold>\<leftrightarrow>" 50) (* — Free equivalence *)
    where "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> \<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<and> \<psi> \<^bold>\<rightarrow> \<phi>"  

  definition fExists :: "('a \<Rightarrow> bool) \<Rightarrow> bool" ("\<^bold>\<exists>") (* — Free existential quantification *)                                   
    where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y. \<^bold>\<not>(\<Phi> y)))"
  definition fExistsBinder :: "('a \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<^bold>\<exists>" [8]9) (* — Binder notation *)                   
    where "\<^bold>\<exists>x. \<phi> x \<equiv> \<^bold>\<exists>\<phi>"


  (* Introducing "Defs" as the set of the above definitions; useful for convenient unfolding *)
  named_theorems Defs declare fIdentity_def[Defs] fNot_def[Defs] fOr_def[Defs] fForall_def[Defs] 
    fForallBinder_def[Defs] fThat_def[Defs] fPredicate1_def[Defs] fPredicate2_def[Defs]
    fThatBinder_def[Defs] fAnd_def[Defs] fImp_def[Defs] fEquiv_def[Defs] fExists_def[Defs] 
    fExistsBinder_def[Defs]


text \<open> Some Tests \<close>

  lemma "(\<^bold>\<forall>x. \<^sup>nP x) \<^bold>\<rightarrow> \<^sup>nP x" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "((\<^bold>\<forall>x. (\<^sup>nP x)) \<^bold>\<and> (E x)) \<^bold>\<rightarrow> (\<^sup>nP x)"
    by (metis fAnd_def fForallBinder_def fForall_def fImp_def fNot_def fOr_def) (* properly valid *)
                              
  lemma "\<^sup>nP x \<^bold>\<rightarrow> (\<^bold>\<exists>x. \<^sup>nP x)" unfolding Defs by auto (* properly valid *)
  lemma "(x \<^bold>= y) \<^bold>\<rightarrow> (\<^bold>\<exists>x. (x \<^bold>= y))" unfolding Defs by blast (* properly valid *)
  lemma "(x \<^bold>\<or> y) \<^bold>\<rightarrow> (\<^bold>\<exists>x. (x \<^bold>\<or> y))" unfolding Defs using fTrueAxiom by auto (* properly valid *)
  lemma "(\<^sup>nP x) \<^bold>\<and> (\<^bold>\<exists>x. \<^sup>nP x)" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "(\<^sup>nP x) \<^bold>\<rightarrow> (E x)" unfolding Defs by simp (* properly valid *)

  lemma "(\<^sup>nP x) \<^bold>\<or> (\<^bold>\<not>(\<^sup>nP x))" unfolding Defs by auto (* properly valid *)
  lemma "(\<^sup>nP x) \<^bold>\<and> (\<^bold>\<not>(\<^sup>nP x))" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "\<^bold>\<not>((\<^sup>nP x) \<^bold>\<and> (\<^bold>\<not>(\<^sup>nP x)))" unfolding Defs by auto (* properly valid *)


  consts fIndividual1 :: "i" ("i\<^sub>1")
  axiomatization where fUndefIndividual1Axiom: "\<^bold>\<not>(E i\<^sub>1)"

  consts fIndividual2 :: "i" ("i\<^sub>2")
  axiomatization where fUndefIndividual2Axiom: "\<^bold>\<not>(E i\<^sub>2)"

  lemma "x \<^bold>= x" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "i\<^sub>1 \<^bold>= i\<^sub>1" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "\<^bold>\<not>(i\<^sub>1 \<^bold>= i\<^sub>1)" unfolding Defs using fNot_def fUndefIndividual1Axiom by auto (* properly valid *)


  lemma test_True: "True" by simp
  lemma test_False: "False" nitpick [satisfy, user_axioms=true] oops 


text \<open> Prior's Theorem \<close>

  lemma "(Q (\<forall>p. (Q p \<longrightarrow> (\<not>p)))) \<longrightarrow> ((\<exists>p. Q p \<and> p) \<and> (\<exists>p. Q p \<and> (\<not>p)))" by blast

  lemma "(\<^sup>nQ (\<^bold>\<forall>p. (\<^sup>nQ p \<^bold>\<rightarrow> (\<^bold>\<not>p)))) \<^bold>\<rightarrow> ((\<^bold>\<exists>p. \<^sup>nQ p \<^bold>\<and> p) \<^bold>\<and> (\<^bold>\<exists>p. \<^sup>nQ p \<^bold>\<and> (\<^bold>\<not>p)))" unfolding Defs by smt
