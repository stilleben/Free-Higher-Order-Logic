theory NgFHOL_nonpol imports Main
begin 

(* A nonpolymorphic Embedding of Negative Free Higher-Order Logic (NgFHOL) in HOL *)

text \<open> Negative Free Higher-Order Logic \<close>

  typedecl i (* — Type for individuals *)

  consts fExistenceI :: "i \<Rightarrow> bool" ("E\<^sup>i") (* — Existence/definedness predicate for individuals *)
  consts fExistenceP :: "(i \<Rightarrow> bool) \<Rightarrow> bool" ("E\<^sup>p") (* — Existence/definedness predicate for predicates *)

  consts fUndefI :: "i" ("\<^bold>e\<^sup>i") (* Distinguished symbol for undefinedness amongst the individuals *)
  axiomatization where fUndefIAxiom: "\<not>E\<^sup>i \<^bold>e\<^sup>i"

  consts fFalsehoodB :: "bool" ("\<^bold>e\<^sup>b") (* Distinguished error value among the booleans *)
  axiomatization where fFalsehoodBAxiom: "\<^bold>e\<^sup>b = False"

  (*
  axiomatization where fNonemptyDomainI: "\<exists>x. E\<^sup>i x"
  axiomatization where fNonemptyDomainP: "\<exists>x. E\<^sup>p x"
  *)

  definition fIdentityI :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "\<^bold>=" 56) (* — Free identity *)
    where "\<phi> \<^bold>= \<psi> \<equiv> E\<^sup>i \<phi> \<and> E\<^sup>i \<psi> \<and> (\<phi> = \<psi>)"

  definition fNot :: "bool \<Rightarrow> bool" ("\<^bold>\<not>_" [52]53) (* — Free negation *)
    where "\<^bold>\<not>\<phi> \<equiv> \<not>\<phi>"     
  definition fOr :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<^bold>\<or>" 51) (* — Free disjunction *)
    where "\<phi> \<^bold>\<or> \<psi> \<equiv> \<phi> \<or> \<psi>" 

  definition fForallI :: "(i \<Rightarrow> bool) \<Rightarrow> bool" ("\<^bold>\<forall>\<^sup>i") (* — Free universal quantification over individuals guarded by predicate E *)
    where "\<^bold>\<forall>\<^sup>i\<Phi> \<equiv> \<forall>x. E\<^sup>i x \<longrightarrow> \<Phi> x"   
  definition fForallIBinder:: "(i \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<^bold>\<forall>\<^sup>i" [8]9) (* — Binder notation *)
    where "\<^bold>\<forall>\<^sup>ix. \<phi> x \<equiv> \<^bold>\<forall>\<^sup>i\<phi>"
  definition fForallP :: "((i \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> bool" ("\<^bold>\<forall>\<^sup>p") (* — Free universal quantification over predicates guarded by predicate E *)
    where "\<^bold>\<forall>\<^sup>p\<Phi> \<equiv> \<forall>x. E\<^sup>p x \<longrightarrow> \<Phi> x"   
  definition fForallPBinder:: "((i \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<^bold>\<forall>\<^sup>p" [8]9) (* — Binder notation *)
    where "\<^bold>\<forall>\<^sup>px. \<phi> x \<equiv> \<^bold>\<forall>\<^sup>p\<phi>"

  definition fThatI :: "(i \<Rightarrow> bool) \<Rightarrow> i" ("\<^bold>I") (* — Free definite description for individuals guarded by predicate E *)  
    where "\<^bold>I\<Phi> \<equiv> if \<exists>x. E\<^sup>i x \<and> \<Phi> x \<and> (\<forall>y. (E\<^sup>i y \<and> \<Phi> y) \<longrightarrow> (y = x)) 
                 then THE x. E\<^sup>i x \<and> \<Phi> x
                 else \<^bold>e\<^sup>i"
  definition fThatIBinder:: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<^bold>I" [8]9) (* — Binder notation *) 
    where "\<^bold>Ix. \<phi> x \<equiv> \<^bold>I\<phi>"

  definition fPredicateI1 :: "(i \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> bool" ("\<^sup>i") (* — Free predicate taking an individual guarded by predicate E *)
    where "\<^sup>iP x \<equiv> E\<^sup>i x \<and> P x"
  definition fPredicateI2 :: "(i \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool" ("\<^sup>i\<^sup>i") (* — Free predicate taking two individuals guarded by predicate E *)
    where "\<^sup>i\<^sup>iP x y \<equiv> E\<^sup>i x \<and> E\<^sup>i y \<and> P x y"

  text \<open> Further logical constants can be defined as usual \<close>

  definition fAnd :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<^bold>\<and>" 52) (* — Free conjunction *)
    where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi> \<^bold>\<or> \<^bold>\<not>\<psi>)"   
  definition fImp :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<^bold>\<rightarrow>" 49) (* — Free implication *)
    where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<^bold>\<not>\<phi> \<^bold>\<or> \<psi>"
  definition fEquiv :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<^bold>\<leftrightarrow>" 50) (* — Free equivalence *)
    where "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> \<phi> \<^bold>\<rightarrow> \<psi> \<^bold>\<and> \<psi> \<^bold>\<rightarrow> \<phi>"  

  definition fExistsI :: "(i \<Rightarrow> bool) \<Rightarrow> bool" ("\<^bold>\<exists>\<^sup>i") (* — Free existential quantification over individuals *)                                   
    where "\<^bold>\<exists>\<^sup>i\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>\<^sup>i(\<lambda>y. \<^bold>\<not>(\<Phi> y)))"
  definition fExistsIBinder :: "(i \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<^bold>\<exists>\<^sup>i" [8]9) (* — Binder notation *)                   
    where "\<^bold>\<exists>\<^sup>ix. \<phi> x \<equiv> \<^bold>\<exists>\<^sup>i\<phi>"
  definition fExistsP :: "((i \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> bool" ("\<^bold>\<exists>\<^sup>p") (* — Free existential quantification over predicates *)
    where "\<^bold>\<exists>\<^sup>p\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>\<^sup>p(\<lambda>y. \<^bold>\<not>(\<Phi> y)))"
  definition fExistsPBinder :: "((i \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<^bold>\<exists>\<^sup>p" [8]9) (* — Binder notation *)
    where "\<^bold>\<exists>\<^sup>px. \<phi> x \<equiv> \<^bold>\<exists>\<^sup>p\<phi>" 


  (* Introducing "Defs" as the set of the above definitions; useful for convenient unfolding *)
  named_theorems Defs declare fIdentityI_def[Defs] fNot_def[Defs] fOr_def[Defs] fForallI_def[Defs] 
    fForallIBinder_def[Defs] fForallP_def[Defs] fForallPBinder_def[Defs] fThatI_def[Defs] 
    fPredicateI1_def[Defs] fPredicateI2_def[Defs] fThatIBinder_def[Defs] fAnd_def[Defs] 
    fImp_def[Defs] fEquiv_def[Defs] fExistsI_def[Defs] fExistsIBinder_def[Defs] fExistsP_def[Defs] 
    fExistsPBinder_def[Defs]


text \<open> Some Tests \<close>

  lemma "(\<^bold>\<forall>\<^sup>ix. \<^sup>iP x) \<^bold>\<rightarrow>  \<^sup>iP x" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "((\<^bold>\<forall>\<^sup>ix. (\<^sup>iP x)) \<^bold>\<and> (E\<^sup>i x)) \<^bold>\<rightarrow> (\<^sup>iP x)" unfolding Defs by auto (* properly valid *)

  lemma "\<^sup>iP x \<^bold>\<rightarrow> (\<^bold>\<exists>\<^sup>ix. \<^sup>iP x)" unfolding Defs by auto (* properly valid *)
  lemma "(x \<^bold>= x) \<^bold>\<rightarrow> (\<^bold>\<exists>\<^sup>ix. (x \<^bold>= x))" unfolding Defs by auto (* properly valid *)
  lemma "(x \<^bold>= y) \<^bold>\<rightarrow> (\<^bold>\<exists>\<^sup>ix. (x \<^bold>= y))" unfolding Defs by auto (* properly valid *)
  lemma "(\<^sup>iP x) \<^bold>\<and> (\<^bold>\<exists>\<^sup>ix. \<^sup>iP x)" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "(\<^sup>iP x) \<^bold>\<rightarrow> (E\<^sup>i x)" unfolding Defs by simp (* properly valid *)

  lemma "(\<^sup>iP x) \<^bold>\<or> (\<^bold>\<not>(\<^sup>iP x))" unfolding Defs by auto (* properly valid *)
  lemma "(\<^sup>iP x) \<^bold>\<and> (\<^bold>\<not>(\<^sup>iP x))" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "\<^bold>\<not>((\<^sup>iP x) \<^bold>\<and> (\<^bold>\<not>(\<^sup>iP x)))" unfolding Defs by auto (* properly valid *)


  consts fIndividual1 :: "i" ("i\<^sub>1")
  axiomatization where fUndefIndividual1Axiom: "\<^bold>\<not>(E\<^sup>i i\<^sub>1)"

  consts fIndividual2 :: "i" ("i\<^sub>2")
  axiomatization where fUndefIndividual2Axiom: "\<^bold>\<not>(E\<^sup>i i\<^sub>2)"

  lemma "x \<^bold>= x" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "i\<^sub>1 \<^bold>= i\<^sub>1" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "\<^bold>\<not>(i\<^sub>1 \<^bold>= i\<^sub>1)" unfolding Defs using fNot_def fUndefIndividual1Axiom by auto (* properly valid *)

  lemma "(\<^sup>iP i\<^sub>1)" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "\<^bold>\<not>(\<^sup>iP i\<^sub>1)" unfolding Defs using fNot_def fUndefIndividual1Axiom by auto


  lemma test_True: "True" by simp
  lemma test_False: "False" nitpick [satisfy, user_axioms=true] oops 


text \<open> Prior's Theorem \<close>

  lemma "(Q (\<forall>p. (Q p \<longrightarrow> (\<not>p)))) \<longrightarrow> ((\<exists>p. Q p \<and> p) \<and> (\<exists>p. Q p \<and> (\<not>p)))" by blast


  consts fExistenceB :: "bool \<Rightarrow> bool" ("E\<^sup>b") (* — Existence/definedness predicate for booleans *)

  axiomatization where fTrueAxiom: "E\<^sup>b True"
  axiomatization where fFalseAxiom: "E\<^sup>b False"

  definition fForallB :: "(bool \<Rightarrow> bool) \<Rightarrow> bool" ("\<^bold>\<forall>\<^sup>b") (* — Free universal quantification over booleans guarded by predicate E *)
    where "\<^bold>\<forall>\<^sup>b\<Phi> \<equiv> \<forall>x. E\<^sup>b x \<longrightarrow> \<Phi> x"   
  definition fForallBBinder:: "(bool \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<^bold>\<forall>\<^sup>b" [8]9) (* — Binder notation *)
    where "\<^bold>\<forall>\<^sup>bx. \<phi> x \<equiv> \<^bold>\<forall>\<^sup>b\<phi>"

  definition fExistsB :: "(bool \<Rightarrow> bool) \<Rightarrow> bool" ("\<^bold>\<exists>\<^sup>b") (* — Free existential quantification over booleans *)                                   
    where "\<^bold>\<exists>\<^sup>b\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>\<^sup>b(\<lambda>y. \<^bold>\<not>(\<Phi> y)))"
  definition fExistsBBinder :: "(bool \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<^bold>\<exists>\<^sup>b" [8]9) (* — Binder notation *)                   
    where "\<^bold>\<exists>\<^sup>bx. \<phi> x \<equiv> \<^bold>\<exists>\<^sup>b\<phi>"

  definition fPredicateB1 :: "(bool \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> bool" ("\<^sup>b") (* — Free predicate taking a boolean guarded by predicate E *)
    where "\<^sup>bP x \<equiv> E\<^sup>b x \<and> P x"


  lemma "(\<^sup>bQ (\<^bold>\<forall>\<^sup>bp. (\<^sup>bQ p \<^bold>\<rightarrow> (\<^bold>\<not>p)))) \<^bold>\<rightarrow> ((\<^bold>\<exists>\<^sup>bp. \<^sup>bQ p \<^bold>\<and> p) \<^bold>\<and> (\<^bold>\<exists>\<^sup>bp. \<^sup>bQ p \<^bold>\<and> (\<^bold>\<not>p)))" 
    unfolding Defs
    by (smt fPredicateB1_def fExistsBBinder_def fExistsB_def fForallBBinder_def fForallB_def fNot_def)
