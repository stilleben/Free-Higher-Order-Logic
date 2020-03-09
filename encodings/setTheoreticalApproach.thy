theory setTheoreticalApproach imports Main
begin 

(* An Embedding of Free Higher-Order Modal Logic (FHOML) in HOL *)


text \<open> Free Higher Order Modal  Logic \<close>

  typedecl w (* — Type of possible worlds *)
  type_synonym wSet = "w \<Rightarrow> bool"  (* — Type of the set containing worlds *)
  type_synonym wSetSet = "(w \<Rightarrow> bool) \<Rightarrow> bool"  (* — Type of the set containing sets of worlds *)

  text \<open> Set relevant Definitions \<close>

  definition wSetMember :: "w \<Rightarrow> wSet \<Rightarrow> bool" (infixr "\<^bold>\<in>\<^sub>{\<^sub>}" 53) 
    where "x \<^bold>\<in>\<^sub>{\<^sub>} S \<equiv> S x"
  definition wSetSetMember :: "wSet \<Rightarrow> wSetSet \<Rightarrow> bool" (infixr "\<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>}" 53) 
    where "x \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} S \<equiv> S x"

  definition wSetUnion :: "wSet \<Rightarrow> wSet \<Rightarrow> wSet" (infixr "\<^bold>\<union>" 50) 
    where "A \<^bold>\<union> B \<equiv> \<lambda>x. A x \<or> B x"
  definition wSetOther :: "wSet \<Rightarrow> wSet \<Rightarrow> wSet" (infixr "\<^bold>-" 50) 
    where "A \<^bold>- B \<equiv> \<lambda>x. A x \<and> \<not>(B x)"
  definition wSetSubsetEq :: "wSet \<Rightarrow> wSet \<Rightarrow> bool" (infixr "\<^bold>\<subseteq>" 50) 
    where "A \<^bold>\<subseteq> B \<equiv> \<forall>x. A x \<longrightarrow> B x"

  consts W :: "wSet"
  axiomatization where defW: "\<forall>x. x \<^bold>\<in>\<^sub>{\<^sub>} W"

  consts emptySet :: "wSet" ("\<^bold>{\<^bold>}")
  axiomatization where defEmptySet: "\<forall>x. \<not>(x \<^bold>\<in>\<^sub>{\<^sub>} \<^bold>{\<^bold>})"

  consts emptySetSet :: "wSetSet" ("\<^bold>{\<^bold>{\<^bold>}\<^bold>}")
  axiomatization where defEmptySetSet: "\<forall>x. \<not>(x \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} \<^bold>{\<^bold>{\<^bold>}\<^bold>})"

  text \<open> Free Modal Logic relevant Definitions \<close>

  consts r :: "w \<Rightarrow> w \<Rightarrow> bool" (infixr "r" 53) (* — Accessibility relation between worlds *)

  (* Conditions on the accessibility relation *)
  abbreviation reflexive :: "bool"
    where "reflexive \<equiv> \<forall>x. x r x"
  abbreviation symmetric :: "bool"
    where "symmetric \<equiv> \<forall>x y. x r y \<longrightarrow> y r x"
  abbreviation transitive :: "bool"
    where "transitive \<equiv> \<forall>x y z. (x r y) \<and> (y r z) \<longrightarrow> (x r z)"
  abbreviation universal :: "bool"
    where "universal \<equiv> \<forall>x y. x r y"

  axiomatization where S5: 
    "reflexive \<and> symmetric \<and> transitive \<and> universal"

  abbreviation R :: "w \<Rightarrow> wSet" ("\<^bold>R_"[52]53) 
    where "\<^bold>R w \<equiv> \<lambda>x. w r x"

  consts fmExistenceDomains :: "w \<Rightarrow> wSetSet" ("D") (* — Existence domains *)

  definition fmTop :: "wSet" ("\<^bold>\<top>") 
    where "\<^bold>\<top> \<equiv> W" 
  definition fmBot :: "wSet" ("\<^bold>\<bottom>") 
    where "\<^bold>\<bottom> \<equiv> \<^bold>{\<^bold>}" 

  definition fmIdentity :: "wSet \<Rightarrow> wSet \<Rightarrow> wSet" (infixr "\<^bold>=" 56) (* — Free modal identity *)
    where "\<phi> \<^bold>= \<psi> \<equiv> if (\<phi> = \<psi>) then W else \<^bold>{\<^bold>}"
  
  definition fmNot :: "wSet \<Rightarrow> wSet" ("\<^bold>\<not>_" [52]53) (* — Free modal negation *)
    where "\<^bold>\<not>\<phi> \<equiv> W \<^bold>- \<phi>"
  definition fmOr :: "wSet \<Rightarrow> wSet \<Rightarrow> wSet" (infixr "\<^bold>\<or>" 51) (* — Free modal disjunction *)
    where "\<phi> \<^bold>\<or> \<psi> \<equiv> \<phi> \<^bold>\<union> \<psi>"

  definition fmBox :: "wSet \<Rightarrow> wSet" ("\<^bold>\<box>_" [52]53) (* — Free modal necessity *)
    where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w. (\<^bold>R w) \<^bold>\<subseteq> \<phi>"

  consts Qex :: "w \<Rightarrow> wSetSet" ("\<^bold>|\<^bold>Q\<^bold>|")
  definition Qin :: "wSet \<Rightarrow> wSet" ("\<^bold>Q") 
    where "\<^bold>Q\<phi> \<equiv> \<lambda>w. \<phi> \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} \<^bold>|\<^bold>Q\<^bold>|(w)" 

  definition fmForall :: "(wSet \<Rightarrow> wSet) \<Rightarrow> wSet" ("\<^bold>\<forall>") (* — Free modal universal quantification *)
    where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w. \<forall>x. x \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} (D w) \<longrightarrow> w \<^bold>\<in>\<^sub>{\<^sub>} (\<Phi> x)"
  definition fmForallB:: "(wSet \<Rightarrow> wSet) \<Rightarrow> wSet" (binder "\<^bold>\<forall>" [8]9) (* — Binder notation *)
    where "\<^bold>\<forall>x. \<phi> x \<equiv> \<^bold>\<forall>\<phi>"

  definition fmValid :: "wSet \<Rightarrow> bool" ("\<lfloor>_\<rfloor>" [7]8) (* — Validity of free modal formulas *)
    where "\<lfloor>\<phi>\<rfloor> \<equiv> \<phi> = W"

  text \<open> Further logical constants can be defined as usual \<close>

  definition fmAnd :: "wSet \<Rightarrow> wSet \<Rightarrow> wSet" (infixr "\<^bold>\<and>" 52) (* — Free modal conjunction *)
    where "\<phi> \<^bold>\<and> \<psi> \<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi> \<^bold>\<or> \<^bold>\<not>\<psi>)"
  definition fmImp :: "wSet \<Rightarrow> wSet \<Rightarrow> wSet" (infixr "\<^bold>\<rightarrow>" 49) (* — Free modal implication *)
    where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> \<^bold>\<not>\<phi> \<^bold>\<or> \<psi>" 
  definition fmEquiv :: "wSet \<Rightarrow> wSet \<Rightarrow> wSet" (infixr "\<^bold>\<leftrightarrow>" 50) (* — Free modal equivalence *)
    where "\<phi> \<^bold>\<leftrightarrow> \<psi> \<equiv> (\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<and> (\<psi> \<^bold>\<rightarrow> \<phi>)" 

  definition fmDia :: "wSet \<Rightarrow> wSet" ("\<^bold>\<diamond>_" [52]53) (* — Free modal possibility *)
    where "\<^bold>\<diamond>\<phi> \<equiv> \<^bold>\<not>(\<^bold>\<box>\<^bold>\<not>\<phi>)"

  definition fmExists :: "(wSet \<Rightarrow> wSet) \<Rightarrow> wSet" ("\<^bold>\<exists>") (* — Free modal existential quantification *)
    where "\<^bold>\<exists>\<Phi> \<equiv> \<^bold>\<not>(\<^bold>\<forall>(\<lambda>y. \<^bold>\<not>(\<Phi> y)))"
  definition fmExistsB:: "(wSet \<Rightarrow> wSet) \<Rightarrow> wSet" (binder "\<^bold>\<exists>" [8]9) (* — Binder notation *)
    where "\<^bold>\<exists>x. \<phi> x \<equiv> \<^bold>\<exists>\<phi>"


  (* Introducing "Defs" as the set of the above definitions; useful for convenient unfolding *)  
  named_theorems Defs declare defW[Defs] defEmptySet[Defs] defEmptySetSet[Defs] 
    wSetMember_def[Defs] wSetMember_def[Defs] wSetOther_def[Defs] wSetUnion_def[Defs] 
    wSetSubsetEq_def[Defs] fmTop_def[Defs] fmBot_def[Defs] fmIdentity_def[Defs] fmNot_def[Defs] 
    fmOr_def[Defs] fmBox_def[Defs] Qin_def[Defs] fmForall_def[Defs] fmForallB_def[Defs] 
    fmAnd_def[Defs] fmImp_def[Defs] fmEquiv_def[Defs] fmExists_def[Defs] fmExistsB_def[Defs] 
    fmDia_def[Defs] fmValid_def[Defs]


text \<open> Some Tests \<close>

  lemma "\<lfloor>(\<^bold>\<forall>x. P) \<^bold>\<rightarrow> A\<rfloor>" unfolding Defs nitpick [user_axioms=true, show_all, format=2] oops 
  lemma "\<lfloor>(\<^bold>\<forall>x. A x) \<^bold>\<rightarrow> A x\<rfloor>" unfolding Defs nitpick [user_axioms=true, show_all, format=2] oops 

  lemma "\<lfloor>A \<^bold>\<rightarrow> (\<^bold>\<exists>x. P)\<rfloor>" unfolding Defs nitpick [user_axioms=true, show_all, format=2] oops 
  lemma "\<lfloor>A x \<^bold>\<rightarrow> (\<^bold>\<exists>x. A x)\<rfloor>" unfolding Defs nitpick [user_axioms=true, show_all, format=2] oops 


text \<open> Prior's Theorem \<close>

  text \<open> Proposition 4.1.: Finite countermodel with constant, possibly empty existence domains \<close>

  (*
  axiomatization where Ax1: "\<forall>x. (D x) = \<^bold>{\<^bold>{\<^bold>}\<^bold>}"
  axiomatization where Ax2: "\<exists>x. W \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} \<^bold>|\<^bold>Q\<^bold>|(x) \<and> \<^bold>{\<^bold>} \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} \<^bold>|\<^bold>Q\<^bold>|(x)"
  *)

  lemma "\<lfloor>(\<^bold>Q (\<^bold>\<forall>p. (\<^bold>Q p \<^bold>\<rightarrow> \<^bold>\<not>p))) \<^bold>\<rightarrow> ((\<^bold>\<exists>p. \<^bold>Q p \<^bold>\<and> p) \<^bold>\<and> (\<^bold>\<exists>p. \<^bold>Q p \<^bold>\<and> \<^bold>\<not>p))\<rfloor>" 
    unfolding Defs 
    nitpick [user_axioms=true, format=2, show_all]
    oops  
 
  text \<open> Proposition 4.2.: Finite countermodel with constant, nonempty existence domains \<close>

  axiomatization where fmNonemptyExistenceDomains: "\<forall>w. (D w) \<noteq> \<^bold>{\<^bold>{\<^bold>}\<^bold>}"

  axiomatization where Ax1: "\<forall>x y. (D x) = (D y)"
  axiomatization where Ax2: "\<forall>x. W \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} (D x) \<and> \<^bold>{\<^bold>} \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} (D x)"
  axiomatization where Ax3: "\<forall>x y. (y \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} (D x)) \<longrightarrow> ((y = \<^bold>{\<^bold>}) \<or> (y = W))"
  axiomatization where Ax4: "\<exists>x. W \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} \<^bold>|\<^bold>Q\<^bold>|(x) \<and> (\<forall>y. y \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} \<^bold>|\<^bold>Q\<^bold>|(x) \<longrightarrow> y = W)"
  axiomatization where Ax5: "\<exists>x. \<^bold>{\<^bold>} \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} \<^bold>|\<^bold>Q\<^bold>|(x) \<and> (\<forall>y. y \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} \<^bold>|\<^bold>Q\<^bold>|(x) \<longrightarrow> y = \<^bold>{\<^bold>})"
  axiomatization where Ax6: "\<exists>x. \<forall>y. ((y \<noteq> \<^bold>{\<^bold>}) \<and> (y \<noteq> W)) \<longrightarrow> (y \<^bold>\<in>\<^sub>{\<^sub>{\<^sub>}\<^sub>} \<^bold>|\<^bold>Q\<^bold>|(x))"

  lemma "\<lfloor>(\<^bold>Q (\<^bold>\<forall>p. (\<^bold>Q p \<^bold>\<rightarrow> \<^bold>\<not>p))) \<^bold>\<rightarrow> ((\<^bold>\<exists>p. \<^bold>Q p \<^bold>\<and> p) \<^bold>\<and> (\<^bold>\<exists>p. \<^bold>Q p \<^bold>\<and> \<^bold>\<not>p))\<rfloor>" 
    unfolding Defs 
    nitpick [user_axioms=true, format=2, show_all, card=3]
    oops 
