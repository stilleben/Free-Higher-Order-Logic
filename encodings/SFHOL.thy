theory SFHOL imports Main
begin 

(* A nonpolymorphic Embedding of Supervaluational Free Higher-Order Logic (SFHOL) in HOL *)


text \<open> Negative Free Higher-Order Modal Logic \<close>

  (* A nonpolymorphic Embedding of Negative Free Higher-Order Modal Logic (NgFHOML) in HOL *)

  typedecl i (* — Type for individuals *)
  typedecl w (* — Type of possible worlds *) 
  type_synonym \<mu> = "w \<Rightarrow> bool" (* — Type of world depended formulas *) 

  consts fExistenceI :: "i \<Rightarrow> \<mu>" ("E\<^sup>i") (* — Existence/definedness predicate for individuals *)
  consts fExistenceP :: "(i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" ("E\<^sup>p") (* — Existence/definedness predicate for predicates *)

  consts r :: "w \<Rightarrow> w \<Rightarrow> bool" (infixr "r" 53) (* — Accessibility relation between worlds *)

  (* Conditions on the accessibility relation *)
  abbreviation reflexive :: "bool"
    where "reflexive \<equiv> \<forall>x. x r x"
  abbreviation transitive :: "bool"
    where "transitive \<equiv> \<forall>x y z. (x r y) \<and> (y r z) \<longrightarrow> (x r z)"
  abbreviation mcKinseysAxiom :: "bool"
    where "mcKinseysAxiom \<equiv> \<forall>x. \<exists>y. (x r y) \<and> (\<forall>z. (y r z) \<longrightarrow> y = z)"
  axiomatization where S41: 
    "reflexive \<and> transitive \<and> mcKinseysAxiom"

  axiomatization where nestedDomains: (* — Nested domains property: If some object exists at a world w, then it also exists in all from w reachable worlds *) 
    "\<forall>x y. x r y \<longrightarrow> (\<forall>z. E\<^sup>i z x \<longrightarrow> E\<^sup>i z y)"
  (* axiomatization where Ax2: "\<exists>x. \<forall>y. x r y" *) (* — There exists a world from which every world is reachable *)
  (* axiomatization where Ax3: "\<forall>x y. x r y \<longrightarrow> (\<forall>z. ((E\<^sup>i z x) \<and> (P z x)) \<longrightarrow> (P z y))" *) (* — If some existent object in a world w has property P, this object has the same property in all from w reachable worlds *)

  definition fmIdentity :: "i \<Rightarrow> i \<Rightarrow> \<mu>" (infixr "\<^bold>=\<^sub>f\<^sub>m" 56) (* — Free modal identity *)
    where "\<phi> \<^bold>=\<^sub>f\<^sub>m \<psi> \<equiv> \<lambda>w. \<phi> = \<psi>"

  definition fmNot :: "\<mu> \<Rightarrow> \<mu>" ("\<^bold>\<not>\<^sub>f\<^sub>m_" [52]53) (* — Free modal negation *)
    where "\<^bold>\<not>\<^sub>f\<^sub>m\<phi> \<equiv> \<lambda>w. \<not>(\<phi> w)"
  definition fmOr :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu>" (infixr "\<^bold>\<or>\<^sub>f\<^sub>m" 51) (* — Free modal disjunction *)
    where "\<phi> \<^bold>\<or>\<^sub>f\<^sub>m \<psi> \<equiv> \<lambda>w. \<phi> w \<or> \<psi> w" 

  definition fmBox :: "\<mu> \<Rightarrow> \<mu>" ("\<^bold>\<box>_" [52]53) (* — Free modal necessity *)
    where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w. \<forall>v. w r v \<longrightarrow> \<phi> v"

  definition fmForallI :: "(i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" ("\<^bold>\<forall>\<^sup>i\<^sub>f\<^sub>m") (* — Free modal universal quantification over individuals guarded by predicate E *)
    where "\<^bold>\<forall>\<^sup>i\<^sub>f\<^sub>m\<Phi> \<equiv> \<lambda>w. \<forall>x. E\<^sup>i x w \<longrightarrow> \<Phi> x w"
  definition fmForallIBinder:: "(i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" (binder "\<^bold>\<forall>\<^sup>i\<^sub>f\<^sub>m" [8]9) (* — Binder notation *)
    where "\<^bold>\<forall>\<^sup>i\<^sub>f\<^sub>mx. \<phi> x \<equiv> \<^bold>\<forall>\<^sup>i\<^sub>f\<^sub>m\<phi>"   
  definition fmForallP :: "((i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" ("\<^bold>\<forall>\<^sup>p\<^sub>f\<^sub>m") (* — Free modal universal quantification over predicates guarded by predicate E *)
    where "\<^bold>\<forall>\<^sup>p\<^sub>f\<^sub>m\<Phi> \<equiv> \<lambda>w. \<forall>x. E\<^sup>p x w \<longrightarrow> \<Phi> x w"
  definition fmForallPBinder:: "((i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" (binder "\<^bold>\<forall>\<^sup>p\<^sub>f\<^sub>m" [8]9) (* — Binder notation *)
    where "\<^bold>\<forall>\<^sup>p\<^sub>f\<^sub>mx. \<phi> x \<equiv> \<^bold>\<forall>\<^sup>p\<^sub>f\<^sub>m\<phi>"

  definition fmPredicateI :: "(i \<Rightarrow> \<mu>) \<Rightarrow> i \<Rightarrow> \<mu>" ("\<^sup>f\<^sup>m") (* — Free modal predicate guarded by predicate E *)
     where "\<^sup>f\<^sup>mP x \<equiv>  \<lambda>w. E\<^sup>i x w \<and> P x w"

  definition fmValid :: "\<mu> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>f\<^sub>m" [7]8) (* — Validity of lifted free modal formulas *)
    where "\<lfloor>\<phi>\<rfloor>\<^sub>f\<^sub>m \<equiv> \<forall>w. \<phi> w"

  text \<open> Further logical constants can be defined as usual \<close>

  definition fmAnd :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu>" (infixr "\<^bold>\<and>\<^sub>f\<^sub>m" 52) (* — Free modal conjunction *)
    where "\<phi> \<^bold>\<and>\<^sub>f\<^sub>m \<psi> \<equiv> \<^bold>\<not>\<^sub>f\<^sub>m(\<^bold>\<not>\<^sub>f\<^sub>m\<phi> \<^bold>\<or>\<^sub>f\<^sub>m \<^bold>\<not>\<^sub>f\<^sub>m\<psi>)"   
  definition fmImp :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu>" (infixr "\<^bold>\<rightarrow>\<^sub>f\<^sub>m" 49) (* — Free modal implication *)
    where "\<phi> \<^bold>\<rightarrow>\<^sub>f\<^sub>m \<psi> \<equiv> \<^bold>\<not>\<^sub>f\<^sub>m\<phi> \<^bold>\<or>\<^sub>f\<^sub>m \<psi>"
  definition fmEquiv :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu>" (infixr "\<^bold>\<leftrightarrow>\<^sub>f\<^sub>m" 50) (* — Free modal equivalence *)
    where "\<phi> \<^bold>\<leftrightarrow>\<^sub>f\<^sub>m \<psi> \<equiv> \<phi> \<^bold>\<rightarrow>\<^sub>f\<^sub>m \<psi> \<^bold>\<and>\<^sub>f\<^sub>m \<psi> \<^bold>\<rightarrow>\<^sub>f\<^sub>m \<phi>"  

  definition fmDia :: "\<mu> \<Rightarrow> \<mu>" ("\<^bold>\<diamond>_" [52]53) (* — Free modal possibility *)
    where "\<^bold>\<diamond>\<phi> \<equiv> \<^bold>\<not>\<^sub>f\<^sub>m(\<^bold>\<box>(\<^bold>\<not>\<^sub>f\<^sub>m\<phi>))"

  definition fmExistsI :: "(i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" ("\<^bold>\<exists>\<^sup>i\<^sub>f\<^sub>m") (* — Free modal existential quantification over individuals *)                                 
    where "\<^bold>\<exists>\<^sup>i\<^sub>f\<^sub>m\<Phi> \<equiv> \<^bold>\<not>\<^sub>f\<^sub>m(\<^bold>\<forall>\<^sup>i\<^sub>f\<^sub>m(\<lambda>y. \<^bold>\<not>\<^sub>f\<^sub>m(\<Phi> y)))"
  definition fmExistsIBinder :: "(i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" (binder "\<^bold>\<exists>\<^sup>i\<^sub>f\<^sub>m" [8]9) (* — Binder notation *)                   
    where "\<^bold>\<exists>\<^sup>i\<^sub>f\<^sub>mx. \<phi> x \<equiv> \<^bold>\<exists>\<^sup>i\<^sub>f\<^sub>m\<phi>"
  definition fmExistsP :: "((i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" ("\<^bold>\<exists>\<^sup>p\<^sub>f\<^sub>m") (* — Free modal existential quantification over predicates *)                                 
    where "\<^bold>\<exists>\<^sup>p\<^sub>f\<^sub>m\<Phi> \<equiv> \<^bold>\<not>\<^sub>f\<^sub>m(\<^bold>\<forall>\<^sup>p\<^sub>f\<^sub>m(\<lambda>y. \<^bold>\<not>\<^sub>f\<^sub>m(\<Phi> y)))"
  definition fmExistsPBinder :: "((i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" (binder "\<^bold>\<exists>\<^sup>p\<^sub>f\<^sub>m" [8]9) (* — Binder notation *)                   
    where "\<^bold>\<exists>\<^sup>p\<^sub>f\<^sub>mx. \<phi> x \<equiv> \<^bold>\<exists>\<^sup>p\<^sub>f\<^sub>m\<phi>"


  (* Introducing "Defs" as the set of the above definitions; useful for convenient unfolding *)
  named_theorems Defs declare fmIdentity_def[Defs] fmNot_def[Defs] fmOr_def[Defs] 
    fmForallI_def[Defs] fmForallIBinder_def[Defs] fmForallP_def[Defs] fmForallPBinder_def[Defs] 
    fmPredicateI_def[Defs] fmBox_def[Defs] fmAnd_def[Defs] fmImp_def[Defs] fmEquiv_def[Defs] 
    fmExistsI_def[Defs] fmExistsIBinder_def[Defs] fmExistsP_def[Defs] fmExistsPBinder_def[Defs] 
    fmDia_def[Defs] fmValid_def[Defs]


text \<open> Some Tests \<close>

  lemma Kf: "\<lfloor>(\<^bold>\<box>((\<^sup>f\<^sup>m\<phi> x) \<^bold>\<rightarrow>\<^sub>f\<^sub>m (\<^sup>f\<^sup>m\<psi> x))) \<^bold>\<rightarrow>\<^sub>f\<^sub>m ((\<^bold>\<box>(\<^sup>f\<^sup>m\<phi> x)) \<^bold>\<rightarrow>\<^sub>f\<^sub>m (\<^bold>\<box>(\<^sup>f\<^sup>m\<psi> x)))\<rfloor>\<^sub>f\<^sub>m" unfolding Defs by blast (* — Verifying K principle *)
  lemma NECf: "\<lfloor>\<^sup>f\<^sup>m\<phi> x\<rfloor>\<^sub>f\<^sub>m \<Longrightarrow> \<lfloor>\<^bold>\<box>(\<^sup>f\<^sup>m\<phi> x)\<rfloor>\<^sub>f\<^sub>m" unfolding Defs by blast (* — Verifying necessitation rule *)


  lemma "\<lfloor>(\<^bold>\<forall>\<^sup>i\<^sub>f\<^sub>mx. \<^sup>f\<^sup>mP x) \<^bold>\<rightarrow>\<^sub>f\<^sub>m (\<^sup>f\<^sup>mP x)\<rfloor>\<^sub>f\<^sub>m" nitpick [user_axioms=true, show_all, format=2, card w=3] oops (* properly invalid *)
  lemma "\<lfloor>((\<^bold>\<forall>\<^sup>i\<^sub>f\<^sub>mx. (\<^sup>f\<^sup>mP x)) \<^bold>\<and>\<^sub>f\<^sub>m (E\<^sup>i x)) \<^bold>\<rightarrow>\<^sub>f\<^sub>m (\<^sup>f\<^sup>mP x)\<rfloor>\<^sub>f\<^sub>m" unfolding Defs by blast (* properly valid *)

  lemma "\<lfloor>(\<^sup>f\<^sup>mP x) \<^bold>\<rightarrow>\<^sub>f\<^sub>m (\<^bold>\<exists>\<^sup>i\<^sub>f\<^sub>mx. \<^sup>f\<^sup>mP x)\<rfloor>\<^sub>f\<^sub>m" unfolding Defs by blast (* properly valid *)
  lemma "\<lfloor>(\<^sup>f\<^sup>mP x) \<^bold>\<rightarrow>\<^sub>f\<^sub>m (E\<^sup>i x)\<rfloor>\<^sub>f\<^sub>m" unfolding Defs by blast (* properly valid *)
  lemma "\<lfloor>(\<^sup>f\<^sup>mP x) \<^bold>\<and>\<^sub>f\<^sub>m (\<^bold>\<exists>\<^sup>i\<^sub>f\<^sub>mx. \<^sup>f\<^sup>mP x)\<rfloor>\<^sub>f\<^sub>m" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)

  lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>\<^sup>i\<^sub>f\<^sub>mx. E\<^sup>i x)\<rfloor>\<^sub>f\<^sub>m" unfolding Defs by simp (* properly valid *)
  lemma "\<lfloor>\<^bold>\<box>(E\<^sup>i x)\<rfloor>\<^sub>f\<^sub>m" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "\<lfloor>\<^bold>\<forall>\<^sup>i\<^sub>f\<^sub>mx. \<^bold>\<box>(E\<^sup>i x)\<rfloor>\<^sub>f\<^sub>m" unfolding Defs using nestedDomains by blast (* properly valid *)
  lemma "\<lfloor>(\<^bold>\<box>(\<^bold>\<forall>\<^sup>i\<^sub>f\<^sub>mx. \<^sup>f\<^sup>mP x)) \<^bold>\<leftrightarrow>\<^sub>f\<^sub>m (\<^bold>\<forall>\<^sup>i\<^sub>f\<^sub>mx. \<^bold>\<box>(\<^sup>f\<^sup>mP x))\<rfloor>\<^sub>f\<^sub>m" unfolding Defs by blast (* properly valid *)

  lemma "\<lfloor>(a \<^bold>=\<^sub>f\<^sub>m b) \<^bold>\<rightarrow>\<^sub>f\<^sub>m (\<^bold>\<box>(a \<^bold>=\<^sub>f\<^sub>m b))\<rfloor>\<^sub>f\<^sub>m" unfolding Defs by simp (* properly valid *)


text \<open> Supervaluational Free Higher-Order Logic \<close>

  definition sIdentity :: "i \<Rightarrow> i \<Rightarrow> \<mu>" (infixr "\<^bold>=\<^sub>s" 56) (* — Supervaluational free identity *)
    where "\<phi> \<^bold>=\<^sub>s \<psi> \<equiv> \<phi> \<^bold>=\<^sub>f\<^sub>m \<psi>"

  definition sNot :: "\<mu> \<Rightarrow> \<mu>" ("\<^bold>\<not>\<^sub>s_" [52]53) (* — Supervaluational free negation *)
    where "\<^bold>\<not>\<^sub>s\<phi> \<equiv> \<^bold>\<not>\<^sub>f\<^sub>m\<phi>" 
  definition sOr :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu>" (infixr "\<^bold>\<or>\<^sub>s" 51) (* — Supervaluational free disjunction *)
    where "\<phi> \<^bold>\<or>\<^sub>s \<psi> \<equiv> \<phi> \<^bold>\<or>\<^sub>f\<^sub>m \<psi>"

  definition sForallI :: "(i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" ("\<^bold>\<forall>\<^sup>i\<^sub>s") (* — Supervaluational free universal quantification over individuals *)
    where "\<^bold>\<forall>\<^sup>i\<^sub>s\<Phi> \<equiv> \<^bold>\<forall>\<^sup>i\<^sub>f\<^sub>mx. \<Phi> x"
  definition sForallIBinder:: "(i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" (binder "\<^bold>\<forall>\<^sup>i\<^sub>s" [8]9) (* — Binder notation *)
    where "\<^bold>\<forall>\<^sup>i\<^sub>sx. \<phi> x \<equiv> \<^bold>\<forall>\<^sup>i\<^sub>s\<phi>"   
  definition sForallP :: "((i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" ("\<^bold>\<forall>\<^sup>p\<^sub>s") (* — Supervaluational free universal quantification over predicates *)
    where "\<^bold>\<forall>\<^sup>p\<^sub>s\<Phi> \<equiv> \<^bold>\<forall>\<^sup>p\<^sub>f\<^sub>mx. \<Phi> x"
  definition sForallPBinder:: "((i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" (binder "\<^bold>\<forall>\<^sup>p\<^sub>s" [8]9) (* — Binder notation *)
    where "\<^bold>\<forall>\<^sup>p\<^sub>sx. \<phi> x \<equiv> \<^bold>\<forall>\<^sup>p\<^sub>s\<phi>"

  definition sPredicateI :: "(i \<Rightarrow> \<mu>) \<Rightarrow> i \<Rightarrow> \<mu>" ("\<^sup>s") (* — Supervaluational free predicate *)
    where "\<^sup>sP x \<equiv> (E\<^sup>i x \<^bold>\<rightarrow>\<^sub>f\<^sub>m (\<^sup>f\<^sup>mP x)) \<^bold>\<and>\<^sub>f\<^sub>m (\<^bold>\<not>\<^sub>f\<^sub>m(E\<^sup>i x) \<^bold>\<rightarrow>\<^sub>f\<^sub>m (\<^bold>\<box>(\<^bold>\<diamond>(\<^sup>f\<^sup>mP x))))"

  text \<open> Further logical constants can be defined as usual \<close>

  definition sAnd :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu>" (infixr "\<^bold>\<and>\<^sub>s" 52) (* — Supervaluational free conjunction *)
    where "\<phi> \<^bold>\<and>\<^sub>s \<psi> \<equiv> \<^bold>\<not>\<^sub>s(\<^bold>\<not>\<^sub>s\<phi> \<^bold>\<or>\<^sub>s \<^bold>\<not>\<^sub>s\<psi>)"   
  definition sImp :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu>" (infixr "\<^bold>\<rightarrow>\<^sub>s" 49) (* — Supervaluational free implication *)
    where "\<phi> \<^bold>\<rightarrow>\<^sub>s \<psi> \<equiv> \<^bold>\<not>\<^sub>s\<phi> \<^bold>\<or>\<^sub>s \<psi>"
  definition sEquiv :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu>" (infixr "\<^bold>\<leftrightarrow>\<^sub>s" 50) (* — Supervaluational free equivalence *)
    where "\<phi> \<^bold>\<leftrightarrow>\<^sub>s \<psi> \<equiv> \<phi> \<^bold>\<rightarrow>\<^sub>s \<psi> \<^bold>\<and>\<^sub>s \<psi> \<^bold>\<rightarrow>\<^sub>s \<phi>"  

  definition sExistsI :: "(i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" ("\<^bold>\<exists>\<^sup>i\<^sub>s") (* — Supervaluational free existential quantification over individuals *)                                   
    where "\<^bold>\<exists>\<^sup>i\<^sub>s\<Phi> \<equiv> \<^bold>\<not>\<^sub>s(\<^bold>\<forall>\<^sup>i\<^sub>s(\<lambda>y. \<^bold>\<not>\<^sub>s(\<Phi> y)))"
  definition sExistsIBinder :: "(i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" (binder "\<^bold>\<exists>\<^sup>i\<^sub>s" [8]9) (* — Binder notation *)                   
    where "\<^bold>\<exists>\<^sup>i\<^sub>sx. \<phi> x \<equiv> \<^bold>\<exists>\<^sup>i\<^sub>s\<phi>"
  definition sExistsP :: "((i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" ("\<^bold>\<exists>\<^sup>p\<^sub>s") (* — Supervaluational free existential quantification over predicates *)                                   
    where "\<^bold>\<exists>\<^sup>p\<^sub>s\<Phi> \<equiv> \<^bold>\<not>\<^sub>s(\<^bold>\<forall>\<^sup>p\<^sub>s(\<lambda>y. \<^bold>\<not>\<^sub>s(\<Phi> y)))"
  definition sExistsPBinder :: "((i \<Rightarrow> \<mu>) \<Rightarrow> \<mu>) \<Rightarrow> \<mu>" (binder "\<^bold>\<exists>\<^sup>p\<^sub>s" [8]9) (* — Binder notation *)                   
    where "\<^bold>\<exists>\<^sup>p\<^sub>sx. \<phi> x \<equiv> \<^bold>\<exists>\<^sup>p\<^sub>s\<phi>"

  definition sValid :: "\<mu> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>s" [7]8) (* — Validity of supervaluational free formulas *)
    where "\<lfloor>\<phi>\<rfloor>\<^sub>s \<equiv> \<forall>w. \<phi> w"


  declare sIdentity_def[Defs] sNot_def[Defs] sOr_def[Defs] sForallI_def[Defs] 
    sForallIBinder_def[Defs] sForallP_def[Defs] sForallPBinder_def[Defs] sPredicateI_def[Defs] 
    sAnd_def[Defs] sImp_def[Defs] sEquiv_def[Defs] sExistsI_def[Defs] sExistsIBinder_def[Defs] 
    sExistsP_def[Defs] sExistsPBinder_def[Defs] sValid_def[Defs]


text \<open> Some Tests \<close>

  lemma "\<lfloor>(\<^bold>\<forall>\<^sup>i\<^sub>sx. \<^sup>sP x) \<^bold>\<rightarrow>\<^sub>s (\<^sup>sP x)\<rfloor>\<^sub>s" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "\<lfloor>((\<^bold>\<forall>\<^sup>i\<^sub>sx. (\<^sup>sP x)) \<^bold>\<and>\<^sub>s (E\<^sup>i x)) \<^bold>\<rightarrow>\<^sub>s (\<^sup>sP x)\<rfloor>\<^sub>s" unfolding Defs by blast (* properly valid *)

  lemma "\<lfloor>(\<^sup>sP x) \<^bold>\<rightarrow>\<^sub>s (\<^bold>\<exists>\<^sup>i\<^sub>sx. \<^sup>sP x)\<rfloor>\<^sub>s" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "\<lfloor>((\<^sup>sP x) \<^bold>\<and>\<^sub>s (E\<^sup>i x)) \<^bold>\<rightarrow>\<^sub>s (\<^bold>\<exists>\<^sup>i\<^sub>sx. \<^sup>sP x)\<rfloor>\<^sub>s" unfolding Defs by blast (* properly valid *)
  lemma "\<lfloor>(\<^sup>sP x) \<^bold>\<rightarrow>\<^sub>s (E\<^sup>i x)\<rfloor>\<^sub>s" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "\<lfloor>(\<^sup>sP x) \<^bold>\<and>\<^sub>s (\<^bold>\<exists>\<^sup>i\<^sub>sx. \<^sup>sP x)\<rfloor>\<^sub>s" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)

  lemma "\<lfloor>(\<^sup>sP x) \<^bold>\<or>\<^sub>s (\<^bold>\<not>\<^sub>s(\<^sup>sP x))\<rfloor>\<^sub>s" unfolding Defs by blast (* properly valid *)
  lemma "\<lfloor>(\<^sup>sP x) \<^bold>\<and>\<^sub>s (\<^bold>\<not>\<^sub>s(\<^sup>sP x))\<rfloor>\<^sub>s" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "\<lfloor>\<^bold>\<not>\<^sub>s((\<^sup>sP x) \<^bold>\<and>\<^sub>s (\<^bold>\<not>\<^sub>s(\<^sup>sP x)))\<rfloor>\<^sub>s" unfolding Defs by blast (* properly valid *)

  lemma "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>\<^sup>i\<^sub>sx. E\<^sup>i x)\<rfloor>\<^sub>s" unfolding Defs by simp (* properly valid *)
  lemma "\<lfloor>\<^bold>\<box>(E\<^sup>i x)\<rfloor>\<^sub>s" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "\<lfloor>\<^bold>\<forall>\<^sup>i\<^sub>sx. \<^bold>\<box>(E\<^sup>i x)\<rfloor>\<^sub>s" unfolding Defs by (simp add: nestedDomains) (* properly valid *)
  lemma "\<lfloor>(\<^bold>\<box>(\<^bold>\<forall>\<^sup>i\<^sub>sx. \<^sup>sP x)) \<^bold>\<leftrightarrow>\<^sub>s (\<^bold>\<forall>\<^sup>i\<^sub>sx. \<^bold>\<box>(\<^sup>sP x))\<rfloor>\<^sub>s" unfolding Defs by blast (* properly valid *)

  lemma "\<lfloor>(a \<^bold>=\<^sub>s b) \<^bold>\<rightarrow>\<^sub>s (\<^bold>\<box>(a \<^bold>=\<^sub>s b))\<rfloor>\<^sub>s" unfolding Defs by simp (* properly valid *)


  consts sIndividual1 :: "i" ("i\<^sub>1")
  axiomatization where sUndefIndividual1Axiom: "\<exists>w. \<not>(E\<^sup>i i\<^sub>1 w)"

  lemma "\<lfloor>x \<^bold>=\<^sub>s x\<rfloor>\<^sub>s" unfolding Defs by simp (* properly valid *)
  lemma "\<lfloor>i\<^sub>1 \<^bold>=\<^sub>s i\<^sub>1\<rfloor>\<^sub>s" unfolding Defs by simp (* properly valid *)

  lemma "\<lfloor>\<^sup>sP i\<^sub>1\<rfloor>\<^sub>s" nitpick [user_axioms=true, show_all, format=2] nitpick [satisfy, user_axioms=true, show_all, format=2, card w=2] oops (* should be truth-valueless *)
  lemma "\<lfloor>\<^bold>\<not>\<^sub>s(\<^sup>sP i\<^sub>1)\<rfloor>\<^sub>s" nitpick [user_axioms=true, show_all, format=2] nitpick [satisfy, user_axioms=true, show_all, format=2] oops (* should be truth-valueless *)
  lemma "(\<lfloor>(\<^sup>sP i\<^sub>1) \<^bold>\<or>\<^sub>s (\<^bold>\<not>\<^sub>s(\<^sup>sP i\<^sub>1))\<rfloor>\<^sub>s)" unfolding Defs nitpick [satisfy, user_axioms=true, show_all, format=2] by blast (* properly valid *)
  lemma "(\<lfloor>(\<^sup>sP i\<^sub>1) \<^bold>\<or>\<^sub>s (\<^bold>\<not>\<^sub>s(\<^sup>sP i\<^sub>1))\<rfloor>\<^sub>s)" unfolding Defs nitpick [satisfy, user_axioms=true, show_all, format=2, card i=1, card w=2] by blast (* properly valid *)
  lemma "\<lfloor>\<^bold>\<exists>\<^sup>p\<^sub>sP. \<^sup>sP i\<^sub>1\<rfloor>\<^sub>s" nitpick [user_axioms=true, show_all, format=2] oops (* properly invalid *)
  lemma "\<lfloor>\<^bold>\<not>\<^sub>s(\<^bold>\<exists>\<^sup>p\<^sub>sP. \<^sup>sP i\<^sub>1)\<rfloor>\<^sub>s" nitpick [user_axioms=true, show_all, format=2] nitpick [satisfy, user_axioms=true, show_all, format=2, card=2] oops (* properly invalid *)


  lemma test_True: "True" by simp
  lemma test_False: "False" nitpick [satisfy, user_axioms=true] oops
