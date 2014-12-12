(*<*)
theory Typed_Arithmetic_Expressions
imports Main
  Untyped_Arithmetic_Expressions
begin
(*>*)

section {* Typed Arithmetic Expressions *}
text {* \label{sec:typed-arith-expr} *}

text {* In this section, we revisit the previously formalized arithmetic expression language
(Section \ref{sec:untyped-arith-expr}) and augment it with static types. Since types are a
characterization external to the definition of terms, we import the theory to reuse its definitions
and theorems. We complete the definitions with the typing relation and prove type safety through the
progress and preservation theorems.
*}

subsection {* Definitions *}

text {*
The language of arithmetic expressions contains two types for booleans and natural numbers, which we
model using a datatype:
*}

datatype nbtype = Bool | Nat

(* Definition 8.2.1 *)

text {*
The typing relation serves to assign a type to an expression. We express it with an inductive
definition for which we also provide the @{text "|:|"} operator as a more conventional notation:
*}

inductive has_type :: "nbterm \<Rightarrow> nbtype \<Rightarrow> bool" (infix "|:|" 150) where
  has_type_NBTrue:
    "NBTrue |:| Bool" |
  has_type_NBFalse:
    "NBFalse |:| Bool" |
  has_type_NBIf:
    "t1 |:| Bool \<Longrightarrow> t2 |:| T \<Longrightarrow> t3 |:| T \<Longrightarrow> NBIf t1 t2 t3 |:| T" |
  has_type_NBZero:
    "NBZero |:| Nat" |
  has_type_NBSucc:
    "t |:| Nat \<Longrightarrow> NBSucc t |:| Nat" |
  has_type_NBPred:
    "t |:| Nat \<Longrightarrow> NBPred t |:| Nat" |
  has_type_NBIs_zero:
    "t |:| Nat \<Longrightarrow> NBIs_zero t |:| Bool"

(* Lemma 8.2.2 *)

text {*
The inversion of the typing relation gives us information on types for specific terms:
*}

lemma inversion_of_typing_relation:
  "NBTrue |:| R \<Longrightarrow> R = Bool"
  "NBFalse |:| R \<Longrightarrow> R = Bool"
  "NBIf t1 t2 t3 |:| R \<Longrightarrow> t1 |:| Bool \<and> t2 |:| R \<and> t3 |:| R"
  "NBZero |:| R \<Longrightarrow> R = Nat"
  "NBSucc t |:| R \<Longrightarrow> R = Nat \<and> t |:| Nat"
  "NBPred t |:| R \<Longrightarrow> R = Nat \<and> t |:| Nat"
  "NBIs_zero t |:| R \<Longrightarrow> R = Bool \<and> t |:| Nat"
by (auto elim: has_type.cases)

(* Theorem 8.2.4 *)

text {*
In the typed arithmetic language, every term @{term t} has at most one type. That is, if @{term t}
is typable, then its type is unique:
*}

theorem uniqueness_of_types:
  "t |:| T \<Longrightarrow> t |:| T' \<Longrightarrow> T = T'"
by (induction t T rule: has_type.induct) (auto dest: inversion_of_typing_relation)

subsection {* Safety = Progress + Preservation *}

text {*
The most basic property a type system must provide is \emph{safety}, also called \emph{soundness}:
the evaluation of a well-typed term will not reach a state whose semantic is undefined. Since our
\emph{operational semantic} is based the of the evaluation relation and the value predicate, every
term that does not fit in one or the other have no defined semantic.

An example of an undefined state is @{term "NBSucc NBTrue"}: there is no further evaluation
step possible but it is not a value neither. In our current language, there is nothing we can do
with this term.
*}

(* Lemma 8.3.1 *)

text {*
An other usefull lemma is the canonical form of values which, for well typed terms, give us
information on the nature of the terms:
*}

lemma canonical_form:
  "is_value_NB v \<Longrightarrow> v |:| Bool \<Longrightarrow> v = NBTrue \<or> v = NBFalse"
  "is_value_NB v \<Longrightarrow> v |:| Nat \<Longrightarrow> is_numeric_value_NB v"
by (auto elim: has_type.cases is_value_NB.cases is_numeric_value_NB.cases)

(* Theorem 8.3.2 *)

text {*
The safety of a type system can be shown in two step: progress and preservation. Progress means that
a well-typed term is not stuck, i.e. either it is a value or it can take a step according to the
evaluation rules.
*}

theorem progress: "t |:| T \<Longrightarrow> is_value_NB t \<or> (\<exists>t'. eval1_NB t t')"
proof (induction t T rule: has_type.induct)
  case (has_type_NBPred t)
  thus ?case
    by (auto intro: eval1_NB.intros is_numeric_value_NB.cases dest: canonical_form)
next
  case (has_type_NBIs_zero t)
  thus ?case
    by (auto intro: eval1_NB.intros is_numeric_value_NB.cases dest: canonical_form)
qed (auto
  intro: eval1_NB.intros is_value_NB.intros is_numeric_value_NB.intros
  dest: canonical_form)

(* Theorem 8.3.3 *)

text {*
Preservation means that if a well-typed term takes a step of evaluation, then the resulting term is
also well-typed.
*}

theorem preservation: "t |:| T \<Longrightarrow> eval1_NB t t' \<Longrightarrow> t' |:| T"
proof (induction t T arbitrary: t' rule: has_type.induct)
  case (has_type_NBIf t1 t2 T t3)
  from has_type_NBIf.prems has_type_NBIf.IH has_type_NBIf.hyps show ?case
    by (auto intro: has_type.intros elim: eval1_NB.cases)
qed (auto
  intro: has_type.intros
  dest: inversion_of_typing_relation
  elim: eval1_NB.cases)

(*<*)
end
(*>*)
