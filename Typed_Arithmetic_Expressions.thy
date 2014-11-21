(*<*)
theory Typed_Arithmetic_Expressions
imports Main
  Untyped_Arithmetic_Expressions
begin
(*>*)

chapter {* Typed Arithmetic Expressions *}

text {* In this chapter, we revisit the arithmetic expression language and augment it with static
types.

Here is, as a reminder, the definition of the value predicate introduced in section
\ref{untyped-arith-NBTerm}.
\newline \newline
@{datatype NBTerm} *}

section {* Types *}

text {* The language of arithmetic expressions contains two types: booleans and natural numbers.*}

datatype Type = Bool | Nat

section {* The Typing Relation *}

subsubsection {* Definition 8.2.1 *}

text {* The typing relation is a binary predicate that range over a @{term NBTerm} and
a @{term Type}. It is defined inductively with @{term NBTrue}, @{term NBFalse} and  @{term NBZero}
as base cases and @{term NBIf}, @{term NBSucc}, @{term NBPred} and @{term NBIs_zero} as inductive
cases. *}

inductive has_type :: "NBTerm \<Rightarrow> Type \<Rightarrow> bool" (infix "|:|" 150) where
  has_type_NBTrue: "NBTrue |:| Bool" |
  has_type_NBFalse: "NBFalse |:| Bool" |
  has_type_NBIf: "t1 |:| Bool \<Longrightarrow> t2 |:| T \<Longrightarrow> t3 |:| T \<Longrightarrow> NBIf t1 t2 t3 |:| T" |
  has_type_NBZero: "NBZero |:| Nat" |
  has_type_NBSucc: "t |:| Nat \<Longrightarrow> NBSucc t |:| Nat" |
  has_type_NBPred: "t |:| Nat \<Longrightarrow> NBPred t |:| Nat" |
  has_type_NBIs_zero: "t |:| Nat \<Longrightarrow> NBIs_zero t |:| Bool"

subsubsection {* Lemma 8.2.2 *}

lemma inversion_of_the_typing_relation:
  "NBTrue |:| R \<Longrightarrow> R = Bool"
  "NBFalse |:| R \<Longrightarrow> R = Bool"
  "NBIf t1 t2 t3 |:| R \<Longrightarrow> t1 |:| Bool \<and> t2 |:| R \<and> t3 |:| R"
  "NBZero |:| R \<Longrightarrow> R = Nat"
  "NBSucc t |:| R \<Longrightarrow> R = Nat \<and> t |:| Nat"
  "NBPred t |:| R \<Longrightarrow> R = Nat \<and> t |:| Nat"
  "NBIs_zero t |:| R \<Longrightarrow> R = Bool \<and> t |:| Nat"
  by (auto elim: has_type.cases)

subsubsection {* Theorem 8.2.4 *}

text {* Each term @{term t} has at most one type. That is, if @{term t} is typeable, then its type
is unique. *}

theorem uniqueness_of_types:
  "t |:| T \<Longrightarrow> t |:| T' \<Longrightarrow> T = T'"
by (induction t T rule: has_type.induct) (auto dest: inversion_of_the_typing_relation)

section {* Safety = Progress + Preservation *}

text {* The most basic property a type system must provide is \emph{safety}, also called
\emph{soundness}: the evaluation of a well-typed term will not reach a state whose semantic is
undefined. Since our \emph{operational semantic} is based the of the evaluation relation and the
value predicate. Every term that does not fit in one or the other have no defnied semantic.

Here is, as a reminder, the definition of the value predicate introduced in section
\ref{untyped-arith-is_value}.
\newline \newline
@{thm is_numeric_value_NB.intros[no_vars]}
\newline \newline
@{thm is_value_NB.intros[no_vars]}
*}

subsubsection {* Lemma 8.3.1 *}

text {* We now have assigned types to various terms and defined some of them to be values. Based on
this information, we can restrict the shape a value must have if we know it's type.*}

lemma canonical_form:
  "is_value_NB v \<Longrightarrow> v |:| Bool \<Longrightarrow> v = NBTrue \<or> v = NBFalse"
  "is_value_NB v \<Longrightarrow> v |:| Nat \<Longrightarrow> is_numeric_value_NB v"
  by (auto elim: has_type.cases is_value_NB.cases is_numeric_value_NB.cases)

text {* Here is, as a reminder, the definition of the evaluation relation introduced in section
\ref{untyped-arith-eval_once}.
\newline \newline
@{thm eval_NB.intros[no_vars]}
*}

text {* An example of an undefined state is @{term "NBSucc NBTrue"}: there is no further evaluation
step possible but it is not a value neither. In our current language, there is nothing we can do
with this term.

The safety of a type system can be shown in two step: progress and preservation. *}

subsubsection {* Theorem 8.3.2 *}

text {* A well-typed term is not stuck (either it is a value or it can take a step according to the
evaluation rules). *}

theorem progress: "t |:| T \<Longrightarrow> is_value_NB t \<or> (\<exists>t'. eval_once_NB t t')"
proof (induction t T rule: has_type.induct)
  case (has_type_NBPred t)
  thus ?case by (auto
    intro: eval_once_NB.intros is_numeric_value_NB.cases
    dest: canonical_form)
next
  case (has_type_NBIs_zero t)
  thus ?case by (auto
    intro: eval_once_NB.intros is_numeric_value_NB.cases
    dest: canonical_form)
qed (auto
  intro: eval_once_NB.intros is_value_NB.intros is_numeric_value_NB.intros
  dest: canonical_form)

subsubsection {* Theorem 8.3.3 *}

text {* If a well-typed term takes a step of evaluation, then the resulting term is also
well-typed. *}

theorem preservation: "t |:| T \<Longrightarrow> eval_once_NB t t' \<Longrightarrow> t' |:| T"
proof (induction t T arbitrary: t' rule: has_type.induct)
  case (has_type_NBIf t1 t2 T t3)
  from has_type_NBIf.prems has_type_NBIf.IH has_type_NBIf.hyps show ?case
    by (auto intro: has_type.has_type_NBIf elim: eval_once_NB.cases)
qed (auto
  intro: has_type.intros
  dest: inversion_of_the_typing_relation
  elim: eval_once_NB.cases)

(*>*)
end
(*<*)
