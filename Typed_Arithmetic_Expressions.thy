(*<*)
theory Typed_Arithmetic_Expressions
imports Main
begin
(*>*)

chapter {* Typed Arithmetic Expressions *}

datatype NBTerm =
  NBTrue
| NBFalse
| NBIf NBTerm NBTerm NBTerm
| NBZero
| NBSucc NBTerm
| NBPred NBTerm
| NBIs_zero NBTerm

section {* Types *}

text {* The language of arithmetic expressions contains two types of expressions: booleans and
natural numbers.*}

datatype Type = Bool | Nat

section {* The Typing Relation *}

text {* Definition 8.2.1 *}

inductive has_type :: "NBTerm \<Rightarrow> Type \<Rightarrow> bool" (infix "|:|" 150) where
  has_type_NBTrue: "NBTrue |:| Bool" |
  has_type_NBFalse: "NBFalse |:| Bool" |
  has_type_NBIf: "t1 |:| Bool \<Longrightarrow> t2 |:| T \<Longrightarrow> t3 |:| T \<Longrightarrow> NBIf t1 t2 t3 |:| T" |
  has_type_NBZero: "NBZero |:| Nat" |
  has_type_NBSucc: "t |:| Nat \<Longrightarrow> NBSucc t |:| Nat" |
  has_type_NBPred: "t |:| Nat \<Longrightarrow> NBPred t |:| Nat" |
  has_type_NBIs_zero: "t |:| Nat \<Longrightarrow> NBIs_zero t |:| Bool"

text {* Lemma 8.2.2 *}

lemma inversion_of_typing_relation:
  "NBTrue |:| R \<Longrightarrow> R = Bool"
  "NBFalse |:| R \<Longrightarrow> R = Bool"
  "NBIf t1 t2 t3 |:| R \<Longrightarrow> t1 |:| Bool \<and> t2 |:| R \<and> t3 |:| R"
  "NBZero |:| R \<Longrightarrow> R = Nat"
  "NBSucc t |:| R \<Longrightarrow> R = Nat \<and> t |:| Nat"
  "NBPred t |:| R \<Longrightarrow> R = Nat \<and> t |:| Nat"
  "NBIs_zero t |:| R \<Longrightarrow> R = Bool \<and> t |:| Nat"
  by (auto elim: has_type.cases)

text {* Theorem 8.2.4 *}

theorem has_type_right_unique:
  "t |:| T \<Longrightarrow> t |:| T' \<Longrightarrow> T = T'"
by (induction t T rule: has_type.induct) (auto dest: inversion_of_typing_relation)

section {* Safety = Progress + Preservation *}

inductive is_numeric_value :: "NBTerm \<Rightarrow> bool" where
  "is_numeric_value NBZero" |
  "is_numeric_value nv \<Longrightarrow> is_numeric_value (NBSucc nv)"

inductive is_value :: "NBTerm \<Rightarrow> bool" where
  "is_value NBTrue" |
  "is_value NBFalse" |
  "is_numeric_value nv \<Longrightarrow> is_value nv"

text {* Lemma 8.3.1 *}

lemma canonical_form:
  "is_value v \<Longrightarrow> v |:| Bool \<Longrightarrow> v = NBTrue \<or> v = NBFalse"
  "is_value v \<Longrightarrow> v |:| Nat \<Longrightarrow> is_numeric_value v"
  by (auto elim: has_type.cases is_value.cases is_numeric_value.cases)

inductive eval_once :: "NBTerm \<Rightarrow> NBTerm \<Rightarrow> bool" where
  "eval_once (NBIf NBTrue t2 t3) t2" |
  "eval_once (NBIf NBFalse t2 t3) t3" |
  "eval_once t1 t1' \<Longrightarrow> eval_once (NBIf t1 t2 t3) (NBIf t1' t2 t3)" |
  "eval_once t1 t1' \<Longrightarrow> eval_once (NBSucc t1) (NBSucc t1')" |
  "eval_once (NBPred NBZero) NBZero" |
  "is_numeric_value nv1 \<Longrightarrow> eval_once (NBPred (NBSucc nv1)) nv1" |
  "eval_once t1 t1' \<Longrightarrow> eval_once (NBPred t1) (NBPred t1')" |
  "eval_once (NBIs_zero NBZero) NBTrue" |
  "is_numeric_value nv1 \<Longrightarrow> eval_once (NBIs_zero (NBSucc nv1)) NBFalse" |
  "eval_once t1 t1' \<Longrightarrow> eval_once (NBIs_zero t1) (NBIs_zero t1')"

text {* Theorem 8.3.2 *}

theorem progress: "t |:| T \<Longrightarrow> is_value t \<or> (\<exists>t'. eval_once t t')"
proof (induction t T rule: has_type.induct)
  case has_type_NBTrue
  thus ?case by (auto intro: is_value.intros)
next
  case has_type_NBFalse
  thus ?case by (auto intro: is_value.intros)
next
  case (has_type_NBIf t1 t2 T t3)
  thus ?case by (cases "is_value t1") (auto intro: eval_once.intros dest: canonical_form)
next
  case has_type_NBZero
  thus ?case  by (auto intro: is_value.intros is_numeric_value.intros)
next
  case (has_type_NBSucc t)
  thus ?case by (cases "is_value t")
    (auto intro: eval_once.intros is_value.intros is_numeric_value.intros dest: canonical_form)
next
  case (has_type_NBPred t)
  thus ?case by (cases "is_value t")
    (auto intro: eval_once.intros is_numeric_value.cases dest: canonical_form)
next
  case (has_type_NBIs_zero t)
  thus ?case by (cases "is_value t")
    (auto intro: eval_once.intros is_numeric_value.cases dest: canonical_form)
qed

text {* Theorem 8.3.3 *}

theorem preservation: "t |:| T \<Longrightarrow> eval_once t t' \<Longrightarrow> t' |:| T"
proof (induction t T arbitrary: t' rule: has_type.induct)
  case (has_type_NBIf t1 t2 T t3)
  from has_type_NBIf.prems has_type_NBIf.IH has_type_NBIf.hyps show ?case
    by (auto intro: has_type.has_type_NBIf elim: eval_once.cases)
qed (auto intro: has_type.intros dest: inversion_of_typing_relation elim: eval_once.cases)

end
