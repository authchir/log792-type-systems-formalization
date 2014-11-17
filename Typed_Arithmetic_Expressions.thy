(*<*)
theory Typed_Arithmetic_Expressions
imports Main
begin
(*>*)

chapter {* Typed Arithmetic Expressions *}

datatype_new NBTerm
  = NBTrue
  | NBFalse
  | NBIf NBTerm NBTerm NBTerm
  | NBZero
  | NBSucc NBTerm
  | NBPred NBTerm
  | NBIs_zero NBTerm

section {* Types *}

datatype_new Type
  = Bool
  | Nat

section {* The Typing Relation *}

text {* Definition 8.2.1 *}

inductive has_type :: "NBTerm \<Rightarrow> Type \<Rightarrow> bool" where
  has_type_NBTrue: "has_type NBTrue Bool" |
  has_type_NBFalse: "has_type NBFalse Bool" |
  has_type_NBIf: "has_type t1 Bool \<Longrightarrow> has_type t2 T \<Longrightarrow> has_type t3 T \<Longrightarrow> has_type (NBIf t1 t2 t3) T" |
  has_type_NBZero: "has_type NBZero Nat" |
  has_type_NBSucc: "has_type t Nat \<Longrightarrow> has_type (NBSucc t) Nat" |
  has_type_NBPred: "has_type t Nat \<Longrightarrow> has_type (NBPred t) Nat" |
  has_type_NBIs_zero: "has_type t Nat \<Longrightarrow> has_type (NBIs_zero t) Bool"

text {* Lemma 8.2.2 *}

lemma inversion_of_typing_relation:
  "has_type NBTrue R \<Longrightarrow> R = Bool"
  "has_type NBFalse R \<Longrightarrow> R = Bool"
  "has_type (NBIf t1 t2 t3) R \<Longrightarrow> has_type t1 Bool \<and> has_type t2 R \<and> has_type t3 R"
  "has_type NBZero R \<Longrightarrow> R = Nat"
  "has_type (NBSucc t) R \<Longrightarrow> R = Nat \<and> has_type t Nat"
  "has_type (NBPred t) R \<Longrightarrow> R = Nat \<and> has_type t Nat"
  "has_type (NBIs_zero t) R \<Longrightarrow> R = Bool \<and> has_type t Nat"
  by (auto elim: has_type.cases)

text {* Theorem 8.2.4 *}

theorem has_type_right_unique:
  "has_type t T \<Longrightarrow> has_type t T' \<Longrightarrow> T = T'"
proof (induction t T arbitrary: T' rule: has_type.induct)
  case has_type_NBTrue
  thus ?case by (metis inversion_of_typing_relation(1))
next
  case has_type_NBFalse
  thus ?case by (metis inversion_of_typing_relation(2))
next
  case (has_type_NBIf t1 t2 T t4)
  thus ?case by (metis inversion_of_typing_relation(3))
next
  case has_type_NBZero
  thus ?case by (metis inversion_of_typing_relation(4))
next
  case has_type_NBSucc
  thus ?case by (metis inversion_of_typing_relation(5))
next
  case has_type_NBPred
  thus ?case by (metis inversion_of_typing_relation(6))
next
  case has_type_NBIs_zero
  thus ?case by (metis inversion_of_typing_relation(7))
qed

section {* Safety = Progress + Preservation *}

inductive is_numeric_value :: "NBTerm \<Rightarrow> bool" where
  is_numeric_value_NBZero: "is_numeric_value NBZero" |
  is_numeric_value_NBSucc: "is_numeric_value nv \<Longrightarrow> is_numeric_value (NBSucc nv)"

inductive is_value :: "NBTerm \<Rightarrow> bool" where
  is_value_NBTrue: "is_value NBTrue" |
  is_value_NBFalse: "is_value NBFalse" |
  is_value_numeric_value: "is_numeric_value nv \<Longrightarrow> is_value nv"

text {* Lemma 8.3.1 *}

lemma canonical_form:
  "is_value v \<Longrightarrow> has_type v Bool \<Longrightarrow> v = NBTrue \<or> v = NBFalse"
  "is_value v \<Longrightarrow> has_type v Nat \<Longrightarrow> is_numeric_value v"
  by (auto elim: has_type.cases is_value.cases is_numeric_value.cases)

inductive eval_once :: "NBTerm \<Rightarrow> NBTerm \<Rightarrow> bool" where
  eval_once_NBIf_NBTrue: "eval_once (NBIf NBTrue t2 t3) t2" |
  eval_once_NBIf_NBFalse: "eval_once (NBIf NBFalse t2 t3) t3" |
  eval_once_NBIf: "eval_once t1 t1' \<Longrightarrow> eval_once (NBIf t1 t2 t3) (NBIf t1' t2 t3)" |
  eval_once_NBSucc: "eval_once t1 t1' \<Longrightarrow> eval_once (NBSucc t1) (NBSucc t1')" |
  eval_once_NBPred_NBZero: "eval_once (NBPred NBZero) NBZero" |
  eval_once_NBPred_NBSucc: "is_numeric_value nv1 \<Longrightarrow> eval_once (NBPred (NBSucc nv1)) nv1" |
  eval_once_NBPred: "eval_once t1 t1' \<Longrightarrow> eval_once (NBPred t1) (NBPred t1')" |
  eval_once_NBIs_zero_NBZero: "eval_once (NBIs_zero NBZero) NBTrue" |
  eval_once_NBIs_zero_NBSucc: "is_numeric_value nv1 \<Longrightarrow> eval_once (NBIs_zero (NBSucc nv1)) NBFalse" |
  eval_once_NBIs_zero: "eval_once t1 t1' \<Longrightarrow> eval_once (NBIs_zero t1) (NBIs_zero t1')"

text {* Theorem 8.3.2 *}

theorem progress: "has_type t T \<Longrightarrow> is_value t \<or> (\<exists>t'. eval_once t t')"
proof (induction t T rule: has_type.induct)
  case has_type_NBTrue
  thus ?case by (auto intro: is_value_NBTrue)
next
  case has_type_NBFalse
  thus ?case by (auto intro: is_value_NBFalse)
next
  case (has_type_NBIf t1 t2 T t3)
  have "\<exists>t'. eval_once (NBIf t1 t2 t3) t'"
    proof (cases "is_value t1")
      case True
      thus "\<exists>t'. eval_once (NBIf t1 t2 t3) t'"
        by (auto
          intro: has_type_NBIf.hyps(1) eval_once_NBIf_NBTrue eval_once_NBIf_NBFalse
          dest: canonical_form)
    next
      case False
      thus "\<exists>t'. eval_once (NBIf t1 t2 t3) t'"
        using has_type_NBIf.IH(1)
        by (auto intro: eval_once_NBIf)
    qed
  thus ?case by simp
next
  case has_type_NBZero
  thus ?case  by (auto intro: is_value_numeric_value is_numeric_value_NBZero)
next
  case (has_type_NBSucc t)
  show "?case"
    proof (cases "is_value t")
      case True
      thus "is_value (NBSucc t) \<or> (\<exists>a. eval_once (NBSucc t) a)"
        by (auto
          intro: is_value_numeric_value is_numeric_value_NBSucc
          dest!: canonical_form
          simp: has_type_NBSucc.hyps)
    next
      case False
      thus "is_value (NBSucc t) \<or> (\<exists>a. eval_once (NBSucc t) a)"
        by (metis eval_once_NBSucc has_type_NBSucc.IH)
    qed
next
  case (has_type_NBPred t)
  show ?case
    proof (cases "is_value t")
      case True
      thus "is_value (NBPred t) \<or> (\<exists>a. eval_once (NBPred t) a)"
        by (auto
          intro: eval_once_NBPred_NBZero eval_once_NBPred_NBSucc is_numeric_value.cases
          dest!: canonical_form
          simp: has_type_NBPred.hyps)
    next
      case False
      thus "is_value (NBPred t) \<or> (\<exists>a. eval_once (NBPred t) a)"
        by (metis eval_once_NBPred has_type_NBPred.IH)
    qed
next
  case (has_type_NBIs_zero t)
  show ?case
    proof (cases "is_value t")
      case True
      thus "is_value (NBIs_zero t) \<or> (\<exists>a. eval_once (NBIs_zero t) a)"
        by (auto
          intro: eval_once_NBIs_zero_NBZero eval_once_NBIs_zero_NBSucc is_numeric_value.cases
          dest!: canonical_form
          simp: has_type_NBIs_zero.hyps)
    next
      case False
      thus "is_value (NBIs_zero t) \<or> (\<exists>a. eval_once (NBIs_zero t) a)"
        using has_type_NBIs_zero.IH
        by (auto intro: eval_once_NBIs_zero)
    qed
qed

text {* Theorem 8.3.3 *}

inductive_cases eval_once_NBTrueE: "eval_once NBTrue t"
inductive_cases eval_once_NBFalseE: "eval_once NBFalse t"
inductive_cases eval_once_NBZeroE: "eval_once NBZero t"
inductive_cases eval_once_NBSuccE: "eval_once (NBSucc t) t'"
inductive_cases eval_once_NBPredE: "eval_once (NBPred t) t'"
inductive_cases eval_once_NBIs_zeroE: "eval_once (NBIs_zero t) t'"

theorem preservation: "has_type t T \<Longrightarrow> eval_once t t' \<Longrightarrow> has_type t' T"
proof (induction t T arbitrary: t' rule: has_type.induct)
  case has_type_NBTrue
  thus ?case by (rule eval_once_NBTrueE)
next
  case has_type_NBFalse
  thus ?case by (rule eval_once_NBFalseE)
next
  case (has_type_NBIf t1 t2 T t3)
  from has_type_NBIf.prems has_type_NBIf.IH has_type_NBIf.hyps show ?case
    by (cases rule: eval_once.cases) (auto intro: has_type.has_type_NBIf)
next
  case has_type_NBZero
  thus ?case by (rule eval_once_NBZeroE)
next
  case (has_type_NBSucc t)
  thus ?case by (auto intro: has_type.intros elim: eval_once_NBSuccE)
next
  case (has_type_NBPred t)
  thus ?case
    by (auto intro: has_type.intros dest: inversion_of_typing_relation elim: eval_once_NBPredE)
next
  case (has_type_NBIs_zero t)
  thus ?case by (auto intro: has_type.intros elim: eval_once_NBIs_zeroE)
qed

end
