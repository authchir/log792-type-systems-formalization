(*<*)
theory Untyped_Arithmetic_Expressions
imports Main
begin
(*>*)

section {* Untyped Arithmetic Expressions *}

text {*
The untyped arithmetic expressions language is the first one we formalize. It consists of boolean
expressions, containing the constants \texttt{true} and \texttt{false} and conditionals as
primitives, and natural numbers, containing the constant \texttt{zero}, the successor and
predecessor functions and an operation to test equality with zero as primitives. Following the book,
we start with a subset containing only the boolean expression and carry on with fully fledged
arithmetic expressions.
*}

subsection {* Booleans *}

text {*
The syntax of this language is defined, in the book, in the following way:

\begin{verbatim}
  t ::=
    true                        constant true
    false                       constant false
    if t then t else t          conditional
\end{verbatim}

Its counterpart, using Isabelle/HOL's syntax, is the \texttt{bterm} datatype: \footnote{To prevent
name clashes with Isabelle's predefined types and constants of the same name, our types and type
constructors are prefixed with \texttt{b}, which stand for "booleans". Functions use a suffix for
the same purpose.}
*}

datatype bterm =
  BTrue |
  BFalse |
  BIf bterm bterm bterm

text {*
The semantics of the language is defined using the small-step operational semantics which consists
of an evaluation relation that performs the smallest possible step toward the final value. For the
booleans, the only values are the constants @{term BTrue} and @{term BFalse}. To describe those,
the book uses the following notation:

\begin{verbatim}
  v ::=
    true           true value
    false          false value
\end{verbatim}

We translate this in Isabelle/HOL using an inductive definition:
*}

inductive is_value_B :: "bterm \<Rightarrow> bool" where
  "is_value_B BTrue" |
  "is_value_B BFalse"

text {*
The evaluation relation is concerned with the way a conditional expression will be reduced. The book
uses the standard mathematical notation for inference rules:

\begin{verbatim}
if true then t2 else t3 --> t2

if false then t2 else t3 --> t3

                  t1 --> t1'
------------------------------------------------
if t1 then t2 else t3 --> if t1' then t2 else t3
\end{verbatim}

These rules translate easily into an other inductive definition:
*}

inductive eval1_B :: "bterm \<Rightarrow> bterm \<Rightarrow> bool" where
  eval1_BIf_BTrue: "eval1_B (BIf BTrue t2 t3) t2" |
  eval1_BIf_BFalse: "eval1_B (BIf BFalse t2 t3) t3" |
  eval1_BIf: "eval1_B t1 t1' \<Longrightarrow> eval1_B (BIf t1 t2 t3) (BIf t1' t2 t3)"

(*<*)
(* Example of definition 3.5.3 *)

lemma
  assumes
    s: "s = BIf BTrue BFalse BFalse" and
    t: "t = BIf s BTrue BTrue" and
    u: "u = BIf BFalse BTrue BTrue"
  shows "eval1_B (BIf t BFalse BFalse) (BIf u BFalse BFalse)"
proof -
  have "eval1_B s BFalse" unfolding s by (rule eval1_BIf_BTrue)
  hence "eval1_B t u" unfolding t u by (rule eval1_BIf)
  thus ?thesis by (rule eval1_BIf)
qed
(*>*)

(* subsubsection {* Theorem 3.5.4 *} *)

text {*
With those basic definitions, we can turn to the first interesting theorem: the determinacy of
one-step evaluation. As in the book, it goes by induction over the evaluation of @{term t} to
@{term t'}, followed by a case analysis:
*}

theorem eval_single_determinacy:
  "eval1_B t t' \<Longrightarrow> eval1_B t t'' \<Longrightarrow> t' = t''"
proof (induction t t' arbitrary: t'' rule: eval1_B.induct)
  case (eval1_BIf_BTrue t1 t2)
  thus ?case by (auto elim: eval1_B.cases)
next
  case (eval1_BIf_BFalse t1 t2)
  thus ?case by (auto elim: eval1_B.cases)
next
  case (eval1_BIf t1 t1' t2 t3)
  from eval1_BIf.prems eval1_BIf.hyps show ?case
    by (auto dest: eval1_BIf.IH elim: eval1_B.cases)
qed

(* subsubsection {* Theorem 3.5.7 *} *)

text {*
We now formalize the concept of normal form, for which the book gives the following definition:

\begin{quotation}
  \noindent A term \texttt{t} is in \emph{normal form} if no evaluation rule applies to it --- i.e.,
  if there is no \texttt{t'} such that \texttt{t $\to$ t'}.
\end{quotation}

Since this definition mainly introduce some standard terminologie for some property of terms with
respect to the single-step evaluation relation, we translate it using a simple synonym definition:
*}

definition is_normal_form_B :: "bterm \<Rightarrow> bool" where
  "is_normal_form_B t \<longleftrightarrow> (\<forall>t'. \<not> eval1_B t t')"

text {*
We follows by proving, using a simple case analysis, that every value is in normal form:
*}

theorem value_imp_normal_form:
  "is_value_B t \<Longrightarrow> is_normal_form_B t"
by (auto elim: is_value_B.cases eval1_B.cases simp: is_normal_form_B_def)

(* subsubsection {* Theorem 3.5.8 *} *)

text {*
For this simple language, the converse is also true: every term in normal form is a value. Our proof
follows the book and use contradiction, structural induction over @{term t} and case analysis over
the possible values.
*}

theorem normal_form_imp_value:
  "is_normal_form_B t \<Longrightarrow> is_value_B t"
by (rule ccontr, induction t rule: bterm.induct)
  (auto intro: eval1_B.intros is_value_B.intros elim: is_value_B.cases simp: is_normal_form_B_def)

(* subsubsection {* Definition 3.5.9 *} *)

text {*
The one-step evaluation is a very useful representation of the semantic of a language, but it does
not represent what really interests us: the final value of an evaluation. To this end, the book
defines a multi-step evaluation relation based on the single-step one:

\begin{quotation}
  \noindent The \emph{multi-step evaluation} relation $\to^*$ is the reflexive, transitive closure
  of one-step evaluation. That is, it is the smallest relation such that (1) if t $t \to t'$ then
  $t \to^* t'$, (2) $t \to^* t$ for all $t$, and (3) if $t \to^* t'$ and $t' \to^* t''$, then
  $t \to^* t''$.
\end{quotation}

A direct translation of this definition would lead to the following definition:
*}

inductive eval_direct :: "bterm \<Rightarrow> bterm \<Rightarrow> bool" where
  e_once: "eval1_B t t' \<Longrightarrow> eval_direct t t'" |
  e_self: "eval_direct t t" |
  e_transitive: "eval_direct t t' \<Longrightarrow> eval_direct t' t'' \<Longrightarrow> eval_direct t t''"

text {*
But this definition is inconvenient for theorem proving because it requires to consider three cases
for each induction on a evaluation relation. We chose to define the multi-step evaluation relation
using a shape similar to a list of one-step evaluations. The inductive definition consists of a base
case, the reflexive application, and of an inductive case where one step of evaluation is perfomed:
*}

inductive eval_B :: "bterm \<Rightarrow> bterm \<Rightarrow> bool" where
  e_base: "eval_B t t" |
  e_step: "eval1_B t t' \<Longrightarrow> eval_B t' t'' \<Longrightarrow> eval_B t t''"

text {*
We then prove that this reprentation is equivalent to the direct translation of the definition found
in the book before to continue:
*}

lemma eval_B_once:
  "eval1_B t t' \<Longrightarrow> eval_B t t'"
by (simp add: eval_B.intros)

lemma eval_B_transitive:
  "eval_B t t' \<Longrightarrow> eval_B t' t'' \<Longrightarrow> eval_B t t''"
by (induction t t' rule: eval_B.induct) (auto intro: eval_B.intros)

lemma eval_direct_eq_eval_B:
  "eval_direct = eval_B"
proof ((rule ext)+, rule iffI)
  fix t t'
  assume "eval_direct t t'"
  thus "eval_B t t'" by (auto intro: e_base elim: eval_direct.induct eval_B_once eval_B_transitive)
next
  fix t t'
  assume "eval_B t t'"
  thus "eval_direct t t'" by (auto intro: e_self dest!: e_once elim: eval_B.induct e_transitive)
qed

(* subsubsection {* Corollary 3.5.11 *} *)

text {*
The next theorem we consider is the uniqueness of normal form, which is a corollary of the
determinacy of the single-step evaluation:
*}

corollary uniqueness_of_normal_form:
  "eval_B t u \<Longrightarrow> eval_B t u' \<Longrightarrow> is_normal_form_B u \<Longrightarrow> is_normal_form_B u' \<Longrightarrow> u = u'"
proof (induction t u rule: eval_B.induct)
  case (e_base t)
  thus ?case by (auto elim: eval_B.cases simp: is_normal_form_B_def)
next
  case (e_step t t' t'')
  thus ?case by (metis eval_B.cases is_normal_form_B_def eval_single_determinacy)
qed

text {*
The last theorem we consider is the termination of evaluation. To prove it, we must first add a
helper lemma about the size of terms after evaluation, which was implicitly assumed in the book:
*}

(*<*)
(* subsubsection {* Theorem 3.5.12 *} *)
primrec size_B :: "bterm \<Rightarrow> nat" where
  "size_B BTrue = 1" |
  "size_B BFalse = 1" |
  "size_B (BIf t1 t2 t3) = 1 + size_B t1 + size_B t2 + size_B t3"
(*>*)

lemma eval_once_size_B:
  "eval1_B t t' \<Longrightarrow> size_B t > size_B t'"
by (induction t t' rule: eval1_B.induct) simp_all

theorem termination_of_evaluation:
  "\<exists>t'. eval_B t t' \<and> is_normal_form_B t'"
by (induction rule: measure_induct_rule[of size_B])
  (metis e_base e_step eval_once_size_B is_normal_form_B_def)

subsection {* Arithmetic Expressions *}

text {*
We now turn to the fully fledged arithmetic expression language. The syntax is defined in the same
way as for booleans:\footnote{the suffix \emph{nb} stands for \emph{numeric and booleans}.}
*}

datatype nbterm =
  NBTrue |
  NBFalse |
  NBIf nbterm nbterm nbterm |
  NBZero |
  NBSucc nbterm |
  NBPred nbterm |
  NBIs_zero nbterm
(*<*)

(* subsubsection {* Definition 3.3.1 *} *)

primrec const_NB :: "nbterm \<Rightarrow> nbterm set" where
  "const_NB NBTrue = {NBTrue}" |
  "const_NB NBFalse = {NBFalse}" |
  "const_NB NBZero = {NBZero}" |
  "const_NB (NBSucc t) = const_NB t" |
  "const_NB (NBPred t) = const_NB t" |
  "const_NB (NBIs_zero t) = const_NB t" |
  "const_NB (NBIf t1 t2 t3) = const_NB t1 \<union> const_NB t2 \<union> const_NB t3"

(* subsubsection {* Definition 3.3.2 *} *)

primrec size_NB :: "nbterm \<Rightarrow> nat" where
  "size_NB NBTrue = 1" |
  "size_NB NBFalse = 1" |
  "size_NB NBZero = 1" |
  "size_NB (NBSucc t) = size_NB t + 1" |
  "size_NB (NBPred t) = size_NB t + 1" |
  "size_NB (NBIs_zero t) = size_NB t + 1" |
  "size_NB (NBIf t1 t2 t3) = size_NB t1 + size_NB t2 + size_NB t3 + 1"

primrec depth_NB :: "nbterm \<Rightarrow> nat" where
  "depth_NB NBTrue = 1" |
  "depth_NB NBFalse = 1" |
  "depth_NB NBZero = 1" |
  "depth_NB (NBSucc t) = depth_NB t + 1" |
  "depth_NB (NBPred t) = depth_NB t + 1" |
  "depth_NB (NBIs_zero t) = depth_NB t + 1" |
  "depth_NB (NBIf t1 t2 t3) = max (depth_NB t1) (max (depth_NB t2) (depth_NB t3)) + 1"

(* subsubsection {* Lemma 3.3.3 *} *)

lemma card_union_leq_sum_card: "card (A \<union> B) \<le> card A + card B"
  by (cases "finite A \<and> finite B") (simp only: card_Un_Int, auto)

lemma "card (const_NB t) \<le> size_NB t"
proof (induction t)
  case (NBIf t1 t2 t3)
  show ?case
  proof -
    let ?t1 = "const_NB t1"
    let ?t2 = "const_NB t2"
    let ?t3 = "const_NB t3"
    have "card (?t1 \<union> ?t2 \<union> ?t3) \<le> card ?t1 + card ?t2 + card ?t3"
      by (smt card_union_leq_sum_card add_le_imp_le_right le_antisym le_trans nat_le_linear)
    also have "\<dots> \<le> size_NB t1 + size_NB t2 + size_NB t3"
      using NBIf.IH by simp
    finally show ?thesis by simp
  qed
qed (simp_all add: le_SucI)

(* subsubsection {* Theorem 3.3.4 *} *)

theorems induct_depth = measure_induct_rule[of depth_NB]
theorems induct_size = measure_induct_rule[of size_NB]
theorems structural_induction = nbterm.induct

(*>*)
text {*
Values now consist either of booleans or numeric values, for which a separate inductive
definition is given. Here is the definition as founded in the book:

\begin{verbatim}
  v ::=
    true             true value
    false            false value
    nv               numeric value
  nv ::=
    0                zero value
    succ nv          successor value
\end{verbatim}

Our inductive definition is very similar, but contains explicit assumptions on the nature of
\texttt{nv}. The book uses naming conventions which define letters such as \texttt{t} as
always representing terms, letters such as \texttt{v} as always representing values and variants of
\texttt{nv} as always representing numeric values. In our formalization, such implicit assumption is
possible for \texttt{t} because Isabelle/HOL infers that @{term nberm} is the only type that could
be place at this position. Since values and numerical values do not have a proper type but are a
subset of terms, we must add assumptions to declare the nature of these variables:
*}

inductive is_numeric_value_NB :: "nbterm \<Rightarrow> bool" where
  "is_numeric_value_NB NBZero" |
  "is_numeric_value_NB nv \<Longrightarrow> is_numeric_value_NB (NBSucc nv)"

inductive is_value_NB :: "nbterm \<Rightarrow> bool" where
  "is_value_NB NBTrue" |
  "is_value_NB NBFalse" |
  "is_numeric_value_NB nv \<Longrightarrow> is_value_NB nv"

text {*
The single-step evaluation relation is a superset of the one defined for booleans:
*}

inductive eval1_NB :: "nbterm \<Rightarrow> nbterm \<Rightarrow> bool" where
  eval1_NBIf_NBTrue: "eval1_NB (NBIf NBTrue t2 t3) t2" |
  eval1_NBIf_NBFalse: "eval1_NB (NBIf NBFalse t2 t3) t3" |
  eval1_NBIf: "eval1_NB t1 t1' \<Longrightarrow> eval1_NB (NBIf t1 t2 t3) (NBIf t1' t2 t3)" |
  eval1_NBSucc: "eval1_NB t t' \<Longrightarrow> eval1_NB (NBSucc t) (NBSucc t')" |
  eval1_NBPred_NBZero: "eval1_NB (NBPred NBZero) NBZero" |
  eval1_NBPred_NBSucc: "is_numeric_value_NB nv \<Longrightarrow> eval1_NB (NBPred (NBSucc nv)) nv" |
  eval1_NBPred: "eval1_NB t t' \<Longrightarrow> eval1_NB (NBPred t) (NBPred t')" |
  eval1_NBIs_zero_NBZero: "eval1_NB (NBIs_zero NBZero) NBTrue" |
  eval1_NBIs_zero_NBSucc: "is_numeric_value_NB nv \<Longrightarrow> eval1_NB (NBIs_zero (NBSucc nv)) NBFalse" |
  eval1_NBIs_zero: "eval1_NB t t' \<Longrightarrow> eval1_NB (NBIs_zero t) (NBIs_zero t')"

text {*
The multi-step evaluation relation and the definition normal form are exactly the
same as for booleans:
*}

inductive eval_NB :: "nbterm \<Rightarrow> nbterm \<Rightarrow> bool" where
  eval_NB_base: "eval_NB t t" |
  eval_NB_step: "eval1_NB t t' \<Longrightarrow> eval_NB t' t'' \<Longrightarrow> eval_NB t t''"

definition is_normal_form_NB :: "nbterm \<Rightarrow> bool" where
  "is_normal_form_NB t \<longleftrightarrow> (\<forall>t'. \<not> eval1_NB t t')"

text {*
The reason is that all the actual work is perfomed by the singl-step evaluation relation and these
two definition are just a convenient notation.

In the book, the second covering this fully fledge arithmetic expression language is mainly an
explanation of the constructions not present in the boolean expression language and does not
contains any theorems. Nevertheless, we decided to reprove, or disprove, the theorems introduced in
the section on booleans.
*}

(*<*)
(* Usefull lemmas *)

lemma eval1_NB_impl_eval_NB: "eval1_NB t t' \<Longrightarrow> eval_NB t t'"
  by (simp add: eval_NB_step eval_NB_base)

lemma eval_NB_transitive: "eval_NB t t' \<Longrightarrow> eval_NB t' t'' \<Longrightarrow> eval_NB t t''"
by (induction t t' rule: eval_NB.induct) (auto intro: eval_NB.intros)

lemma not_eval_once_numeric_value: "is_numeric_value_NB nv \<Longrightarrow> eval1_NB nv t \<Longrightarrow> P"
by (induction nv arbitrary: t rule: is_numeric_value_NB.induct)
  (auto elim: eval1_NB.cases)

(* subsubsection {* Theorem 3.5.4 for Arithmetic Expressions *} *)
(*>*)

text {*
The determinacy of the single-step evaluation still holds:
*}

theorem eval1_NB_right_unique:
  "eval1_NB t t' \<Longrightarrow> eval1_NB t t'' \<Longrightarrow> t' = t''"
proof (induction t t' arbitrary: t'' rule: eval1_NB.induct)
  case (eval1_NBIf t1 t1' t2 t3)
  from eval1_NBIf.prems eval1_NBIf.hyps show ?case
    by (auto intro: eval1_NB.cases dest: eval1_NBIf.IH)
next
  case (eval1_NBSucc t1 t2)
  from eval1_NBSucc.prems eval1_NBSucc.IH show ?case
    by (auto elim: eval1_NB.cases)
next
  case (eval1_NBPred_NBSucc nv1)
  from eval1_NBPred_NBSucc.prems eval1_NBPred_NBSucc.hyps show ?case
    by (cases rule: eval1_NB.cases)
      (auto intro: is_numeric_value_NB.intros elim: not_eval_once_numeric_value[rotated])
next
  case (eval1_NBPred t1 t2)
  from eval1_NBPred.hyps eval1_NBPred.prems show ?case
    by (auto
      intro: eval1_NBPred.IH is_numeric_value_NB.intros
      elim: eval1_NB.cases
      dest: not_eval_once_numeric_value)
next
  case (eval1_NBIs_zero_NBSucc nv)
  thus ?case
    by (auto intro: eval1_NB.cases not_eval_once_numeric_value is_numeric_value_NB.intros)
next
  case (eval1_NBIs_zero t1 t2)
  from eval1_NBIs_zero.prems eval1_NBIs_zero.hyps show ?case
    by (cases rule: eval1_NB.cases) (auto
      elim: eval1_NB.cases
      intro: eval1_NBIs_zero.IH is_numeric_value_NB.intros
      elim: not_eval_once_numeric_value[rotated])
qed (auto elim: eval1_NB.cases)

(* subsubsection {* Theorem 3.5.7 for Arithmetic Expressions *} *)

text {*
Every value is in normal form:
*}

theorem value_imp_normal_form_NB:
  "is_value_NB t \<Longrightarrow> is_normal_form_NB t"
by (auto
  intro: not_eval_once_numeric_value
  elim: eval1_NB.cases is_value_NB.cases
  simp: is_normal_form_NB_def)

(* subsubsection {* Theorem 3.5.8 does not hold for Arithmetic Expressions *} *)

text {*
But contrary to boolean expressions, some expressions that are in normal form are not values. An
example of such term is @{term "NBSucc NBTrue"}.
*}

theorem not_normal_form_imp_value_NB:
  "\<exists>t. is_normal_form_NB t \<and> \<not> is_value_NB t" (is "\<exists>t. ?P t")
proof
  have a: "is_normal_form_NB (NBSucc NBTrue)"
    by (auto elim: eval1_NB.cases simp: is_normal_form_NB_def)
  have b: "\<not> is_value_NB (NBSucc NBTrue)"
    by (auto elim: is_numeric_value_NB.cases simp: is_value_NB.simps)
  from a b show "?P (NBSucc NBTrue)" by simp
qed

(* subsubsection {* Corollary 3.5.11 for Arithmetic Expressions *} *)

text {*
The uniqueness of normal form still holds:
*}

corollary uniqueness_of_normal_form_NB:
  "eval_NB t u \<Longrightarrow> eval_NB t u' \<Longrightarrow> is_normal_form_NB u \<Longrightarrow> is_normal_form_NB u' \<Longrightarrow> u = u'"
proof (induction t u arbitrary: u' rule: eval_NB.induct)
  case (eval_NB_base t)
  thus ?case by (auto elim: eval_NB.cases simp: is_normal_form_NB_def)
next
  case (eval_NB_step t1 t2 t3)
  thus ?case by (metis eval_NB.cases is_normal_form_NB_def eval1_NB_right_unique)
qed

(* subsubsection {* Theorem 3.5.12 for Arithmetic Expressions *} *)

text {*
So does the termination of the evaluation function:
*}

(*<*)
lemma eval_once_size_NB:
  "eval1_NB t t' \<Longrightarrow> size_NB t > size_NB t'"
by (induction t t' rule: eval1_NB.induct) auto
(*>*)

theorem eval_NB_always_terminate:
  "\<exists>t'. eval_NB t t' \<and> is_normal_form_NB t'"
proof (induction rule: measure_induct_rule[of size_NB])
  case (less t)
  show ?case
    apply (cases "is_normal_form_NB t")
    apply (auto intro: eval_NB_base)
    using eval_NB_step eval_once_size_NB is_normal_form_NB_def less.IH
    by blast
qed

(*<*)
end
(*>*)
