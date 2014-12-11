(*<*)
theory Typed_Lambda_Calculus
imports
  Main
  "~/afp-code/thys/List-Index/List_Index"
begin
(*>*)

section {* Typed Lambda Calculus *}
text {* \label{sec:simply-typed-lambda-calculus} *}

text {*
We now revisit the $\lambda$-calculus (Section \ref{sec:untyped-lambda-calculus}) and augment it
with static types. Unlike the typed arithmetic expressions language, types are an integral part of
the language and its syntax. For this reason, we cannot import the theory of the untyped variant
and build on top of it, but need to provide new, although similar, definitions. We will prove type
safety through the progress and preservation theorems before to show that types can be safely erased
while preserving the semantic of the language.
*}

subsection {* Definitions *}

(* Definition 9.1.1 *)

text {*
In the untyped lambda-calculus, everything is a function. Thus, we need to provide the type of
functions, usually written @{text "a \<rightarrow> b"} which, given an argument of type @{term a}, will
evaluate to a value of type @{term b}. Since both @{term a} and @{term b} must be valid types, we
need to provide a base case to stop the recursion at some point. To keep the language minimal, we
only add boolean expressions as base case:\footnote{The prefix \emph{l} stands for
\emph{lambda-calculus}.}
*}

datatype_new ltype =
  Bool |
  Fun (domain: ltype) (codomain: ltype) (infixr "\<rightarrow>" 225)

text {*
In the previous definition, @{const Fun} is a type constructor which can be use to create functions
types for some concreate domain and codomain. Examples of such types include @{term "Bool \<rightarrow> Bool"},
@{term "(Bool \<rightarrow> Bool) \<rightarrow> Bool"}, @{term [source] "(Bool \<rightarrow> Bool) \<rightarrow> (Bool \<rightarrow> Bool)"},
@{term "(Bool \<rightarrow> Bool) \<rightarrow> Bool \<rightarrow> Bool"}, etc. Note that the last two examples are equivalent, since
the @{text "\<rightarrow>"} operator is right-associative.

In programming languages, more types are usually added as base cases to the core calculus for
performance reason. Examples include integers, floating point numbers, characters, arrays, etc.

Since variables can now range over infinitely many types, we need a way to know which type a
function require as domain. There are two possible strategies: annotate the $\lambda$-abstractions
with the intended type of their arguments or analyse the body of the abstraction to infer the
required type. \emph{TAPL} chose the former strategy.

The syntax of this language differs from the pure $\lambda$-calculus by having constructions for
boolean expressions and a type annotation on function abstractions:
*}

datatype_new lterm =
  LTrue |
  LFalse |
  LIf (bool_expr: lterm) (then_expr: lterm) (else_expr: lterm) |
  LVar nat |
  LAbs (arg_type: ltype) (body: lterm) |
  LApp lterm lterm

text {*
We define the shift and substitution functions for this extended language:
*}

primrec shift_L :: "int \<Rightarrow> nat \<Rightarrow> lterm \<Rightarrow> lterm" where
  "shift_L d c LTrue = LTrue" |
  "shift_L d c LFalse = LFalse" |
  "shift_L d c (LIf t1 t2 t3) = LIf (shift_L d c t1) (shift_L d c t2) (shift_L d c t3)" |
  "shift_L d c (LVar k) = LVar (if k < c then k else nat (int k + d))" |
  "shift_L d c (LAbs T t) = LAbs T (shift_L d (Suc c) t)" |
  "shift_L d c (LApp t1 t2) = LApp (shift_L d c t1) (shift_L d c t2)"

primrec subst_L :: "nat \<Rightarrow> lterm \<Rightarrow> lterm \<Rightarrow> lterm" where
  "subst_L j s LTrue = LTrue" |
  "subst_L j s LFalse = LFalse" |
  "subst_L j s (LIf t1 t2 t3) = LIf (subst_L j s t1) (subst_L j s t2) (subst_L j s t3)" |
  "subst_L j s (LVar k) = (if k = j then s else LVar k)" |
  "subst_L j s (LAbs T t) = LAbs T (subst_L (Suc j) (shift_L 1 0 s) t)" |
  "subst_L j s (LApp t1 t2) = LApp (subst_L j s t1) (subst_L j s t2)"

text {*
The semantic is similar to the pure $\lambda$-calculus. A first difference is that the set of values
also contain the boolean constants:
*}

inductive is_value_L :: "lterm \<Rightarrow> bool" where
  "is_value_L LTrue" |
  "is_value_L LFalse" |
  "is_value_L (LAbs T t)"

text {*
A second difference is that the single-step evaluation relation also contains the rules for the
evaluation of the conditional statement:
*}

inductive eval1_L :: "lterm \<Rightarrow> lterm \<Rightarrow> bool" where
  eval1_LIf_LTrue:
    "eval1_L (LIf LTrue t2 t3) t2" |
  eval1_LIf_LFalse:
    "eval1_L (LIf LFalse t2 t3) t3" |
  eval1_LIf:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (LIf t1 t2 t3) (LIf t1' t2 t3)" |
  eval1_LApp1:
    "eval1_L t1 t1' \<Longrightarrow> eval1_L (LApp t1 t2) (LApp t1' t2)" |
  eval1_LApp2:
    "is_value_L v1 \<Longrightarrow> eval1_L t2 t2' \<Longrightarrow> eval1_L (LApp v1 t2) (LApp v1 t2')" |
  eval1_LApp_LAbs:
    "is_value_L v2 \<Longrightarrow> eval1_L (LApp (LAbs T t12) v2)
      (shift_L (-1) 0 (subst_L 0 (shift_L 1 0 v2) t12))"

text {*
When type-checking the body of a function abstraction, we assume that the given function argument
does have the type annotated. Since the body could itself be a function abstraction, we need to keep
track of this set of assumptions, also known as typing context. Since the book considers variables
to be a named reference to a $\lambda$-absraction, its typing context is a set of identifier--type
pairs. Our use of ``de Bruijn indices'' requires us to consider an alternative representation. We
define a context to be a list of types whose $n$th position contains the type of the $n$th
enclosing $\lambda$-abstraction:
*}

type_synonym lcontext = "ltype list"

text {*
To keep the notation similar to the book, we define some synonyms for the list operations
that mimic their set counterpart:
*}

notation Nil ("\<emptyset>")
abbreviation cons :: "lcontext \<Rightarrow> ltype \<Rightarrow> lcontext" (infixl "|,|" 200) where
  "cons \<Gamma> T \<equiv> T # \<Gamma>"
abbreviation elem' :: "(nat \<times> ltype) \<Rightarrow> lcontext \<Rightarrow> bool" (infix "|\<in>|" 200) where
  "elem' p \<Gamma> \<equiv> fst p < length \<Gamma> \<and> snd p = nth \<Gamma> (fst p)"

text {*
We now define the typing relation by translating the induction rules present in the book to an
inductive definition:
*}

inductive has_type_L :: "lcontext \<Rightarrow> lterm \<Rightarrow> ltype \<Rightarrow> bool" ("((_)/ \<turnstile> (_)/ |:| (_))" [150, 150, 150] 150) where
  has_type_LTrue:
    "\<Gamma> \<turnstile> LTrue |:| Bool" |
  has_type_LFalse:
    "\<Gamma> \<turnstile> LFalse |:| Bool" |
  has_type_LIf:
    "\<Gamma> \<turnstile> t1 |:| Bool \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| T \<Longrightarrow> \<Gamma> \<turnstile> t3 |:| T \<Longrightarrow> \<Gamma> \<turnstile> (LIf t1 t2 t3) |:| T" |
  has_type_LVar:
    "(x, T) |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (LVar x) |:| T" |
  has_type_LAbs:
    "(\<Gamma> |,| T1) \<turnstile> t2 |:| T2 \<Longrightarrow> \<Gamma> \<turnstile> (LAbs T1 t2) |:| (T1 \<rightarrow> T2)" |
  has_type_LApp:
    "\<Gamma> \<turnstile> t1 |:| (T11 \<rightarrow> T12) \<Longrightarrow> \<Gamma> \<turnstile> t2 |:| T11 \<Longrightarrow> \<Gamma> \<turnstile> (LApp t1 t2) |:| T12"

text {*
As an example of a usage of the typing relation, consider the type of the application of
@{term LTrue} to the boolean identity function:
*}

lemma "\<emptyset> \<turnstile> (LApp (LAbs Bool (LVar 0)) LTrue) |:| Bool"
  by (auto intro!: has_type_L.intros)

(* Exercice 9.2.2 *)

text {*
A more interesting example, assuming there is one variable of type @{term "Bool \<rightarrow> Bool"} in the
typing context, is the type of applying a boolean expression to this variable:
*}

lemma
  assumes "\<Gamma> = \<emptyset> |,| (Bool \<rightarrow> Bool)"
  shows "\<Gamma> \<turnstile> LApp (LVar 0) (LIf LFalse LTrue LFalse) |:| Bool"
by (auto intro!: has_type_L.intros simp: assms)
(*<*)

lemma
  assumes "\<Gamma> = \<emptyset> |,| (Bool \<rightarrow> Bool)"
  shows "\<Gamma> \<turnstile> LAbs Bool (LApp (LVar 1) (LIf (LVar 0) LTrue LFalse)) |:| Bool \<rightarrow> Bool"
  by (auto intro!: has_type_L.intros simp: assms)

(* Exercice 9.2.3 *)

lemma
  assumes "\<Gamma> = \<emptyset> |,| Bool \<rightarrow> Bool \<rightarrow> Bool |,| Bool |,| Bool"
  shows "\<Gamma> \<turnstile> LApp (LApp (LVar 2) (LVar 1)) (LVar 0) |:| Bool"
  by (auto intro!: has_type_L.intros simp: assms)

lemma ex9_2_3_general:
  "\<emptyset> |,| T \<rightarrow> T \<rightarrow> Bool |,| T |,| T \<turnstile> LApp (LApp (LVar 2) (LVar 1)) (LVar 0) |:| Bool"
  by (auto intro!: has_type_L.intros simp: assms)

lemmas ex9_2_3_bool = ex9_2_3_general[of Bool]

(*>*)
subsection {* Properties of Typing *}

(* Lemma 9.3.1 *)

text {*
The inversion of typing relation, which gives us informations on types for specific terms, will be
a useful lemma in the following theorems:
*}

lemma inversion:
  "\<Gamma> \<turnstile> LTrue |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> LFalse |:| R \<Longrightarrow> R = Bool"
  "\<Gamma> \<turnstile> LIf t1 t2 t3 |:| R \<Longrightarrow> \<Gamma> \<turnstile> t1 |:| Bool \<and> \<Gamma> \<turnstile> t2 |:| R \<and> \<Gamma> \<turnstile> t3 |:| R"
  "\<Gamma> \<turnstile> LVar x |:| R \<Longrightarrow> (x, R) |\<in>| \<Gamma>"
  "\<Gamma> \<turnstile> LAbs T1 t2 |:| R \<Longrightarrow> \<exists>R2. R = T1 \<rightarrow> R2 \<and> \<Gamma> |,| T1 \<turnstile> t2 |:| R2"
  "\<Gamma> \<turnstile> LApp t1 t2 |:| R \<Longrightarrow> \<exists>T11. \<Gamma> \<turnstile> t1 |:| T11 \<rightarrow> R \<and> \<Gamma> \<turnstile> t2 |:| T11"
  by (auto elim: has_type_L.cases)
(*<*)
(* Exercise 9.3.2 *)

lemma "\<not> (\<Gamma> \<turnstile> LApp (LVar 0) (LVar 0) |:| T)"
proof
  assume "\<Gamma> \<turnstile> LApp (LVar 0) (LVar 0) |:| T"
  hence "\<exists>U. \<Gamma> \<turnstile> LVar 0 |:| U \<rightarrow> T \<and> \<Gamma> \<turnstile> LVar 0 |:| U" by (auto dest: inversion(6))
  hence "\<exists>U. (0, U \<rightarrow> T) |\<in>| \<Gamma> \<and> (0, U) |\<in>| \<Gamma>" by (auto dest!: inversion(4))
  hence "\<exists>U R. (0, R) |\<in>| \<Gamma> \<and> R = U \<rightarrow> T \<and> R = U" by simp
  hence "\<exists>U. U = U \<rightarrow> T" by auto
  thus "False" by (auto dest: arg_cong[of _ _ size])
qed

(*>*)
(* Theorem 9.3.3 *)

text {*
Every terms have at most one type:
*}

theorem uniqueness_of_types:
  "\<Gamma> \<turnstile> t |:| T1 \<Longrightarrow> \<Gamma> \<turnstile> t |:| T2 \<Longrightarrow> T1 = T2"
by (induction \<Gamma> t T1 arbitrary: T2 rule: has_type_L.induct)
  (metis prod.sel ltype.sel inversion)+

(* Lemma 9.3.4 *)

text {*
The canonical form of values, which gives us information on terms for well-typed values, will also
be useful later:
*}

lemma canonical_forms:
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| Bool \<Longrightarrow> v = LTrue \<or> v = LFalse"
  "is_value_L v \<Longrightarrow> \<Gamma> \<turnstile> v |:| T1 \<rightarrow> T2 \<Longrightarrow> \<exists>t. v = LAbs T1 t"
by (auto elim: has_type_L.cases is_value_L.cases)

(* Theorem 9.3.5 *)

text {*
To formalize the concept of free variables (i.e. variables referring to a non existing
$\lambda$-abstraction), we provide a function that return the set of free variables of a term:
*}

primrec FV :: "lterm \<Rightarrow> nat set" where
  "FV LTrue = {}" |
  "FV LFalse = {}" |
  "FV (LIf t1 t2 t3) = FV t1 \<union> FV t2 \<union> FV t3" |
  "FV (LVar x) = {x}" |
  "FV (LAbs T t) = image (\<lambda>x. x - 1) (FV t - {0})" |
  "FV (LApp t1 t2) = FV t1 \<union> FV t2"
(*<*)

lemma "FV (LAbs Bool (LAbs Bool (LIf (LVar 2) (LVar 0) (LVar 1)))) = {0}"
  by (simp add: insert_commute[of _ 0])

(*>*)
text {*
Based on the @{const FV} function, we can now define a closed term to be a term whose set of
free-variables is empty:
*}

definition is_closed :: "lterm \<Rightarrow> bool" where
  "is_closed t \<equiv> FV t = {}"
(*<*)

lemma "\<not> is_closed (LAbs Bool (LAbs Bool (LIf (LVar 2) (LVar 0) (LVar 1))))"
  by (simp add: is_closed_def insert_commute[of _ 0])

lemma "is_closed (LAbs Bool (LAbs Bool (LAbs Bool (LIf (LVar 2) (LVar 0) (LVar 1)))))"
  by (simp add: is_closed_def insert_commute[of _ 0])

(*>*)
text {*
We now prove the progress theorem (i.e. a well-typed term is either a value or can take a step
according to the evaluation rules):
*}

theorem progress:
   "\<emptyset> \<turnstile> t |:| T \<Longrightarrow> is_closed t \<Longrightarrow> is_value_L t \<or> (\<exists>t'. eval1_L t t')"
proof (induction t T rule: has_type_L.induct)
  case (has_type_LIf \<Gamma> t1 t2 T t3)
  thus ?case by (cases "is_value_L t1")
    (auto intro: eval1_L.intros dest: canonical_forms simp: is_closed_def)
next
  case (has_type_LApp \<Gamma> t1 T11 T12 t2)
  thus ?case by (cases "is_value_L t1", cases "is_value_L t2")
    (auto intro: eval1_L.intros dest: canonical_forms simp: is_closed_def)
qed (simp_all add: is_value_L.intros is_closed_def)
(*<*)

lemma[simp]: "nat (int x + 1) = Suc x" by simp
lemma[simp]: "nat (1 + int x) = Suc x" by simp

(*>*)
(* Lemma 9.3.7 *)

text {*
Proving the preservation theorem requires use to first prove a number of helper lemmas. For these,
our reliance on "de Bruijn indices" forces us to depart substantially from the book.

The first lemma the book consider is the permutation of the typing context:

\begin{quotation}
  \noindent If $\Gamma \vdash t : T$ and $\Delta$ is a permutation of $\Gamma$, then
  $\Delta \vdash t : T$. Moreover, the latter derivation has the same depth as the former.
\end{quotation}

Translated naïvely, this lemma does not hold with our representation of the typing context as an
ordered list.

The book then consider the weakening the typing context:

\begin{quotation}
  \noindent If $\Gamma \vdash t : T$ and $x \notin dom(\Gamma)$, then $\Gamma , x:S \vdash t : T$.
  Moreover, the latter derivation has the same depth as the former.
\end{quotation}

This lemma does hold with our representation of the typing context, but we need to express it in
terms of list by inserting @{term s} at a fixed position @{term n}. Moreover, we need to shift up
every variable refering to a $\lambda$-abstraction farther in the context than @{term n}.
*}

lemma weakening:
  "\<Gamma> \<turnstile> t |:| T \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow> insert_nth n S \<Gamma> \<turnstile> shift_L 1 n t |:| T"
proof (induction \<Gamma> t T arbitrary: n rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> T1 t2 T2)
  from has_type_LAbs.prems has_type_LAbs.hyps
    has_type_LAbs.IH[where n="Suc n"] show ?case
    by (auto intro: has_type_L.intros)
qed (auto simp: nth_append min_def intro: has_type_L.intros)

text {*
This specific formulation was difficult to come with but the proof is, after simplifications, fairly
short. It is a typical situation in interactive theorem proving that the result seems simple and
does not make justice to the effort. It can be considered an achievement to reduce a huge and
unreadable proof to a small and readable one.
*}

(* Lemma 9.3.8 *)

text {*
The book then consider, as its last helper lemma, the preservation of types under substitution:

\begin{quotation}
  \noindent If $\Gamma, x:S \vdash t : T$ and $\Gamma \vdash s : S$, then
  $\Gamma \vdash [x \mapsto s] : T$.
\end{quotation}

We prove a slightly different theorem that is more suitable for the coming proofs:
*}

lemma substitution:
  "\<Gamma> \<turnstile> t |:| T \<Longrightarrow>  \<Gamma> \<turnstile> LVar n |:| S \<Longrightarrow> \<Gamma> \<turnstile> s |:| S \<Longrightarrow> \<Gamma> \<turnstile> subst_L n s t |:| T"
proof (induction \<Gamma> t T arbitrary: s n rule: has_type_L.induct)
  case (has_type_LAbs \<Gamma> T1 t T2)
  thus ?case by (fastforce
    intro: has_type_L.intros weakening[where n=0, unfolded insert_nth_def nat.rec]
    dest: inversion(4))
qed (auto intro!: has_type_L.intros dest: inversion(4))
(*<*)
(* Theorem 9.3.9 *)

inductive_cases eval1_LAppE: "eval1_L (LApp t1 t2) t"

lemma[simp]: "nat (int x - 1) = x - 1" by simp

(*>*)
text {*
We must provide a few more lemmas, the most important expressing that it is safe to remove a
variable from the context if it is not referenced in the considered term:
*}

lemma shift_down:
  "insert_nth n U \<Gamma> \<turnstile> t |:| T \<Longrightarrow> n \<le> length \<Gamma> \<Longrightarrow>
   (\<And>x. x \<in> FV t \<Longrightarrow> x \<noteq> n) \<Longrightarrow> \<Gamma> \<turnstile> shift_L (- 1) n t |:| T"
proof (induction "insert_nth n U \<Gamma>" t T arbitrary: \<Gamma> n rule: has_type_L.induct)
  case (has_type_LAbs V t T)
  from this(1,3,4) show ?case
    by (fastforce intro: has_type_L.intros has_type_LAbs.hyps(2)[where n="Suc n"])+
qed (fastforce intro: has_type_L.intros simp: nth_append min_def)+

text {*
This lemma was the most challenging to express and prove. It was difficult to define the correct set
of assumptions and, prior to simplifications, the proof was quite imposing.

We also need to define how the @{const FV} function react with respect to the @{term shift_L} and
@{term subst_L} functions:
*}
(*<*)

lemma gr_Suc_conv: "Suc x \<le> n \<longleftrightarrow> (\<exists>m. n = Suc m \<and> x \<le> m)"
  by (cases n) auto

(*>*)
lemma FV_shift:
  "FV (shift_L (int d) c t) = image (\<lambda>x. if x \<ge> c then x + d else x) (FV t)"
proof (induction t arbitrary: c rule: lterm.induct)
  case (LAbs T t)
  thus ?case by (auto simp: gr_Suc_conv image_iff) force+
qed auto

lemma FV_subst:
  "FV (subst_L n t u) = (if n \<in> FV u then (FV u - {n}) \<union> FV t else FV u)"
proof (induction u arbitrary: n t rule: lterm.induct)
  case (LAbs T u)
  thus ?case
    apply (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1])
    by (metis DiffI One_nat_def UnCI diff_Suc_1 empty_iff imageI insert_iff nat.distinct(1))+
qed (auto simp: gr0_conv_Suc image_iff FV_shift[of 1, unfolded int_1])

text {*
Again, those lemmas are not present in the book. It is usual for paper proofs to be a little sketchy
and rely on readers to imagine fill in the blanks for some simple lemmas. The need for these arise
from the use of the @{const FV} function in the @{thm [source] shift_down} lemma.

Building on top of these lemmas, we can now prove the preservation theorem:
*}

theorem preservation:
  "\<Gamma> \<turnstile> t |:| T \<Longrightarrow> eval1_L t t' \<Longrightarrow> \<Gamma> \<turnstile> t' |:| T"
proof (induction \<Gamma> t T arbitrary: t' rule: has_type_L.induct)
  case (has_type_LIf \<Gamma> t1 t2 T t3)
  thus ?case by (auto intro: has_type_L.intros eval1_L.cases[OF has_type_LIf.prems])
next
  case (has_type_LApp \<Gamma> t1 T11 T12 t2)
  thus ?case by (auto
    intro!: has_type_L.intros substitution shift_down
    dest!: inversion
    dest: weakening[where n=0, unfolded insert_nth_def nat.rec]
    elim!: eval1_LAppE
    split: lterm.splits if_splits
    simp: FV_subst FV_shift[of 1, unfolded int_1])
      (metis neq0_conv)
qed (auto elim: eval1_L.cases)

text {*
By proving the progress and the preservation theorems, we have shown that the typed
$\lambda$-calculus is type safe, i.e. every well-typed program has a well-defined semantics.
*}

subsection {* Erasure and Typability *}

text {*
The type system we formalized is completely static (i.e. there is no run-time checked involving the
types of terms). Since the type annotations are not used during evaluation, it is worth exploring
the possibility to erase them prior to execution. To this end, we define an untyped version of
our $\lambda$-calculus with booleans:
*}

datatype uterm =
  UTrue |
  UFalse |
  UIf uterm uterm uterm |
  UVar nat |
  UAbs uterm |
  UApp uterm uterm

primrec shift_U :: "int \<Rightarrow> nat \<Rightarrow> uterm \<Rightarrow> uterm" where
  "shift_U d c UTrue = UTrue" |
  "shift_U d c UFalse = UFalse" |
  "shift_U d c (UIf t1 t2 t3) =
    UIf (shift_U d c t1) (shift_U d c t2) (shift_U d c t3)" |
  "shift_U d c (UVar k) = UVar (if k < c then k else nat (int k + d))" |
  "shift_U d c (UAbs t) = UAbs (shift_U d (Suc c) t)" |
  "shift_U d c (UApp t1 t2) = UApp (shift_U d c t1) (shift_U d c t2)"

primrec subst_U :: "nat \<Rightarrow> uterm \<Rightarrow> uterm \<Rightarrow> uterm" where
  "subst_U j s UTrue = UTrue" |
  "subst_U j s UFalse = UFalse" |
  "subst_U j s (UIf t1 t2 t3) =
    UIf (subst_U j s t1) (subst_U j s t2) (subst_U j s t3)" |
  "subst_U j s (UVar k) = (if k = j then s else UVar k)" |
  "subst_U j s (UAbs t) = UAbs (subst_U (Suc j) (shift_U 1 0 s) t)" |
  "subst_U j s (UApp t1 t2) = UApp (subst_U j s t1) (subst_U j s t2)"

inductive is_value_U :: "uterm \<Rightarrow> bool" where
  "is_value_U UTrue" |
  "is_value_U UFalse" |
  "is_value_U (UAbs t)"

inductive eval1_U :: "uterm \<Rightarrow> uterm \<Rightarrow> bool" where
  "eval1_U (UIf UTrue t2 t3) t2" |
  "eval1_U (UIf UFalse t2 t3) t3" |
  "eval1_U t1 t1' \<Longrightarrow> eval1_U (UIf t1 t2 t3) (UIf t1' t2 t3)" |
  "eval1_U t1 t1' \<Longrightarrow> eval1_U (UApp t1 t2) (UApp t1' t2)" |
  "is_value_U v1 \<Longrightarrow> eval1_U t2 t2' \<Longrightarrow> eval1_U (UApp v1 t2) (UApp v1 t2')" |
  "is_value_U v2 \<Longrightarrow> eval1_U (UApp (UAbs t12) v2)
    (shift_U (-1) 0 (subst_U 0 (shift_U 1 0 v2) t12))"

text {*
We now define a morphism which maps every typed term to an equivalent untyped one:
*}

primrec erase :: "lterm \<Rightarrow> uterm" where
  "erase LTrue = UTrue" |
  "erase LFalse = UFalse" |
  "erase (LIf t1 t2 t3) = (UIf (erase t1) (erase t2) (erase t3))" |
  "erase (LVar x) = UVar x" |
  "erase (LAbs _ t) = UAbs (erase t)" |
  "erase (LApp t1 t2) = UApp (erase t1) (erase t2)"

text {*
We also characterize how the @{const erase} function reacts with respect to values and the
@{const shift_L} and @{const subst_L} functions.
*}

lemma is_value_erasure:
  "is_value_L t = is_value_U (erase t)"
by (induction t rule: lterm.induct) (auto simp: is_value_L.simps is_value_U.simps)

lemma shift_erasure:
  "erase (shift_L d c t) = shift_U d c (erase t)"
by (induction t arbitrary: d c rule: lterm.induct) auto

lemma subst_erasure:
  "erase (subst_L j s t) = subst_U j (erase s) (erase t)"
by (induction t arbitrary: j s rule: lterm.induct) (auto simp: shift_erasure)

(* Theorem 9.5.1 *)

text {*
We can now prove that every step of evaluation on a typed term can be perform in parallel on a
corresponding untyped term.
*}

theorem
"eval1_L t t' \<Longrightarrow> eval1_U (erase t) (erase t')"
by (induction t t' rule: eval1_L.induct)
  (auto intro: eval1_U.intros simp: shift_erasure subst_erasure is_value_erasure)

(*<*)
end
(*>*)
