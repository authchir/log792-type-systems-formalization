Formalizing _Types and Programming Languages_ in Isabelle/HOL
=================================

We formalize, using Isabelle/HOL, some languages present in the first two sections, namely "Untyped
Systems" and "Simple Types", of the book _Types and Programming Languages_ by Benjamin~C.~Pierce.
We first begin with a short tour of the lambda-calculus, type systems and the Isabelle/HOL theorem
prover before attacking the formalization _per se_. Starting with an arithmetic expressions language
offering Booleans and natural numbers, we pursue, after a brief digression to de Bruijn indices, to
the untyped lambda-calculus. Then, we return to a typed variant of the arithmetic expression
language before concluding with the simply typed lambda-calculu.

Preparation for AFP submission
------------------------------

- [ ] No use of the commands sorry or back.
- [ ] Instantiations must not use Isabelle-generated names such as xa — use
      Isar, the subgoal command or rename_tac to avoid such names.
- [x] No use of the command smt_oracle.
- [x] If your theories contain calls to nitpick, quickcheck, or nunchaku those
      calls must include the expect parameter. Alternatively the expect
      parameter must be set globally via, e.g. nitpick_params.
- [ ] apply scripts should be indented by subgoal as in the Isabelle
      distribution. If an apply command is applied to a state with n+1 subgoals,
      it must be indented by n spaces relative to the first apply in the
      sequence.
- [ ] Only named lemmas should carry attributes such as [simp].
- [x] We prefer structured Isar proofs over apply style, but do not mandate
      them.
- [ ] If there are proof steps that take significant time, i.e. longer than
      roughly 1 min, please add a short comment to that step, so maintainers
      will know what to expect.
- [ ] The entry must contain a ROOT file with one session that has the name of
      the entry. We strongly encourage precisely one session per entry, but
      exceptions can be made. All sessions must be in group (AFP), and all
      theory files of the submission must be contained in at least one session.
      See also the example ROOT file in the Example submission. 
