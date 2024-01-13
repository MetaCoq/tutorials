(*** MetaCoq Tutorial @ POPL 2024 ***)

Load MetaCoqPrelude.
(** If the above does not work for you, compile the file using
  `coqc -I . "" MetaCoqPrelude` or using `make`
  and use (uncomment) the following line instead
**)
(* Require Import MetaCoqPrelude. *)

Require Import List.

(** EXERCISE ** Print Assumptions

  A recent question on coq-club asked

  "Is there a way to get Print Assumptions to output fully qualified names of
  all items?"

  (https://sympa.inria.fr/sympa/arc/coq-club/2024-01/msg00007.html)

  There is no satisfying answer using just Coq's Print Assumptions command.

  The exercise here is to implement an improved Print Assumptions command in
  Coq, such that

  Compute print_assumptions ($quote_rec 0).

  prints []

  and

  Axiom test : nat.

  Compute print_assumptions ($quote_rec test).

  prints a list containing a representation of test.

  Define print_assumptions : global_env * term -> list kername

**)

Unset Guard Checking.
Section fix_Σ.

  Variable (Σ : global_env).

End fix_Σ.
Set Guard Checking.

(* Definition print_assumptions p := print_assms p.1 p.2. *)

(* Compute print_assumptions ($quote_rec 0). *)

Axiom test : nat.

(* Compute print_assumptions ($quote_rec test).

Module test.

  Require Import Classical.

  Lemma DNE P : ~~ P -> P.
  Proof.
    tauto.
  Qed.

End test.

Compute print_assumptions ($quote_rec test.DNE). *)

(** EXERCISE

  Define a function which replaces let binding by equivalent beta redexes.
  You can copy-paste and rename the below identity function as starting point.

**)

Fixpoint identity (t : term) :=
  match t with
  | tRel n => tRel n
  | tVar id => tVar id
  | tEvar ev args => tEvar ev (map identity args)
  | tSort s => tSort s
  | tCast t kind v => tCast (identity t) kind (identity v)
  | tProd na ty body => tProd na (identity ty) (identity body)
  | tLambda na ty body => tLambda na (identity ty) (identity body)
  | tLetIn na def def_ty body => tLetIn na (identity def) (identity def_ty) (identity body)
  | tApp f args => tApp (identity f) (map identity args)
  | tConst c u => tConst c u
  | tInd ind u => tInd ind u
  | tConstruct ind idx u => tConstruct ind idx u
  | tCase ind p discr brs =>
      let p' := map_predicate id identity identity p in
      let brs' := map_branches identity brs in
      tCase ind p' (identity discr) brs'
  | tProj proj t => tProj proj (identity t)
  | tFix mfix idx => tFix (map (map_def identity identity) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def identity identity) mfix) idx
  | tInt i => tInt i
  | tFloat f => tFloat f
  end.

(* #[bypass_check(guard)]
Fixpoint Mpower' (n : nat) : term :=
  match n with
  | 0 => $quote 1
  | 1 => tRel 0
  | 2 => tApp ($quote mult) [tRel 0; tRel 0]
  | S n' as n => if n mod 2 =? 0 then
                    tLet "p" ($quote nat) (Mpower' (div n 2))
                      (tApp ($quote mult) [tRel 0 ; tRel 0])
                else tApp ($quote mult) [Mpower' n' ; tRel 0]
  end.

Definition Mpower (n : nat) :=
  tLam "x" ($quote nat) (Mpower' n).

Definition power5 := ($unquote (Mpower 5)).
Print power5.

Check $unquote (let_to_lambda (Mpower 5)). *)

(** EXERCISE

  Define a function which replaces any subterm of the form a * b + c by a call
  to muladd:

**)

Definition muladd a b c := a * b + c.

Unset Guard Checking.

(* Check $unquote (fold_muladd ($quote (3 * 2 + 5))). *)

(* Check $unquote (fold_muladd ($quote (1 + (3 * 2 + 5)))). *)

(* Check $unquote (fold_muladd ($quote (1 + ((7 * 9 + 12) * 2 + 5)))). *)

(** EXERCISE

  Write a command reify that reifies Coq arithmetic formulas into the following
  datatype.

**)

Inductive arith :=
| aPlus : arith -> arith -> arith
| aConst : nat -> arith.

(* Goal 4 + (3 + 1) = 2.
Proof.
  match goal with
  | [ |- ?L = _ ] => pose ($unquote (reify ($quote L)))
  end.
Abort. *)
