(*** MetaCoq Tutorial @ POPL 2024 ***)

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

(* Load MetaCoqPrelude. *)
(** If the above does not work for you, compile the file using
  `coqc -I . "" MetaCoqPrelude` or using `make`
  and use (uncomment) the following line instead
**)
Require Import MetaCoqPrelude.

From Coq Require Import List Utf8.

Unset Guard Checking.
Section fix_Σ.

  Variable (Σ : global_env).

  Fixpoint assumptions (t : term) :=
    match t with
    | tRel n => []
    | tVar id => []
    | tEvar ev args => []
    | tSort s => []
    | tCast t kind v => assumptions t ++ assumptions v
    | tProd na ty body => assumptions ty ++ assumptions body
    | tLambda na ty body => assumptions ty ++ assumptions body
    | tLetIn na def def_ty body =>
      assumptions def ++ assumptions def_ty ++ assumptions body
    | tApp f args => assumptions f ++ concat (map assumptions args)
    | tConst c u =>
      match lookup_constant Σ c with
      | Some {| cst_body := Some b |} => assumptions b
      | _ => [ c ]
      end
    | tInd ind u => []
    | tConstruct ind idx u => []
    | tCase ind p discr brs =>
        concat (map assumptions p.(pparams)) ++
        assumptions p.(preturn) ++
        concat (map (λ b, assumptions b.(bbody)) brs) ++
        assumptions discr
    | tProj proj t => assumptions t
    | tFix mfix idx =>
      concat (map (λ d, assumptions d.(dtype) ++ assumptions d.(dbody)) mfix)
    | tCoFix mfix idx =>
      concat (map (λ d, assumptions d.(dtype) ++ assumptions d.(dbody)) mfix)
    | tInt i => []
    | tFloat f => []
    end.

End fix_Σ.
Set Guard Checking.

Definition print_assumptions p := assumptions p.1 p.2.

Compute print_assumptions ($quote_rec 0).

Axiom test : nat.

Compute print_assumptions ($quote_rec test).

Module test.

  Require Import Classical.

  Lemma DNE P : ~~ P -> P.
  Proof.
    tauto.
  Qed.

End test.

Compute print_assumptions ($quote_rec test.DNE).

(** Alternative solution by just traversing the global environment **)

Fixpoint assumptions_alt (Σ : global_declarations) :=
  match Σ with
  | (kn, ConstantDecl {| cst_body := None |}) :: Σ =>
    kn :: assumptions_alt Σ
  | (kn, _) :: Σ => assumptions_alt Σ
  | [] => []
  end.

Definition print_assumptions_alt (p : program) :=
  assumptions_alt p.1.(declarations).

Compute print_assumptions_alt ($quote_rec 0).
Compute print_assumptions_alt ($quote_rec test).
Compute print_assumptions_alt ($quote_rec test.DNE).

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

Fixpoint let_to_lambda (t : term) :=
  match t with
  | tRel n => tRel n
  | tVar id => tVar id
  | tEvar ev args => tEvar ev (map let_to_lambda args)
  | tSort s => tSort s
  | tCast t kind v => tCast (let_to_lambda t) kind (let_to_lambda v)
  | tProd na ty body => tProd na (let_to_lambda ty) (let_to_lambda body)
  | tLambda na ty body => tLambda na (let_to_lambda ty) (let_to_lambda body)
  | tLetIn na def def_ty body =>
    tApp (tLambda na (let_to_lambda def_ty) (let_to_lambda body)) [
      let_to_lambda def
    ]
  | tApp f args => tApp (let_to_lambda f) (map let_to_lambda args)
  | tConst c u => tConst c u
  | tInd ind u => tInd ind u
  | tConstruct ind idx u => tConstruct ind idx u
  | tCase ind p discr brs =>
      let p' := map_predicate id let_to_lambda let_to_lambda p in
      let brs' := map_branches let_to_lambda brs in
      tCase ind p' (let_to_lambda discr) brs'
  | tProj proj t => tProj proj (let_to_lambda t)
  | tFix mfix idx => tFix (map (map_def let_to_lambda let_to_lambda) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def let_to_lambda let_to_lambda) mfix) idx
  | tInt i => tInt i
  | tFloat f => tFloat f
  end.

#[bypass_check(guard)]
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

Check $unquote (let_to_lambda (Mpower 5)).

(** EXERCISE

  Define a function which replaces any subterm of the form a * b + c by a call
  to muladd:

**)

Definition muladd a b c := a * b + c.

Unset Guard Checking.

Fixpoint fold_muladd (t : term) :=
  match t with
  | tRel n => tRel n
  | tVar id => tVar id
  | tEvar ev args => tEvar ev (map fold_muladd args)
  | tSort s => tSort s
  | tCast t kind v => tCast (fold_muladd t) kind (fold_muladd v)
  | tProd na ty body => tProd na (fold_muladd ty) (fold_muladd body)
  | tLambda na ty body => tLambda na (fold_muladd ty) (fold_muladd body)
  | tLetIn na def def_ty body =>
    tLetIn na (fold_muladd def) (fold_muladd def_ty) (fold_muladd body)
  | tApp f ([ tApp g [ a ; b ] ; c ] as args) =>
    if (f == $quote plus) && (g == $quote mul) then
      tApp ($quote muladd) [ fold_muladd a ; fold_muladd b ; fold_muladd c ]
    else tApp (fold_muladd f) (map fold_muladd args)
  | tApp f args => tApp (fold_muladd f) (map fold_muladd args)
  | tConst c u => tConst c u
  | tInd ind u => tInd ind u
  | tConstruct ind idx u => tConstruct ind idx u
  | tCase ind p discr brs =>
      let p' := map_predicate id fold_muladd fold_muladd p in
      let brs' := map_branches fold_muladd brs in
      tCase ind p' (fold_muladd discr) brs'
  | tProj proj t => tProj proj (fold_muladd t)
  | tFix mfix idx => tFix (map (map_def fold_muladd fold_muladd) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def fold_muladd fold_muladd) mfix) idx
  | tInt i => tInt i
  | tFloat f => tFloat f
  end.

Check $unquote (fold_muladd ($quote (3 * 2 + 5))).

Check $unquote (fold_muladd ($quote (1 + (3 * 2 + 5)))).

Check $unquote (fold_muladd ($quote (1 + ((7 * 9 + 12) * 2 + 5)))).

(** EXERCISE

  Write a command reify that reifies Coq arithmetic formulas into the following
  datatype.

**)

Inductive arith :=
| aPlus : arith -> arith -> arith
| aConst : nat -> arith.

Fixpoint reify (t : term) :=
  match t with
  | tApp f [ a ; b ] =>
    if f == $quote plus
    then tApp ($quote aPlus) [ reify a ; reify b ]
    else tApp ($quote aConst) [ t ]
  | _ => tApp ($quote aConst) [ t ]
  end.

Goal 4 + (3 + 1) = 2.
Proof.
  match goal with
  | [ |- ?L = _ ] => pose ($unquote (reify ($quote L)))
  end.
Abort.
