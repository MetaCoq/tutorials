(** * The template monad  *)
Load MetaCoqPrelude.

Module monad.

Import MCMonadNotation.
From MetaCoq Require Import bytestring.
Import String.
Open Scope bs.

Print TemplateMonad.

MetaCoq Run (tmBind (tmQuote (3 + 3)) tmPrint).

MetaCoq Run (tmBind (tmQuoteRec add) tmPrint).

MetaCoq Run (tmBind (tmLocate "add") tmPrint).

Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind)) >>= tmPrint
  | _ => tmFail ("[" ++ q ++ "] is not an inductive")
  end.

MetaCoq Run (printInductive "Coq.Init.Datatypes.nat").
MetaCoq Run (printInductive "nat").

CoInductive cnat : Set :=  O :cnat | S : cnat -> cnat.
MetaCoq Run (printInductive "cnat").

Definition printConstant (q : qualid) b : TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | ConstRef kn => (tmQuoteConstant kn b) >>= tmPrint
  | _ => tmFail ("[" ++ q ++ "] is not a constant")
  end.

MetaCoq Run (printConstant "add" false).
Fail MetaCoq Run (printConstant "nat" false).

Definition six : nat.
  exact (3 + 3).
Qed.
MetaCoq Run (printConstant "six" true).
MetaCoq Run (printConstant "six" false).

MetaCoq Run (t <- tmLemma "foo4" nat;;
             tmDefinition "foo5" (t + t + 2)).
Next Obligation.
  exact 3.
Defined.
Print foo5.

MetaCoq Run (t <- tmLemma "foo44" nat ;;
             qt <- tmQuote t ;;
             t <- tmEval all t ;;
             tmPrint qt ;; tmPrint t).
Next Obligation.
  exact (3+2).
Defined.

End monad.

(** * Meta-programs  *)

Print term.

Check $quote (fun x : nat => x).

Check $unquote (tLam "y" ($quote bool) ($quote (fun x : nat => x))).

Definition tNat := $quote nat.

Definition idNat := $unquote
  (tLam "x" tNat (tRel 0)).
Print idNat.

Check $unquote (tLam "x" ($quote nat) (tRel 0)).

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

Print Mpower'.

Definition Mpower (n : nat) :=
  tLam "x" ($quote nat) (Mpower' n).

Compute Mpower' 3.

Definition power3 := ($unquote (Mpower 3)).
Print power3.

Definition power13 := ($unquote (Mpower 13)).
Print power13.
Print Assumptions power13.

Inductive arith :=
| aPlus : arith -> arith -> arith
| aConst : nat -> arith.

Fixpoint reify (x : term) :=
  match x with
  | tApp c [u; v] =>
      if c == $quote plus
      then tApp ($quote aPlus) [reify u; reify v]
      else tApp ($quote aConst) [x]
  | n => tApp ($quote aConst) [x]
  end.

Goal 4 + (3 + 1) = 2.
Proof.
  match goal with
  | [ |- ?L = _ ] => pose ($unquote (reify ($quote L)))
  end.
Abort.

(** ** Advanced  *)
(** Write automation that unfolds and reduces all constants c in a term, *unless* c : Type, or c : P where P : Prop.
    It suffices to change the tConst case of the function below. Use the auxiliary function defined and checked below.
*)

Definition reduce Σ t := match reduce_opt RedFlags.default Σ [] default_fuel t with Some res => res | _ => t end.
Definition infer_type Σ t := infer (cf := config.default_checker_flags) (F := default_fuel) Σ init_graph [] t.

Check lookup_constant.
Check Universe.is_prop.

Require Import List.

Section fix_Sigma.

Variable Σ : global_env.

Fixpoint simplify_consts (t : term) :=
  match t with
  | tRel n => tRel n
  | tVar id => tVar id
  | tEvar ev args => tEvar ev (map simplify_consts args)
  | tSort s => tSort s
  | tCast t kind v => tCast (simplify_consts t) kind (simplify_consts v)
  | tProd na ty body => tProd na (simplify_consts ty) (simplify_consts body)
  | tLambda na ty body => tLambda na (simplify_consts ty) (simplify_consts body)
  | tLetIn na def def_ty body => tLetIn na (simplify_consts def) (simplify_consts def_ty) (simplify_consts body)
  | tApp f args => tApp (simplify_consts f) (map simplify_consts args)
  | tConst c u =>
      match infer_type Σ (tConst c u) with
      | Checked (tSort _) => tConst c u
      | Checked A =>
          match infer_type Σ A with
          | Checked (tSort univ) => if Universe.is_prop univ then
                                  tConst c u
                                else
                                  match lookup_constant Σ c with
                                  | Some {| cst_body := Some b |} => reduce Σ b
                                  | _ => tConst c u
                                  end
          | Checked K => match lookup_constant Σ c with
                        | Some {| cst_body := Some b |} => reduce Σ b
                        | _ => tConst c u
                        end
          | TypeError E => tConst c u
          end
      | TypeError E => tConst c u
      end
  | tInd ind u => tInd ind u
  | tConstruct ind idx u => tConstruct ind idx u
  | tCase ind p discr brs =>
      let p' := map_predicate id simplify_consts simplify_consts p in
      let brs' := map_branches simplify_consts brs in
      tCase ind p' (simplify_consts discr) brs'
  | tProj proj t => tProj proj (simplify_consts t)
  | tFix mfix idx => tFix (map (map_def simplify_consts simplify_consts) mfix) idx
  | tCoFix mfix idx => tCoFix (map (map_def simplify_consts simplify_consts) mfix) idx
  | tInt i => tInt i
  | tFloat f => tFloat f
  end.

End fix_Sigma.

Definition unfold_comp (p : program) :=
  simplify_consts p.1 p.2.

Definition dont := nat.
Definition alsodont := conj I (fun x : False => x).
Definition do := 3 + 1.

Check $unquote (unfold_comp ($quote_rec (dont, alsodont, do))).
(* expected output: (dont, alsodont, 4) *)
