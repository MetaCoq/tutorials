(* You can ignore the content of this file.

   It provides useful notations and combinators to use in the exercises, but it is not necessary to understand their definition. *)

From MetaCoq.Template Require Export All Checker Reduction.

Notation "'$quote' x" := ltac:((let p y := exact y in
                             quote_term
                             x
                             p)) (at level 0).

Notation "'$run' f" := ltac:(let p y := exact y in
                             run_template_program
                             f
                             p) (at level 0).

Notation "'$quote_rec' x" := ($run (tmQuoteRec x)) (at level 0).

Notation "'$unquote' x" := ltac:((let p y := match y with
                                               existT_typed_term ?T ?b => exact b
                                             end in
                             run_template_program
                             (tmUnquote x)
                             p)) (at level 0).

Notation "'$unquote' x : T" := ($run (tmUnquoteTyped T x)) (at level 0, T at level 100, x at next level).

Definition unfold_toplevel {A} (x : A) :=
  tmBind (tmQuote x) (fun y =>
                        match y with
                        | tConst na _ =>
                            tmEval (unfold na) x
                        | y => tmReturn x
                        end).

Notation "'$Quote' x" := ($run (tmBind (unfold_toplevel x) (tmQuote))) (at level 0).

Definition term_eqb (t1 t2 : term) :=
  @eq_term config.default_checker_flags init_graph t1 t2.

Notation "t == u" := (term_eqb t u) (at level 70).

Open Scope bs.
Open Scope bool.
Open Scope list.

Definition tLam x A b :=
  tLambda {| binder_name := nNamed x; binder_relevance := Relevant |} A b.

Definition tLet x A t b :=
  tLetIn {| binder_name := nNamed x; binder_relevance := Relevant |} t A b.

Require Export Nat.

Notation "'__'" := (hole) (no associativity, at level 0).

