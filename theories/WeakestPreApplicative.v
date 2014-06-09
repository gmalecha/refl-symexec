Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.Bool.
Require Import Rtl.Rtl.
Require Import MirrorCore.ExprI.
Require Import MirrorCore.SymEnv.
Require Import MirrorCore.Lambda.TypesI2.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprLift.
Require Import MirrorCore.Lambda.Red.

Set Implicit Arguments.
Set Strict Implicit.

Section wp.
  Import MonadNotation.

  Axiom state : Type.

  Inductive typ :=
  | tyOpaque : positive -> typ
  | tyInt : nat -> typ
  | tyArray : nat -> nat -> typ
  | tyLoc : nat -> typ
  | tyProp
  | tyArr : typ -> typ -> typ
  | tyState.


  Fixpoint typD (t : typ) : Type :=
    match t with
      | tyOpaque _ => Empty_set
      | tyInt n => int n
      | tyArray s l => array s l
      | tyLoc n => location n
      | tyProp => Prop
      | tyArr a b => typD a -> typD b
      | tyState => state
    end.

  Definition typ_eq_dec : forall (a b : typ), {a = b} + {a <> b}.
    repeat decide equality.
  Defined.

  Instance typ_eq : RelDec (@eq typ) :=
  { rel_dec := fun a b =>
       match a , b with
         | tyOpaque a , tyOpaque b => a ?[ eq ] b
         | tyInt a , tyInt b => a ?[ eq ] b
         | tyArray a b , tyArray c d =>
           if a ?[ eq ] c then b ?[ eq ] d else false
         | tyLoc a , tyLoc b => a ?[ eq ] b
         | tyProp , tyProp => true
         | tyState , tyState => true
         | _ , _ => false
       end }.


  Local Instance RType_typ : RType :=
  { typ := typ
  ; typD := fun _ => typD
  ; type_cast := fun _ a b => match typ_eq_dec a b with
                                | left pf => Some pf
                                | right _ => None
                              end
  ; type_weaken := fun _ _ x => x
  }.


  Inductive func : Type :=
  | fOpaque : positive -> func
  | fBVop : nat -> bit_vector_op -> func
  | fTestop : nat -> test_op -> func
  | fIf : typ -> func
  | fCast : bool -> nat -> nat -> func
  | fConst : forall sz, int sz -> func
  | fReadable | fWriteable | fAnd | fOr | fTrue | fFalse
  | fEx : typ -> func
  | fEq : typ -> func
  | fLoc_upd : forall sz, location sz -> func
  | fArray_upd : nat -> nat -> func
  | fMem_upd
    (** these are from applicative **)
  | fPure : typ -> func
  | fAp : typ -> typ -> func
    (** these are selectors **)
  | fLoc : forall sz, location sz -> func
  | fArray : forall s l, array s l -> func
  | fMem_read
  | fRandom : nat -> func
  .

  Local Notation "a @ b" := (@App typ func a b) (at level 30).


  Definition bv_eq_dec : forall a b : bit_vector_op, {a = b} + {a <> b}.
    decide equality.
  Defined.

  Definition loc_eq a (la : location a) b (lb : location b)
  : {@existT _ _ a la = @existT _ _ b lb} + {@existT _ _ a la <> @existT _ _ b lb}.
  Admitted.

  Instance bv_op_eq : RelDec (@eq bit_vector_op) :=
  { rel_dec := fun a b => match bv_eq_dec a b with
                            | right _ => false
                            | left _ => true
                          end }.

  Instance func_eq : RelDec (@eq func) :=
  { rel_dec := fun a b =>
       match a , b with
         | fOpaque a , fOpaque b => a ?[ eq ] b
         | fLoc sa la , fLoc sb lb => if loc_eq la lb then true else false
         | fArray sa la aa , fArray sb lb ab => false (** TODO **)
         | fBVop sa ba , fBVop sb bb =>
           if sa ?[ eq ] sb then ba ?[ eq ] bb else false
         | fIf t , fIf u => t ?[ eq ] u
         | fCast z a b , fCast w c d =>
           if z ?[ eq ] w then
             if a ?[ eq ] c then b ?[ eq ] d else false
           else false
         | fConst sa ia , fConst sb ib => false
         | _ , _ => false
       end }.

  Definition sprop := expr typ func.
  Definition sexpr := expr typ func.

  Definition injLoc {sz : _} (l : location sz) : func :=
    fLoc l.

  Definition mkCast (signed : bool) (from to : nat) : sexpr :=
    Inj (fCast signed from to).
  Definition mkConst (sz : _) (val : int sz) : sexpr :=
    Inj (fConst val).

  Definition lfalse : sprop := Inj fFalse.
  Definition ltrue : sprop := Inj fTrue.
  Definition is_readable (a b : sexpr) : sprop :=
    Inj fReadable @ a @ b.
  Definition is_writeable (a b : sexpr) : sprop :=
    Inj fWriteable @ a @ b.
  Definition land (a b : sprop) : sprop :=
    Inj fAnd @ a @ b.
  Definition lor (a b : sprop) : sprop :=
    Inj fOr @ a @ b.
  Definition is_true (a : sexpr) : sprop :=
    Inj (fIf (tyInt 1)) @ a @ ltrue @ lfalse.
  Definition lif (t : typ) (a : sexpr) (b c : sprop) : sprop :=
    Inj (fIf t) @ a @ b @ c.
  Definition lex (t : typ) (a : sprop) : sprop :=
    Inj (fEx t) @ (Abs t a).
  Definition leq (t : typ) (a b : sexpr) : sprop :=
    Inj (fEq t) @ a @ b.

  Definition array_upd (s l : nat) : sexpr := Inj (fArray_upd s l).

  Definition memory_upd : sexpr := Inj fMem_upd.
  Definition memory_read : sexpr := Inj fMem_read.

  Section rtl_expr_to_expr.
    Variable state : sexpr.

    Fixpoint rtl_exp_to_expr {sz : nat} (re : rtl_exp sz)
    : option sexpr :=
      match re in rtl_exp sz with
        | arith_rtl_exp sz o l r =>
          l <- rtl_exp_to_expr l ;;
          r <- rtl_exp_to_expr r ;;
          ret (Inj (fBVop sz o) @ l @ r)
        | test_rtl_exp sz t l r =>
          l <- rtl_exp_to_expr l ;;
          r <- rtl_exp_to_expr r ;;
          ret (Inj (fTestop sz t) @ l @ r)
        | if_rtl_exp sz test t f =>
          test <- rtl_exp_to_expr test ;;
          t <- rtl_exp_to_expr t ;;
          f <- rtl_exp_to_expr f ;;
          ret (Inj (fIf (tyInt sz)) @ test @ t @ f)
        | cast_s_rtl_exp s1 s2 e =>
          e <- rtl_exp_to_expr e ;;
          ret (mkCast true s1 s2 @ e)
        | cast_u_rtl_exp s1 s2 e =>
          e <- rtl_exp_to_expr e ;;
          ret (mkCast false s1 s2 @ e)
        | imm_rtl_exp _ val =>
          ret (mkConst val)
        | get_byte_rtl_exp a =>
          a <- rtl_exp_to_expr a ;;
          ret (memory_read @ state @  a)
        | get_loc_rtl_exp s l =>
          ret (Inj (fLoc l) @ state)
        | get_array_rtl_exp l s a e =>
          e <- rtl_exp_to_expr e ;;
          ret (Inj (fArray a) @ state @ e)
        | get_random_rtl_exp n =>
          ret (Inj (fRandom n) @ state)
      end%monad.
  End rtl_expr_to_expr.

  (** Normalized:
   ** let P := .... in
   ** \ s . ex a,b.. , P s a b ...
   **)

  (** [p] is a value of type [state -> prop] **)
  Fixpoint wp_rtl_instr (s : rtl_instr) (p : sprop)
  : option sprop.
  refine
    match s return option sprop with
      | set_loc_rtl s e l =>
        e_e <- rtl_exp_to_expr (Var 0) e ;;
        ret (Abs tyState (p @ (Inj (fLoc_upd l) @ e_e @ Var 0)))
      | set_array_rtl l s a x v =>
        x_e <- rtl_exp_to_expr (Var 0) x ;;
        v_e <- rtl_exp_to_expr (Var 0) v ;;
        ret (Abs tyState (p @ (Inj (fArray_upd l s) @ x_e @ v_e @ Var 0)))
      | set_byte_rtl e a =>
        a_e <- rtl_exp_to_expr (Var 0) a ;;
        e_e <- rtl_exp_to_expr (Var 0) e ;;
        ret (Abs tyState (land (is_writeable (Var 0) a_e)
                               (p @ (Inj fMem_upd @ a_e @ e_e @ Var 0))))
      | advance_oracle_rtl => ret p
      | if_rtl t e =>
        test_e <- rtl_exp_to_expr (Var 0) t ;;
        tr_e <- wp_rtl_instr e p ;;
        ret (Abs tyState (lif tyProp
                              (test_e @ Var 0)
                              (tr_e @ Var 0)
                              (p @ Var 0)))
      | error_rtl => ret (Abs tyState lfalse)
      | trap_rtl => ret (Abs tyState lfalse)
    end%monad.
  Defined.

  Fixpoint wp_rtl_instrs' {T} (s : list rtl_instr) (p : sprop)
           (fail : list rtl_instr -> sprop -> T)
           (succeed : sprop -> T) {struct s}
  : T :=
    match s with
      | nil => succeed p
      | cons s ss =>
        wp_rtl_instrs' ss p
                       (fun rs => fail (cons s rs))
                       (fun p =>
                          match wp_rtl_instr s p with
                            | None => fail (cons s nil) p
                            | Some p' => succeed p'
                          end)
    end.

  Definition wp_rtl_instrs (s : list rtl_instr) (p : sprop)
  : list rtl_instr * sprop :=
    wp_rtl_instrs' s p
                   (fun rs p => (rs, beta_all nil nil p))
                   (fun p => (nil, beta_all nil nil p)).

  Time Eval vm_compute in
      fun (P : _) (X : int 8) (L : location 8) =>
        wp_rtl_instrs (set_loc_rtl _ (get_byte_rtl_exp (get_loc_rtl_exp _ P)) L
                       :: nil)
                      (Abs tyState (leq (tyInt 8) (mkConst X)
                                        (memory_read @ Var 0 @ (Inj (fLoc P) @ Var 0)))).

End wp.

(** NOTES:
 ** - Extensibility here enables us to do a lot more extensible reasoning
 ** - At the same time, it is likely to add some overhead b/c it is allowing
 **   ill-typed terms.
 ** - Overall: More expressive, but since this problem is so constrained it
 **   might not matter.
 **)
