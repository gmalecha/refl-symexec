Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Positive.
Require Import ExtLib.Data.Bool.
Require Import Rtl.Rtl.
Require Import MirrorCore.SymEnv.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprLift.

Set Implicit Arguments.
Set Strict Implicit.

Section wp.
  Import MonadNotation.

  Inductive typ :=
  | tyOpaque : positive -> typ
  | tyInt : nat -> typ
  | tyArray : nat -> nat -> typ
  | tyLoc : nat -> typ
  | tyProp
  | tyArr : typ -> typ -> typ
  | tyState.
  Axiom typD : list Type -> typ -> Type.

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
  | fArray_upd : nat -> nat -> func
  | fMem_upd
  | fMem_read
  | fPure : typ -> func
  | fAp : typ -> typ -> func
      (** TODO(gmalecha): These are not going to work! **)
  | fLoc : forall sz, location sz -> func
  | fArray : forall s l, array s l -> func
  | fMemory
  .

  Local Notation "a @ b" := (@App typ func a b) (only parsing, at level 30).

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

  Definition bv_eq_dec : forall a b : bit_vector_op, {a = b} + {a <> b}.
    decide equality.
  Defined.

  Instance bv_op_eq : RelDec (@eq bit_vector_op) :=
  { rel_dec := fun a b => match bv_eq_dec a b with
                            | right _ => false
                            | left _ => true
                          end }.

  Instance func_eq : RelDec (@eq func) :=
  { rel_dec := fun a b =>
       match a , b with
         | fOpaque a , fOpaque b => a ?[ eq ] b
         | fLoc sa la , fLoc sb lb => false (** TODO **)
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
    Inj (fEx t) @ a.
  Definition leq (t : typ) (a b : sexpr) : sprop :=
    Inj (fEq t) @ a @ b.

  Definition array_upd (s l : nat) : sexpr := Inj (fArray_upd s l).

  Definition memory_upd : sexpr := Inj fMem_upd.
  Definition memory_read : sexpr := Inj fMem_read.


  Fixpoint rtl_exp_to_expr {sz : nat} (re : rtl_exp sz)
  : option sexpr.
    refine
      match re in rtl_exp sz with
        | arith_rtl_exp sz o l r =>
          l <- rtl_exp_to_expr _ l ;;
          r <- rtl_exp_to_expr _ r ;;
          ret (Inj (fBVop sz o) @ l @ r)
        | test_rtl_exp sz t l r =>
          l <- rtl_exp_to_expr _ l ;;
          r <- rtl_exp_to_expr _ r ;;
          ret (Inj (fTestop sz t) @ l @ r)
        | if_rtl_exp sz test t f =>
          test <- rtl_exp_to_expr _ test ;;
          t <- rtl_exp_to_expr _ t ;;
          f <- rtl_exp_to_expr _ f ;;
          ret (Inj (fIf (tyInt sz)) @ test @ t @ f)
        | cast_s_rtl_exp s1 s2 e =>
          e <- rtl_exp_to_expr _ e ;;
          ret (mkCast true s1 s2 @ e)
        | cast_u_rtl_exp s1 s2 e =>
          e <- rtl_exp_to_expr _ e ;;
          ret (mkCast false s1 s2 @ e)
        | imm_rtl_exp _ val =>
          ret (mkConst val)
        | get_byte_rtl_exp a =>
          a <- rtl_exp_to_expr _ a ;;
          ret (memory_read @ Inj fMemory @ a)
        | _ => None
      end%monad.
  Defined.

  (** TODO(gmalecha): These look like they need to be typed folds!
   ** That is the only way that I'm going to get the ability to write
   ** abstraction correctly.
   **)
  Section replace_location.
    Variables (sz : nat) (l : location sz).

    Fixpoint replace_location_sexpr (w : sexpr) (p : sprop) : sprop :=
      match p with
        | Var v => Var v
        | Inj i =>
          if i ?[ eq ] (injLoc l) then w
          else Inj i
        | App a b =>
          App (replace_location_sexpr w a) (replace_location_sexpr w b)
        | Abs t a =>
          Abs t (replace_location_sexpr (lift 0 1 w) a)
        | UVar u => UVar u
      end.
  End replace_location.

  Section replace_array.
(*    Variables (s l : nat) (a : array s l).  *)
    Variable for_inj : nat -> func -> sexpr.

    Fixpoint replace_inj_sexpr (under : nat) (p : sexpr) : sexpr :=
      match p with
        | Var v => Var v
        | Inj i => for_inj under i
        | App a b =>
          App (replace_inj_sexpr under a) (replace_inj_sexpr under b)
        | Abs t a =>
          Abs t (replace_inj_sexpr (S under) a)
        | UVar u => UVar u
      end.
  End replace_array.

  Fixpoint wp_rtl_instr (s : rtl_instr) (p : sprop)
  : option sprop.
  refine
    match s return option sprop with
      | set_loc_rtl s e l =>
        e_e <- rtl_exp_to_expr e ;;
        ret (replace_location_sexpr l e_e p)
      | set_array_rtl l s a x v =>
        x_e <- rtl_exp_to_expr x ;;
        v_e <- rtl_exp_to_expr v ;;
        None  (*
        ret (replace_inj_sexpr
               (fun under i =>
                  if i ?[ eq ] (fArray a) then
                    App (App (App (array_upd l s) (Inj i))
                             (lift 0 under x_e))
                        (lift 0 under v_e)
                  else
                    Inj i)
               0 p) *)
      | set_byte_rtl e a =>
        a_e <- rtl_exp_to_expr a ;;
        e_e <- rtl_exp_to_expr e ;;
        None (*
        ret (land (is_writeable (Inj the_memory) a_e)
                  (replace_inj_sexpr
                     (fun under i =>
                        if i ?[ eq ] the_memory then
                          memory_upd @ Inj the_memory @ lift 0 under a_e @ lift 0 under e_e
                        else Inj i)
                     0 p)) *)
      | advance_oracle_rtl => ret p
      | if_rtl t e =>
        test_e <- rtl_exp_to_expr t ;;
        tr_e <- wp_rtl_instr e p ;;
        ret (lif tyProp test_e tr_e p)
      | error_rtl => ret lfalse
      | trap_rtl => ret lfalse
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
                   (fun rs p => (rs,p))
                   (fun p => (nil, p)).

  Eval compute in
      fun (P : int size_addr) (X : int 8) (L : location 8) =>
        wp_rtl_instrs (set_loc_rtl _ (get_byte_rtl_exp (imm_rtl_exp _ P)) L
                       :: nil)
                      (leq (tyInt 8) (mkConst X)
                           (memory_read @ Inj fMemory @ mkConst P)).
End wp.

(** NOTES:
 ** - Extensibility here enables us to do a lot more extensible reasoning
 ** - At the same time, it is likely to add some overhead b/c it is allowing
 **   ill-typed terms.
 ** - Overall: More expressive, but since this problem is so constrained it
 **   might not matter.
 **)