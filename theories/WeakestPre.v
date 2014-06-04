Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Option.
Require Import Rtl.Rtl.
Require Import MirrorCore.Lambda.Expr.
Require Import MirrorCore.Lambda.ExprLift.

Set Implicit Arguments.
Set Strict Implicit.

Section wp.
  Import MonadNotation.

  Variable typ : Type.
  Variable typD : list Type -> typ -> Type.

  Definition func : Type := ({ sz : nat & location sz } + nat)%type.

  Local Notation "a @ b" := (@App typ func a b) (only parsing, at level 30).

  Instance func_eq : RelDec (@eq func).
  Admitted.

  Definition sprop := expr typ func.
  Definition sexpr := expr typ func.

  Axiom int_typ : nat -> typ.
  Axiom array_typ : nat -> nat -> typ.

  Definition injLoc {sz : _} (l : location sz) : func :=
    inl (@existT _ _ sz l).

  Definition injArray (s l : _) (a : array s l) : func.
  Admitted.

  Definition bv_op (sz : nat) (o : bit_vector_op) : sexpr.
  Admitted.

  Definition test_op (sz : nat) (o : test_op) : sexpr.
  Admitted.

  Definition mkIf (a b c : sexpr) : sexpr.
  Admitted.

  Axiom mkCast : bool -> nat -> nat -> sexpr.
  Axiom mkConst : forall sz, int sz -> sexpr.

  Axiom lfalse : sprop.
  Axiom is_readable : sexpr -> sexpr -> sprop.
  Axiom is_writeable : sexpr -> sexpr -> sprop.
  Axiom land : sprop -> sprop -> sprop.
  Axiom lor : sprop -> sprop -> sprop.
  Axiom is_true : sexpr -> sprop.
  Axiom lneg : sprop -> sprop.
  Axiom lex : typ -> sprop -> sprop.
  Axiom leq : typ -> sexpr -> sexpr -> sprop.
  Axiom array_upd : nat -> nat -> sexpr.
  Axiom the_memory : func.
  Axiom memory_upd : sexpr.
  Axiom memory_read : sexpr.

  Fixpoint rtl_exp_to_expr {sz : nat} (re : rtl_exp sz)
  : option sexpr.
    refine
      match re in rtl_exp sz with
        | arith_rtl_exp sz o l r =>
          l <- rtl_exp_to_expr _ l ;;
          r <- rtl_exp_to_expr _ r ;;
          ret (App (App (bv_op sz o) l) r)
        | test_rtl_exp sz t l r =>
          l <- rtl_exp_to_expr _ l ;;
          r <- rtl_exp_to_expr _ r ;;
          ret (App (App (test_op sz t) l) r)
        | if_rtl_exp sz test t f =>
          test <- rtl_exp_to_expr _ test ;;
          t <- rtl_exp_to_expr _ t ;;
          f <- rtl_exp_to_expr _ f ;;
          ret (mkIf test t f)
        | cast_s_rtl_exp s1 s2 e =>
          e <- rtl_exp_to_expr _ e ;;
          ret (App (mkCast true s1 s2) e)
        | cast_u_rtl_exp s1 s2 e =>
          e <- rtl_exp_to_expr _ e ;;
          ret (App (mkCast false s1 s2) e)
        | imm_rtl_exp _ val =>
          ret (mkConst val)
        | get_byte_rtl_exp a =>
          a <- rtl_exp_to_expr _ a ;;
          ret (memory_read @ Inj the_memory @ a)
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


  (** TODO(gmalecha): array and memory operations **)
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
        ret (replace_inj_sexpr
               (fun under i =>
                  if i ?[ eq ] (injArray a) then
                    App (App (App (array_upd l s) (Inj i))
                             (lift 0 under x_e))
                        (lift 0 under v_e)
                  else
                    Inj i)
               0 p)
      | set_byte_rtl e a =>
        a_e <- rtl_exp_to_expr a ;;
        e_e <- rtl_exp_to_expr e ;;
        ret (land (is_writeable (Inj the_memory) a_e)
                  (replace_inj_sexpr
                     (fun under i =>
                        if i ?[ eq ] the_memory then
                          memory_upd @ Inj the_memory @ lift 0 under a_e @ lift 0 under e_e
                        else Inj i)
                     0 p))
      | advance_oracle_rtl => ret p
      | if_rtl t e =>
        test_e <- rtl_exp_to_expr t ;;
        tr_e <- wp_rtl_instr e p ;;
        ret (lor (land (is_true test_e) tr_e)
                 (land (lneg (is_true test_e)) p))
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
        wp_rtl_instrs (cons (set_loc_rtl _ (get_byte_rtl_exp (imm_rtl_exp _ P)) L) nil)
                      (leq (int_typ 8) (mkConst X)
                           (memory_read @ Inj the_memory @ mkConst P)).
End wp.

(** NOTES:
 ** - Extensibility here enables us to do a lot more extensible reasoning
 ** - At the same time, it is likely to add some overhead b/c it is allowing
 **   ill-typed terms.
 ** - Overall: More expressive, but since this problem is so constrained it
 **   might not matter.
 **)