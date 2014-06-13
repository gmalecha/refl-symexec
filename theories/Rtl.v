Inductive bit_vector_op : Set :=
  add_op | sub_op | mul_op | divs_op | divu_op | modu_op | mods_op
| and_op | or_op | xor_op | shl_op | shr_op | shru_op | ror_op | rol_op.

Inductive float_arith_op : Set :=
  fadd_op | fsub_op | fmul_op | fdiv_op.

Inductive test_op : Set := eq_op | lt_op | ltu_op.

(* Ignore floating point for now
(* Constraints on mantissa and exponent widths of floating-point numbers *)
Definition float_width_hyp (ew mw: positive) :=
  Zpos mw + 1 < 2 ^ (Zpos ew - 1).

Definition rounding_mode := Flocq.Appli.Fappli_IEEE.mode.
*)

Axiom int : nat -> Type.
Definition size1 : nat := 1.
Definition size8 : nat := 8.
Axiom location : nat -> Type.
Axiom array : nat -> nat -> Type.
Definition size_addr : nat := 32.

Inductive rtl_exp : nat -> Type :=
| arith_rtl_exp : forall s (b:bit_vector_op)(e1 e2:rtl_exp s), rtl_exp s
| test_rtl_exp : forall s (top:test_op)(e1 e2:rtl_exp s), rtl_exp size1
| if_rtl_exp : forall s (cond:rtl_exp size1) (e1 e2: rtl_exp s), rtl_exp s
| cast_s_rtl_exp : forall s1 s2 (e:rtl_exp s1), rtl_exp s2
| cast_u_rtl_exp : forall s1 s2 (e:rtl_exp s1), rtl_exp s2
| imm_rtl_exp : forall s, int s -> rtl_exp s
| get_loc_rtl_exp : forall s (l:location s), rtl_exp s
| get_array_rtl_exp : forall l s, array l s -> rtl_exp l -> rtl_exp s
| get_byte_rtl_exp : forall (addr:rtl_exp size_addr),  rtl_exp size8
| get_random_rtl_exp : forall s, rtl_exp s.
(*
(* a float has one sign bit, ew bit of exponent, and mw bits of mantissa *)
| farith_rtl_exp : (* floating-point arithmetics *)
    forall (ew mw: positive) (hyp: float_width_hyp ew mw)
           (fop: float_arith_op) (rounding: rtl_exp size2),
      let len := (nat_of_P ew + nat_of_P mw)%nat in
      rtl_exp len -> rtl_exp len -> rtl_exp len
| fcast_rtl_exp : (* cast between floats of different precisions *)
    forall (ew1 mw1 ew2 mw2:positive)
           (hyp1: float_width_hyp ew1 mw1) (hyp2: float_width_hyp ew2 mw2)
           (rounding: rtl_exp size2),
      rtl_exp (nat_of_P ew1 + nat_of_P mw1)%nat ->
      rtl_exp (nat_of_P ew2 + nat_of_P mw2)%nat.
*)

Inductive rtl_instr : Type :=
| set_loc_rtl : forall s (e:rtl_exp s) (l:location s), rtl_instr
| set_array_rtl : forall l s, array l s -> rtl_exp l -> rtl_exp s -> rtl_instr
| set_byte_rtl: forall (e:rtl_exp size8)(addr:rtl_exp size_addr), rtl_instr
(** advance the clock of the oracle so that the next get_random_rtl_exp returns
      a new random bitvalue *)
| advance_oracle_rtl : rtl_instr
| if_rtl : rtl_exp size1 -> rtl_instr -> rtl_instr
| error_rtl : rtl_instr
| trap_rtl : rtl_instr.