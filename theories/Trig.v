(* From mathcomp Require Import ssreflect ssrfun ssrbool eqtype. *)
Require Import egg.Loader.
Require Import Coq.ZArith.ZArith. (* TODO make plugin work even if ZArith is not loaded *)
Require Import Coq.QArith.QArith. (* Add this for rational support *)
Require Import Coq.Strings.String.

Section TestStuff.
    Context (Expr: Type)
            (Var: string -> Expr)
            (add: Expr -> Expr -> Expr)
            (mul: Expr -> Expr -> Expr)
            (div: Expr -> Expr -> Expr)
            (neg: Expr -> Expr)
            (int_pow: Expr -> Z -> Expr)
            (sin: Expr -> Expr)
            (cos: Expr -> Expr)
            (tan: Expr -> Expr)
            (csc: Expr -> Expr)
            (sec: Expr -> Expr)
            (cot: Expr -> Expr)
            (zero: Expr)
            (one: Expr)
            (two: Expr)
            (pi: Expr)
            (rat_lit: Q -> Expr)
            (rat_add: forall (p q: Q), add (rat_lit p) (rat_lit q) = rat_lit (p + q))
            (rat_mul: forall (p q: Q), mul (rat_lit p) (rat_lit q) = rat_lit (p * q))
            (rat_neg: forall (p: Q), neg (rat_lit p) = rat_lit (- p))
            (rat_div: forall (p q: Q), q <> 0%Q -> div (rat_lit p) (rat_lit q) = rat_lit (p / q))
            (rat_zero: rat_lit 0 = zero)
            (rat_one: rat_lit 1 = one)
            (rat_two: rat_lit 2 = two)
            (add_0_l : forall x, add zero x = x)
            (add_comm : forall a b, add a b = add b a)
            (add_to_left_assoc : forall a b c, add a (add b c) = add (add a b) c)
            (add_to_right_assoc : forall a b c, add (add a b) c = add a (add b c))
            (add_to_left_assoc_inv : forall a b c, add (add a b) c = add a (add b c))
            (add_to_right_assoc_inv : forall a b c, add a (add b c) = add (add a b) c)
            (add_opp : forall a, add a (neg a) = zero)
            (mul_1_l : forall x, mul one x = x)
            (mul_0_l : forall x, mul zero x = zero)
            (mul_comm : forall a b, mul a b = mul b a)
            (mul_to_left_assoc : forall a b c, mul a (mul b c) = mul (mul a b) c)
            (mul_distr_l : forall a b c, mul a (add b c) = add (mul a b) (mul a c))
            (mul_distr_r : forall a b c, mul (add a b) c = add (mul a c) (mul b c))
            (mul_distr_l_inv : forall a b c, add (mul a c) (mul b c) = mul (add a b) c)
            (mul_distr_r_inv : forall a b c, add (mul a b) (mul a c) = mul a (add b c))
            (mul_inverse : forall a, (a <> zero) -> mul a (div one a) = one)
            (div_1 : forall a, (a <> zero) -> div a a = one)
            (frac_mul : forall a b c d, mul (div a b) (div c d) = div (mul a c) (mul b d))
            (frac_mul_inv : forall a b c d, div (mul a c) (mul b d) = mul (div a b) (div c d))
            (int_pow_1 : forall a, a = (int_pow a 1%Z))
            (int_pow_0 : forall a, int_pow a 0%Z = one)
            (int_pow_neg : forall a n, int_pow a ((-n)%Z) = div one (int_pow a n))
            (int_pow_pos : forall a n, int_pow a n = mul (int_pow a 1%Z) (int_pow a (n - 1)%Z))
            (int_pow_1_l : forall a, int_pow one a = one)
            (int_pow_0_l : forall a, int_pow zero a = zero)
            (int_pow_a_a : forall a, (mul a a) = int_pow a 2%Z)
            (squareIdent : forall a, add (int_pow (sin a) 2%Z) (int_pow (cos a) 2%Z) = one)
            (TR1a : forall a, sec a = div one (cos a))
            (TR1b : forall a, csc a = div one (sin a))
            (TR2a : forall a, tan a = div (sin a) (cos a))
            (TR2b : forall a, cot a = div (cos a) (sin a))
            (TR5 : forall a, (int_pow (sin a) 2%Z) = (add (one) (neg (int_pow (cos a) 2%Z))))
            (TR6 : forall a, (int_pow (cos a) 2%Z) = (add (one) (neg (int_pow (sin a) 2%Z))))
            (TR10a : forall a b, sin (add a b) = add (mul (sin a) (cos b)) (mul (cos a) (sin b)))
            (TR10b : forall a b, sin (add a (neg b)) = add (mul (sin a) (cos b)) (neg (mul (cos a) (sin b))))
            (TR10c : forall a b, cos (add a b) = add (mul (cos a) (cos b)) (neg (mul (sin a) (sin b))))
            (TR10d : forall a b, cos (add a (neg b)) = add (mul (cos a) (cos b)) (mul (sin a) (sin b)))
            .
            (* (int_pow_mul : forall a n m, (mul (int_pow a m) (int_pow a n) = int_pow a (m + n)%Z)). *)
            

    (* Lemma trig_test_5: forall a, add (mul (two) (int_pow (sin a) 2%Z)) (mul (two) (int_pow (cos a) 2%Z)) = two.
    Proof.
        intros.
        Set Egg Misc Tracing.
        egg_simpl_goal 0.
        cbv beta.
    Abort. *)

    Goal forall x1 x2,
        zero = zero ->
        add x2 (neg x1) = add (add x1 (add x2 (neg x1))) (neg x1).
    Proof.
        intros.
        egg_simpl_goal 5. (* max ffn that occurs is 5 *)
        cbv beta.
        reflexivity.
    Qed.

    Lemma add_0_r: forall x, add x zero = x.
    Proof.
        intros.
        egg_simpl_goal 3.
        cbv beta.
        reflexivity.
    Qed.

    (* Lemma mul_0_rat_lit_l: forall a, mul (rat_lit 0) a = zero.
    Proof.
        intros.
        Set Egg Misc Tracing.
        egg_simpl_goal 5.
        egg_simpl_goal 5.
        cbv beta.
        reflexivity. *)

    Lemma square: forall a, (mul a a) = int_pow a 2%Z.
    Proof.
        intros.
        egg_simpl_goal 5.
        cbv beta.
        reflexivity.
    Qed.

    Lemma trig_test: forall a, add (int_pow (sin a) 2%Z) (int_pow (cos a) 2%Z) = one.
    Proof.
        intros.
        egg_simpl_goal 5.
        cbv beta.
        reflexivity.
    Qed.

    Lemma trig_test2: forall a, add (mul (sin a) (sin a)) (mul (cos a) (cos a)) = one.
    Proof.
        intros.
        egg_simpl_goal 5.
        cbv beta.
        reflexivity.
    Qed.

    Lemma trig_test_3: forall a, mul (sin a) (add (sin a) (cos a)) = add (int_pow (sin a) 2%Z) (mul (sin a) (cos a)).
    Proof.
        intros.
        egg_simpl_goal 5.
        cbv beta.
        reflexivity.
    Qed.

    Lemma trig_test_4: forall a, add (add (int_pow (sin a) 2%Z) (mul (sin a) (cos a))) (neg (mul (sin a) (cos a))) = int_pow (sin a) 2%Z.
    Proof.
        intros.
        egg_simpl_goal 5.
        cbv beta.
        reflexivity.
    Qed.

    

    Lemma trig_test_6: forall a, add (add (mul (sin a) (add (sin a) (cos a))) (neg (mul (sin a) (cos a)))) (int_pow (cos a) 2%Z) = one.
    Proof.
        intros.
        egg_simpl_goal 1.
        cbv beta.
        reflexivity.
    Qed.

    Lemma trig_test_7: forall a, add (div (sin a) (cos a)) (div (cos a) (sin a)) = add (tan a) (cot a).
    Proof.
        intros.
        egg_simpl_goal 1.
        cbv beta.
        reflexivity.
    Qed.
    
    Lemma mul_0_rat_lit_l: forall a, mul (rat_lit 0) a = zero.
    Proof.
        intros.
        egg_simpl_goal 5.
        cbv beta.
        reflexivity.
    Qed.





    
    