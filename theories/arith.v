Require Import egg.Loader.
Require Import Coq.ZArith.ZArith. (* TODO make plugin work even if ZArith is not loaded *)
Require Import Coq.QArith.QArith. (* Add this for rational support *)
Require Import Coq.Strings.String.


    Section Arith.
    
    Context (Expr: Type)
            (Var: string -> Expr)
            (add: Expr -> Expr -> Expr)
            (mul: Expr -> Expr -> Expr)
            (div: Expr -> Expr -> Expr)
            (neg: Expr -> Expr)
            (int_pow: Expr -> Z -> Expr)
            (zero: Expr)
            (one: Expr)
            (two: Expr)
            (rat_lit: Q -> Expr)
            (rat_add: forall (p q: Q), add (rat_lit p) (rat_lit q) = rat_lit (p + q))
            (rat_mul: forall (p q: Q), mul (rat_lit p) (rat_lit q) = rat_lit (p * q))
            (rat_neg: forall (p: Q), neg (rat_lit p) = rat_lit (- p))
            (rat_div: forall (p q: Q), q <> 0%Q -> div (rat_lit p) (rat_lit q) = rat_lit (p / q))
            (rat_zero: rat_lit 0 = zero)
            (rat_zero_inv: zero = rat_lit 0)
            (rat_one: rat_lit 1 = one)
            (rat_one_inv: one = rat_lit 1)
            (rat_two: rat_lit 2 = two)
            (rat_two_inv: two = rat_lit 2)
            (add_0_l : forall x, add zero x = x)
            (add_0_r : forall x, add x zero = x)
            (add_comm : forall a b, add a b = add b a)
            (add_to_left_assoc : forall a b c, add a (add b c) = add (add a b) c)
            (add_to_right_assoc : forall a b c, add (add a b) c = add a (add b c))
            (add_to_left_assoc_inv : forall a b c, add (add a b) c = add a (add b c))
            (add_to_right_assoc_inv : forall a b c, add a (add b c) = add (add a b) c)
            (add_opp : forall a, add a (neg a) = zero)
            (add_copy : forall a, add a a = mul two a)
            (mul_1_l : forall x, mul one x = x)
            (mul_0_l : forall x, mul zero x = zero)
            (mul_comm : forall a b, mul a b = mul b a)
            (mul_to_left_assoc : forall a b c, mul a (mul b c) = mul (mul a b) c)
            (mul_distr_l : forall a b c, mul a (add b c) = add (mul a b) (mul a c))
            (mul_distr_r : forall a b c, mul (add a b) c = add (mul a c) (mul b c))
            (mul_distr_l_inv : forall a b c, add (mul a c) (mul b c) = mul (add a b) c)
            (mul_distr_r_inv : forall a b c, add (mul a b) (mul a c) = mul a (add b c))
            (mul_inverse : forall a, (a <> zero) -> mul a (div one a) = one)
            (mul_integral_domain : forall a b, (a <> zero) -> (b <> zero) -> (mul a b <> zero))
            (neg_move : forall a b, mul (neg a) b = neg (mul a b))
            (neg_move_inv : forall a b, neg (mul a b) = mul (neg a) b)
            (neg_comm : forall a b, mul (neg a) b = mul a (neg b))
            (neg_idem : forall a, neg (neg a) = a)
            (div_1 : forall a, (a <> zero) -> div a a = one)
            (frac_mul : forall a b c d, mul (div a b) (div c d) = div (mul a c) (mul b d))
            (frac_mul_inv : forall a b c d, div (mul a c) (mul b d) = mul (div a b) (div c d))
            (int_pow_1 : forall a, a = (int_pow a 1%Z))
            (ing_pow_1_inv : forall a, int_pow a 1%Z = a)
            (int_pow_0 : forall a, int_pow a 0%Z = one)
            (int_pow_0_inv : forall a, one = int_pow a 0%Z)
            (int_pow_neg : forall a n, int_pow a ((-n)%Z) = div one (int_pow a n))
            (int_pow_pos : forall a n, int_pow a n = mul (int_pow a 1%Z) (int_pow a (n - 1)%Z))
            (int_pow_1_l : forall a, int_pow one a = one)
            (int_pow_0_l : forall a, int_pow zero a = zero)
            (int_pow_a_a : forall a, (mul a a) = int_pow a 2%Z)
            .
            (* (int_pow_mul : forall a n m, (mul (int_pow a m) (int_pow a n) = int_pow a (m + n)%Z)). *)

    Notation "x + y" := (add x y) (at level 50, left associativity).
    Notation "x * y" := (mul x y) (at level 40, left associativity).
    Notation "x / y" := (div x y) (at level 40, left associativity).
    Notation "- x" := (neg x) (at level 35, right associativity).
    Notation "x ^ z" := (int_pow x z) (at level 30, right associativity).
    Notation "x ~" := (rat_lit x) (at level 20, left associativity).



    Lemma test_addition: (50 + 50)%Q = 100%Q.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Goal forall x1 x2,
        zero = zero ->
        add x2 (neg x1) = add (add x1 (add x2 (neg x1))) (neg x1).
    Proof.
        intros.
        egg_simpl_goal 6. (* max ffn that occurs is 5 *)
    Qed.

    (* Lemma mul_0_rat_lit_l: forall a, mul (rat_lit 0) a = zero.
    Proof.
        intros.
        Set Egg Misc Tracing.
        egg_simpl_goal 5.
        egg_simpl_goal 5.
        cbv beta.
        reflexivity. *)

    Lemma square: forall a, a * a = a ^ 2.
    Proof.
        intros.
        egg_simpl_goal 5.
    Qed.

    Lemma square_with_auto: forall a, (mul a a) = a ^ 2.
    Proof.
        intros.
        auto.
    Qed.

    Lemma binomial_test: forall a b, (a + b)^2 = a * a + rat_lit(2) * a * b + b * b.
    Proof.
        intros.
        egg_simpl_goal 50.
    Qed.

    Lemma constant_fold_test_1: (2 + 3)%Q = 5%Q.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma constant_fold_test_2: (4 * (2 + 1))%Q = 12%Q.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma hard_1: forall a b c d, a * b + a * c + d * b + d * c = (a + d) * (b + c).
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma hard_2: forall w x y z k, x * y + x * z + w * y + w * z + k = (x + w) * (y + z) + k.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma hard_3: forall a b c, (a + b + c)^2 = a^2 + b^2 + c^2 + rat_lit(2) * (a * b + a * c + b * c).
    Proof.
        intros.
        egg_simpl_goal 5.
    Abort.

    Lemma hard_4: forall a b, (rat_lit(2) * a + b)^2 = rat_lit(4) * a^2 + rat_lit(4) * a * b + b^2.
    Proof.
        intros.
        egg_simpl_goal 500.
        cbv beta.
    Abort.

    Lemma hard_4_split_1: forall a b, (rat_lit(2) * a + b)^2 = (rat_lit(2) * a + b) * (rat_lit(2) * a + b).
    Proof.
        intros.
        egg_simpl_goal 5.
    Qed.

    Lemma hard_4_split_2: forall a b, (rat_lit(2) * a + b) * (rat_lit(2) * a + b) = rat_lit(2) * a * (rat_lit(2) * a + b) + b * (rat_lit(2) * a + b).
    Proof.
        intros.
        egg_simpl_goal 5.
    Qed.

    Lemma hard_4_split_3: forall a b, rat_lit(2) * a * (rat_lit(2) * a + b) + b * (rat_lit(2) * a + b) = rat_lit(2) * a * (rat_lit(2) * a + b) + rat_lit(2) * b * a + b^2.
    Proof.
        intros.
        egg_simpl_goal 5.
    Qed.

    Lemma hard_4_split_4: forall a b, rat_lit(2) * a * (rat_lit(2) * a + b) + rat_lit(2) * b * a + b^2 = rat_lit(2) * rat_lit(2) * a^2 + rat_lit(2) * a * b + rat_lit(2) * a * b + b^2.
    Proof.
        intros.
        egg_simpl_goal 50.
    Qed.

    Lemma hard_4_split_5: forall a b, rat_lit(2) * rat_lit(2) * a^2 + rat_lit(2) * a * b + rat_lit(2) * a * b + b^2 = rat_lit(4) * a^2 + rat_lit(4) * a * b + b^2.
    Proof.
        intros.
        egg_simpl_goal 50.
    Qed.