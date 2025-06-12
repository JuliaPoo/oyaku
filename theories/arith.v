Require Import egg.Loader.
Require Import Coq.ZArith.ZArith. (* TODO make plugin work even if ZArith is not loaded *)
Require Import Coq.QArith.QArith. (* Add this for rational support *)
Require Import Coq.Strings.String.


Section Arith.

    (* Ltac intro_stuff :=
        assert (1 + 1 = 2) by reflexivity.
        assert (comm_add : forall (a b: Q), a + b = b + a) by admit.
        assert (comm_mult : forall (a b: Q), a * b = b * a) by admit.
        assert (distr_r : forall (a b c: Q), a * (b + c) = a * b + a * c) by admit.
        assert (distr_l : forall (a b c: Q), (b + c) * a = b * a + c * a) by admit.
        assert (distr_r_inv : forall (a b c: Q), a * b + a * c = a * (b + c)) by admit.
        assert (distr_l_inv : forall (a b c: Q), b * a + c * a = (b + c) * a) by admit.
        assert (mult_1_r : forall (a : Q), 1 * a = a) by admit.
        assert (assoc_add : forall (a b c: Q), (a + b) + c = a + (b + c)) by admit.
        assert (assoc_mult : forall (a b c: Q), (a * b) * c = a * (b * c)) by admit.
        assert (pow_intro : forall (a : Q), a * a = a^2) by admit.
        assert (pow_intro_inv : forall (a : Q), a ^ 2 = a * a) by admit. *)

     Context (one_plus_one_eq_two : (1 + 1 = 2)%Q)
            (comm_add : forall (a b: Q), (a + b)%Q = (b + a)%Q)
            (comm_mult : forall (a b: Q), (a * b)%Q = (b * a)%Q)
            (distr_r : forall (a b c: Q), (a * (b + c)%Q)%Q = (a * b)%Q + (a * c)%Q)
            (distr_l : forall (a b c: Q), ((b + c)%Q * a)%Q = (b * a)%Q + (c * a)%Q)
            (distr_r_inv : forall (a b c: Q), ((a * b)%Q + (a * c)%Q)%Q = (a * (b + c)%Q)%Q)
            (distr_l_inv : forall (a b c: Q), ((b * a)%Q + (c * a)%Q)%Q = ((b + c)%Q * a)%Q)
            (mult_1_r : forall (a : Q), (1 * a)%Q = a)
            (assoc_add : forall (a b c: Q), ((a + b)%Q + c)%Q = (a + (b + c)%Q)%Q)
            (assoc_mult : forall (a b c: Q), ((a * b)%Q * c)%Q = (a * (b * c)%Q)%Q)
            (pow_intro : forall (a : Q), (a * a)%Q = (a ^ 2)%Q)
            (pow_intro_inv : forall (a : Q), (a ^ 2)%Q = (a * a)%Q).


    Lemma test_addition: 50 + 50 = 100.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma presentation_1: ((5 - 2) * (4 - (1 * 2))) = 6.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma presentation_2: 
        forall f, (forall x y a b, a * f x + b * f y = f (a * x + b * y))
        -> 2 * f 3 + 4 * f 5 = f 26.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.


    Lemma presentation_3: forall w x y z k, x * y + x * z + w * y + w * z + k = (x + w) * (y + z) + k.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma binomial_test: forall a b n, a ^ 2 + a * b  + b * a + b ^ 2 = n.
    Proof.
        intros.
        egg_simpl_goal 6.
        cbv beta.
    Abort.

    Lemma comm_test: forall a b c d, a + b + c + d + -a + -b + -c + -d = 0.
    Proof.
        intros.





    (* Goal forall x1 x2,
        zero = zero ->
        add x2 (neg x1) = add (add x1 (add x2 (neg x1))) (neg x1).
    Proof.
        intros.
        egg_simpl_goal 6. (* max ffn that occurs is 5 *)
    Qed. *)

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

    Lemma constant_fold_test_3: ((5 - 2)%Q * (4 - (1 * 2)))%Q= 6%Q.
    Proof.
        intros.
        egg_simpl_goal 10.
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

    Lemma egg_sucks_test_1: forall a, a + (-a) = zero.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma egg_sucks_test_2: forall a b, a + b + (-b) + (-a) = zero.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma egg_sucks_test_3: forall a b c, a + (-a) + b + (-b) + c + (-c) = zero.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma egg_sucks_test_4: forall a b c, a + b + c + (-c) + (-b) + (-a) = zero.
    Proof.
        intros.
        egg_simpl_goal 20.
    Abort.
    