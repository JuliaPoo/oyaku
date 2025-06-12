Require Import egg.Loader.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
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
            (add_opp_neg_one: forall a: Expr, mul (rat_lit (-1)) a = neg a)
            (add_copy : forall a, add a a = mul two a)
            (mul_1_l : forall x, mul one x = x)
            (mul_0_l : forall x, mul zero x = zero)
            (mul_comm : forall a b, mul a b = mul b a)
            (mul_to_left_assoc : forall a b c, mul a (mul b c) = mul (mul a b) c)
            (mul_to_right_assoc : forall a b c, mul (mul a b) c = mul a (mul b c))
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
            (frac_assoc : forall a b c, mul a (div b c) = div (mul a b) c)
            (frac_assoc_inv : forall a b c, div (mul a b) c = mul a (div b c))
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
            (squareIdent : forall a, add (int_pow (sin a) 2%Z) (int_pow (cos a) 2%Z) = one)
            (TR1a : forall a, sec a = div one (cos a))
            (TR1b : forall a, csc a = div one (sin a))
            (TR2a : forall a, tan a = div (sin a) (cos a))
            (TR2b : forall a, cot a = div (cos a) (sin a))
            (TR5 : forall a, (int_pow (sin a) 2%Z) = (add (one) (neg (int_pow (cos a) 2%Z))))
            (TR6 : forall a, (int_pow (cos a) 2%Z) = (add (one) (neg (int_pow (sin a) 2%Z))))
            (TR10a : forall a b, sin (add a b) = add (mul (sin a) (cos b)) (mul (cos a) (sin b)))
            (TR10ainv : forall a b, add (mul (sin a) (cos b)) (mul (cos a) (sin b)) = sin (add a b))
            (TR10b : forall a b, sin (add a (neg b)) = add (mul (sin a) (cos b)) (neg (mul (cos a) (sin b))))
            (TR10c : forall a b, cos (add a b) = add (mul (cos a) (cos b)) (neg (mul (sin a) (sin b))))
            (TR10d : forall a b, cos (add a (neg b)) = add (mul (cos a) (cos b)) (mul (sin a) (sin b)))
            .
            (* (int_pow_mul : forall a n m, (mul (int_pow a m) (int_pow a n) = int_pow a (m + n)%Z)). *)

    Notation "x + y" := (add x y) (at level 50, left associativity).
    Notation "x * y" := (mul x y) (at level 40, left associativity).
    Notation "x / y" := (div x y) (at level 40, left associativity).
    Notation "- x" := (neg x) (at level 35, right associativity).
    Notation "x ^ z" := (int_pow x z) (at level 30, right associativity).
    Notation "! x" := (rat_lit x) (at level 20, left associativity).

    Context (TR7 : forall a, (cos a)^2 = (rat_lit(1) + cos (rat_lit(2) * a)) / rat_lit(2))
            (TR8a : forall a b, (sin a) * (cos b) = (rat_lit(1) / rat_lit(2)) * (sin (a + b) + sin (a + (-b))))
            (TR8b : forall a b, (cos a) * (sin b) = (rat_lit(1) / rat_lit(2)) * (sin (a + b) + (-sin (a + (-b)))))
            (TR8c : forall a b, (cos a) * (cos b) = (rat_lit(1) / rat_lit(2)) * (cos (a + b) + cos (a + (-b))))
            (TR8d : forall a b, (sin a) * (sin b) = -(rat_lit(1) / rat_lit(2)) * (cos (a + b) + (-cos (a + (-b)))))
            (TR9a : forall a b, (sin a) + (sin b) = rat_lit(2) * sin ((a + b) / rat_lit(2)) * cos ((a + (-b) / rat_lit(2))))
            (TR9b : forall a b, (sin a) + (-sin b) = rat_lit(2) * cos ((a + b) / rat_lit(2)) * sin ((a + (-b) / rat_lit(2))))
            (TR9c : forall a b, (cos a) + (cos b) = rat_lit(2) * cos ((a + b) / rat_lit(2)) * cos ((a + (-b) / rat_lit(2))))
            (TR9d : forall a b, (cos a) + (-cos b) = -rat_lit(2) * sin ((a + b) / rat_lit(2)) * sin ((a + (-b) / rat_lit(2))))
            (TR11a : forall a, sin (rat_lit(2) * a) = rat_lit(2) * sin a * cos a)
            (TR11b : forall a, cos (rat_lit(2) * a) = (cos a)^2 + (-(sin a)^2))
            (TR12a : forall a b, tan (a + b) = (tan a + tan b) / (rat_lit(1) + -tan a * tan b))
            (TR12b : forall a b, tan (a + (-b)) = (tan a + (-tan b)) / (rat_lit(1) + tan a * tan b))
            (TR13a : forall a b, (tan a) * (tan b) = rat_lit(1) + -(tan a + tan b) * (cot (a + b)))
            (TR13b : forall a b, (cot a) * (cot b) = rat_lit(1) + (cot a + cot b) * (cot (a + b)))
            .
    


    (* Define some common constants *)    
    Create HintDb trig_db.

    (* Addition axioms *)
    Hint Resolve add_0_l add_comm add_to_left_assoc add_to_right_assoc 
                add_to_left_assoc_inv add_to_right_assoc_inv add_opp add_copy : trig_db.

    (* Multiplication axioms *)
    Hint Resolve mul_1_l mul_0_l mul_comm mul_to_left_assoc mul_distr_l mul_distr_r 
                mul_distr_l_inv mul_distr_r_inv mul_integral_domain : trig_db.

    (* Division axioms *)
    Hint Resolve div_1 frac_mul frac_mul_inv : trig_db.

    (* Power axioms *)
    Hint Resolve int_pow_1 int_pow_0 int_pow_neg int_pow_1_l int_pow_0_l int_pow_a_a : trig_db.

    (* Trigonometric identities *)
    Hint Resolve squareIdent TR1a TR1b TR2a TR2b TR5 TR6 
                TR10a TR10b TR10c TR10d : trig_db.

    (* Rational number axioms *)
    Hint Resolve rat_zero rat_one rat_two rat_add rat_mul rat_neg : trig_db.

    (* sympy tests *)
    (* Lemma TR1_test_1: forall x, !2 * csc(x) + sec(x) = !1/cos(x) + !2/sin(x).
    Proof.
        intros.
        egg_simpl_goal 5.
    Qed.

    Lemma TR2_test_1: forall x, tan(x) = sin(x)/cos(x).
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma TR2_test_2: forall x, cot(x) = cos(x)/sin(x).
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma TR2_test_3: forall x, tan(tan(x) + -sin(x)/cos(x)) = zero.
    Proof.
        intros.
        egg_simpl_goal 5.
    Abort.

    Lemma TR2i_test_1: forall x, sin(x)/cos(x) = tan(x).
    Proof.
        intros.
        egg_simpl_goal 2.
    Qed.

    Lemma TR2i_test_2: forall x y, sin(x)*sin(y)/cos(x) = tan(x)*sin(y).
    Proof.
        intros.
        egg_simpl_goal 2.
    Qed.

    Lemma TR2i_test_3: forall x, !1/(sin(x)/cos(x)) = !1/tan(x).
    Proof.
        intros.
        egg_simpl_goal 2.
    Qed.

    Lemma TR2i_test_4: forall x y, !1/(sin(x)*sin(y)/cos(x)) = !1/tan(x)/sin(y).
    Proof.
        intros.
        egg_simpl_goal 5.
        cbv beta.
    Abort.

    Lemma TR2i_test_5: forall x, sin(x)/!2/(cos(x) + !1) = sin(x)/(cos(x) + !1)/!2.
    Proof.
        intros.
        egg_simpl_goal 2.
        cbv beta.
    Abort.

    Lemma TR2i_test_6: forall x, sin(x)/!2/(cos(x) + !1) = tan(x/!2)/!2.
    Proof.
        intros.
        egg_simpl_goal 3.
        cbv beta.
    Abort.

    Lemma TR2i_test_7: sin(!1)/(cos(!1) + !1) = tan(!1/!2).
    Proof.
        egg_simpl_goal 5.
    Abort.

    Lemma TR2i_test_8: sin(!2)/(cos(!2) + !1) = tan(!1).
    Proof.
        egg_simpl_goal 2.
    Abort.

    Lemma TR2i_test_9: sin(!4)/(cos(!4) + !1) = tan(!2).
    Proof.
        egg_simpl_goal 2.
    Abort.

    Lemma TR2i_test_10: sin(!5)/(cos(!5) + !1) = tan(!5/!2).
    Proof.
        egg_simpl_goal 2.
    Abort.

    Lemma TR2i_test_11: (cos(!1) + !1)/sin(!1) = !1/tan(!1/!2).
    Proof.
        egg_simpl_goal 2.
    Abort.

    Lemma TR2i_test_12: (cos(!2) + !1)/sin(!2) = !1/tan(!1).
    Proof.
        egg_simpl_goal 2.
    Abort.

    Lemma TR2i_test_13: (cos(!4) + !1)/sin(!4) = !1/tan(!2).
    Proof.
        egg_simpl_goal 10.
    Abort.

    Lemma TR2i_test_14: (cos(!5) + !1)/sin(!5) = !1/tan(!5/!2).
    Proof.
        egg_simpl_goal 2.
    Abort.

    Lemma TR8c_test_1: cos(!2)*cos(!3) = cos(!5)/!2 + cos(!1)/!2.
    Proof.
        egg_simpl_goal 3.
    Abort.

    Lemma TR8b_test_1: cos(!2)*sin(!3) = sin(!5)/!2 + sin(!1)/!2.
    Proof.
        egg_simpl_goal 3.
    Abort.

    Lemma TR8d_test_1: sin(!2)*sin(!3) = -cos(!5)/!2 + cos(!1)/!2.
    Proof.
        egg_simpl_goal 10.
        cbv beta.
    Abort.

    Lemma TR8d_test_2: sin(!1)*sin(!2)*sin(!3) = sin(!4)/!4 +- sin(!6)/!4 + sin(!2)/!4.
    Proof.
        egg_simpl_goal 4.
    Abort.

    Lemma TR8c_test_2: cos(!2)*cos(!3)*cos(!4)*cos(!5) = 
        cos(!4)/!4 + cos(!10)/!8 + cos(!2)/!8 + cos(!8)/!8 + cos(!14)/!8 + 
        cos(!6)/!8 + !1/!8.
    Proof.
        egg_simpl_goal 20.
    Abort.

    Lemma TR8c_test_3: cos(!2)*cos(!3)*cos(!4)*cos(!5)*cos(!6) = 
        cos(!10)/!8 + cos(!4)/!8 + !3*cos(!2)/!16 + cos(!16)/!16 + cos(!8)/!8 + 
        cos(!14)/!16 + cos(!20)/!16 + cos(!12)/!16 + !1/!16 + cos(!6)/!8.
    Proof.
        egg_simpl_goal 6.
    Abort.

    Lemma TR8_test_complex: (sin(pi*!3/!7))^2*(cos(pi*!3/!7))^2/(!16*sin(pi/!7)^2) = !1/!64.
    Proof.
        egg_simpl_goal 6.
    Abort. *)

    Lemma sin_addition_with_constants: sin (rat_lit 2) * cos (rat_lit 1) + cos (rat_lit 2) * sin (rat_lit 1) = sin (rat_lit 3).
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma presentation_2: forall a, (sin a <> zero) -> (cos a <> zero) -> mul (tan a) (cot a) = one.
    Proof.
        intros. 
        egg_simpl_goal 2.
        auto.
    Qed.

    Lemma test_pow: forall a, a ^ 2 = !1 -> a^3 = a.
    Proof.
        intros.
        egg_simpl_goal 5.
        cbv beta.


    Lemma trig_test_10: forall a b, add (cos (add a b)) (cos (add a (neg b))) = mul (two) (mul (cos a) (cos b)).
    Proof.
        intros.
        egg_simpl_goal 3.
    Abort.

    Lemma trig_test_add_formula: (sin (rat_lit(1)) * cos (rat_lit(2))) + (cos (rat_lit(1)) * sin (rat_lit(2))) = sin (rat_lit(3)).
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

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

    Lemma trig_test: forall a, (sin a)^2 + (cos a)^2 = one.
    Proof.
        intros.
        egg_simpl_goal 5.
    Qed.

    Lemma trig_test_with_auto: forall a, add (int_pow (sin a) 2%Z) (int_pow (cos a) 2%Z) = one.
    Proof.
        intros.
        auto.
    Qed.

    Lemma binomial_test: forall a b, (a + b)^2 = a * a + rat_lit(2) * a * b + b * b.
    Proof.
        intros.
        egg_simpl_goal 50.
    Qed.

    Lemma test_fail: forall a b n, a * a + a * b + b * a + b * b = n.
    Proof.
        intros.
        egg_simpl_goal 1.
        cbv beta.
    Abort.

    Lemma test_fail_2: forall a b c n, a^2 + b^2 + c^2 + rat_lit(2) * (a * b + a * c + b * c) = n.
    Proof.
        intros.
        egg_simpl_goal 1.
        cbv beta.
    Abort.



    (* Lemma binomial_test_1: forall a b, (a + b) * (a + b) = a * (a + b) + b * (a + b).
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma binomial_test_2: forall a b, a * (a + b) + b * (a + b) = a * a + a * b + a * b + b * b.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma binomial_test_3: forall a b, a * a + a * b + a * b + b * b = a * a + rat_lit(2) * a * b + b * b.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma binomial_test_4: forall a b, a * b + a * b = rat_lit(2) * a * b.
    Proof.
        intros.
        egg_simpl_goal 1.
        cbv beta. *)

    Lemma trig_test2: forall a, sin a * sin a + cos a * cos a = one.
    Proof.
        intros.
        egg_simpl_goal 2.
    Qed.

    Lemma trig_test2_with_auto: forall a, sin a * sin a + cos a * cos a = one.
    Proof.
        intros.
        auto 10 with trig_db.
    Abort.

    Lemma trig_test_3: forall a, sin a * (sin a + cos a) = sin a ^ 2 + sin a * cos a.
    Proof.
        intros.
        egg_simpl_goal 2.
    Qed.

    Lemma trig_test_3_with_auto: forall a, sin a * (sin a + cos a) = sin a ^ 2 + sin a * cos a.
    Proof.
        intros.
        auto 10 with trig_db.
    Abort.

    Lemma trig_test_4: forall a, sin a ^ 2 + sin a * cos a +- (sin a * cos a) = sin a ^ 2.
    Proof.
        intros.
        egg_simpl_goal 2.
    Qed.

    Lemma trig_test_4_with_auto: forall a, sin a ^ 2 + sin a * cos a +- (sin a * cos a) = sin a ^ 2.
    Proof.
        intros.
        auto 10 with trig_db.
    Abort.

    Lemma trig_test_5: forall a, two * sin a ^ 2 + two * cos a ^ 2 = two.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma trig_test_5_with_auto: forall a, two * sin a ^ 2 + two * cos a ^ 2 = two.
    Proof.
        intros.
        auto 10 with trig_db.
    Abort.

    Lemma trig_test_6: forall a, sin a * (sin a + cos a) +- (sin a * cos a) + cos a ^ 2 = one.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma trig_test_6_with_auto: forall a, sin a * (sin a + cos a) +- (sin a * cos a) + cos a ^ 2 = one.
    Proof.
        intros.
        auto 10 with trig_db.
    Abort.

    Lemma trig_test_7: forall a, sin a / cos a + cos a / sin a = tan a + cot a.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma trig_test_7_with_auto: forall a, sin a / cos a + cos a / sin a = tan a + cot a.
    Proof.
        intros.
        auto 10 with trig_db.
    Abort.

    Lemma div_test_1: forall a, (a <> zero) -> div a a = one.
    Proof.
        intros.
        egg_simpl_goal 1.
        auto.
    Qed.

    Lemma div_test_2: forall a b, (a <> zero) -> (b <> zero) -> a * b / (a * b)  = one.
    Proof.
        intros.
        egg_simpl_goal 4; auto.
    Qed.

    Lemma trig_test_8: forall a, (sin a <> zero) -> (cos a <> zero) -> tan a * cot a = one.
    Proof.
        intros.
        egg_simpl_goal 1.
        auto.
    Qed.

    Lemma trig_test_8_with_auto: forall a, (sin a <> zero) -> (cos a <> zero) -> tan a * cot a = one.
    Proof.
        intros.
        auto 10 with trig_db.
    Abort.

    Lemma trig_test_9: forall a b, sin (a + b) + sin (a + - b) = (sin a) * (cos b) + (sin a) * (cos b) + (cos a) * (sin b) + -(cos a) * (sin b).
    Proof.
        intros.
        egg_simpl_goal 6.
    Qed.

    Lemma trig_test_9_a: forall a b, (cos a) * (sin b) + -(cos a) * (sin b) = zero.
    Proof.
        intros.
        egg_simpl_goal 5.
    Qed.

    Lemma trig_test_9_b: forall a b, (sin a) * (cos b) + (sin a) * (cos b) + zero = two * (sin a * cos b).
    Proof.
        intros.
        egg_simpl_goal 5.
    Qed.


    Lemma trig_test_9_with_auto: forall a b, sin (a + b) + sin (a + - b) = two * (sin a * cos b).
    Proof.
        intros.
        auto 10 with trig_db.
    Abort.



    Lemma trig_test_10_a: forall a b, cos (a + b) = ((cos a) * (cos b) + (-sin a * sin b)).
    Proof.
        intros.
        egg_simpl_goal 5.
    Qed.

    Lemma trig_test_10_b: forall a b, cos (a + (-b)) = ((cos a) * (cos b) + (sin a * sin b)).
    Proof.
        intros.
        egg_simpl_goal 5.
    Qed.

    Lemma trig_test_10_c: forall a b, (-sin a * sin b) + (sin a * sin b) = zero.
    Proof.
        intros.
        egg_simpl_goal 5.
    Qed.
    

    Lemma trig_test_10_with_auto: forall a b, cos (a + b) + cos (a + - b) = two * (cos a * cos b).
    Proof.
        intros.
        auto 10 with trig_db.
    Abort.

    Lemma mul_0_rat_lit_l: forall a, mul (rat_lit 0) a = zero.
    Proof.
        intros.
        egg_simpl_goal 5.
    Qed.

    Lemma trig_test_11: forall a b, (sin a) ^ 2 * (sin b) ^ 2 + (sin a) ^ 2 * (cos b) ^ 2 + (cos a) ^ 2 = rat_lit 1.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma trig_test_12: forall a b c, (sin (a + b + c)) = (-sin(a)*sin(b) + cos(a)*cos(b))*sin(c) + (sin(a)*cos(b) + sin(b)*cos(a))*cos(c).
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma trig_test_consts: (cos(!1)*sin(!3) + sin(!1)*cos(!3) + cos(!3)) = cos(!3) + sin(!4).
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

    Lemma trig_test_TR10i: (cos(!2)*cos(!3) + sin(!2)*(cos(!1)*sin(!2) + cos(!2)*sin(!1))) = cos(!1).
    Proof.
        intros.
        egg_simpl_goal 2.
        cbv beta.
        egg_simpl_goal 2.
    Qed.

    Lemma tan_test: forall a, (sin a)^2  / (cos a)^2  = (tan a)^2.
    Proof.
        intros.
        egg_simpl_goal 10.
    Abort.

    Lemma tan_test_1: forall a, (sin a)^2 / (cos a)^2  = (sin a / cos a) * (sin a / cos a).
    Proof.
        intros.
        egg_simpl_goal 2.
    Qed.

    Lemma tan_test_2: forall a, (sin a / cos a) * (sin a / cos a) = (tan a) ^ 2.
    Proof.
        intros.
        egg_simpl_goal 2.
    Qed.

    Lemma tan_test_guided: forall a, (sin a)^2 / (cos a)^2  = (tan a) ^ 2.
    Proof.
        intros.
        rewrite tan_test_1.
        rewrite tan_test_2.
        reflexivity.
    Qed.

    Lemma square_inv_test: forall a, a ^ 2 = a * a.
    Proof.
        intros.
        egg_simpl_goal 1.
    Qed.

End TestStuff.