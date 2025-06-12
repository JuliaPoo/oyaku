Require Import egg.Loader.
Require Import Coq.ZArith.ZArith. (* TODO make plugin work even if ZArith is not loaded *)
(* Require Import Coq.QArith.QArith. *)
(* Require Import Coq.Strings.String. *)


Require Import Ring.
From HB Require Import structures.
(* From mathcomp.algebra_tactics Require Import lra. *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp.zify Require Import ssrZ.

From mathcomp Require Import functions reals ereal.
From mathcomp Require Import normedtype landau sequences derive realfun exp.
From mathcomp Require Import realfun measure lebesgue_measure lebesgue_integral.
From mathcomp Require Import ftc trigo.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.

Section TestStuffAgain.
            (* (int_pow_mul : forall a n m, (mul (int_pow a m) (int_pow a n) = int_pow a (m + n)%Z)). *)
    Context (R : realType)
            (* (sinDRule : forall (x y : R), sin (x + y) = sin x * cos y + cos x * sin y) *)
            (* (sinDRuleCasted : forall (x y : R), sin (x + y)%E = ((sin x * cos y)%R + (cos x * sin y)%R)%E)
            (sinDRuleCastedInv : forall (x y : R), ((sin x * cos y)%R + (cos x * sin y)%R)%E = sin (x + y)%E) *)
            (* (sinDRuleImported := sinD) *)
            (Expr : Type)
            (add: Expr -> Expr -> Expr)
            (one: Expr)
            (two: Expr)
            (* real axioms *)
            (real_add_comm: forall (x y : R), x + y = y + x)
            (real_add_assoc: forall (x y z : R), x + (y + z) = (x + y) + z)
            (real_add_id: forall (x : R), x + 0 = x)
            (real_add_inv: forall (x : R), x + - x = 0)
            (real_mult_comm: forall (x y : R), x * y = y * x)
            (real_mult_assoc: forall (x y z : R), x * (y * z) = (x * y) * z)
            (real_mult_id: forall (x : R), x * 1 = x)
            (real_mult_inv: forall (x : R), x * (1 / x) = 1)
            (real_mult_dist: forall (x y z : R), x * (y + z) = x * y + x * z)
            (test_cast_rule: forall (x y : nat), sin (x%:R + y%:R)%E = ((sin x%:R * cos y%:R)%R + (cos x%:R * sin y%:R)%R)%E :> R)
            (nat_addn1 := addn1)
            (natrD_rule := natrD).


(* 
 

    
    Definition Q_to_rat (q : Q) : rat :=
        let n : int := int_of_Z (Qnum q) in
        let d : int := Posz (Pos.to_nat (Qden q)) in
        ((n%:Q) / (d%:Q))%Q.

    Definition rat_to_R (q : rat) : R := ratr q.

    Definition Q_to_R (q : Q) : R :=
        rat_to_R (Q_to_rat q).

    (* ring hom *)
    Lemma Q_to_rat_hom : forall (q1 q2 : Q), Q_to_rat (q1 + q2) = Q_to_rat q1 + Q_to_rat q2.
    Proof.
        intros.
        rat_to_ring.
        unfold Q_to_rat.
        unfold int_of_Z.
        have /eqP : Q_to_rat (q1 + q2) - (Q_to_rat q1 + Q_to_rat q2) == 0 by field.

    Lemma Q_to_R_hom : forall (q1 q2 : Q), Q_to_R (q1 + q2) = Q_to_R q1 + Q_to_R q2.
    Proof.
        intros q1 q2.
        unfold Q_to_R, rat_to_R, Q_to_rat.
        simpl.
        unfold GRing.add.
        unfold GRing.isNmodule.add.
        unfold GRing.Nmodule.GRing_isNmodule_mixin.
        Unset Printing Notations.
        reflexivity. *)

    (* The sinD rule *)

    (* Lemmas *)
    Lemma sinD_inv : forall (R: realType) (x y : R),
    sin x * cos y + cos x * sin y = sin (x + y).
    Proof.
        symmetry.
        exact (sinD x y).
    Qed.

    (* Definition qSin (R: realType) (x y : Q) : R :=
        sin ((ratr x + ratr y)%:R). *)

    Ltac intro_rw_rules :=
        pose proof sinD;
        pose proof sinD_inv;
        pose proof nat_addn1;
        pose proof natrD.
    
    Example test_rule: forall (R : realType) (x y : R), sin (x + y) = sin x * cos y + cos x * sin y.
    Proof.
        intros.
        intro_rw_rules.
        egg_simpl_goal 1.
    Qed.

    Example presentation_1: sin 2%:R * cos 1%:R + cos 2%:R * sin 1%:R = sin (2%:R + 1%:R) :> R.
    Proof.
        intros.
        egg_simpl_goal 2.
    Qed.

    



    (* Example test_nat: S(O) + S(O) = 2.
    Proof.
        intros.
        Print add.
        egg_simpl_goal 5.
        reflexivity. *)

    Example testtste: 1%:R + 1%:R = 2%:R :> R.
    Proof.
        (* rewrite <- natrD. *)
        egg_simpl_goal 5.

        (* rewrite <- natrD.
        assert (f: erefl). *)
        (* egg_simpl_goal 5. *)
        by rewrite -natrD.
    Qed.

    Example testarith2: 3%:R / 2%:R + 1%:R / 2%:R = 2%:R :> R.
    Proof.
        lra.
    Qed.
        
        

    Example test_rule3: sin (3%:R / 2%:R) * cos (1%:R / 2%:R) + cos (3%:R / 2%:R) * sin (1%:R / 2%:R) = sin ((3%:R / 2%:R) + (1%:R / 2%:R)) :> R.
    Proof.
        intros.
        egg_simpl_goal 5.
        reflexivity.
    Qed.

    Example test_comm: forall (x y : R), x + y = y + x.
    Proof.
        intros.
        egg_simpl_goal 5.
        reflexivity.
    Qed.

    Example test_comm2: forall (x y : R), sin x + sin y = sin y + sin x.
    Proof.
        intros.
        egg_simpl_goal 5.
        reflexivity.
    Qed.

    Search _ (_ + _ = _ + _) in ssralg.

  