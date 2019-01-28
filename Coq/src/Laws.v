Require Import Thesis.Effect.
Require Import Thesis.Classes.
Require Import Thesis.DataM.
Require Import Thesis.Handler.
Require Import Thesis.Prog.
Require Import Thesis.Base.
Require Import Thesis.Eq.

Set Implicit Arguments.

Theorem T__Fail_fstrict : forall (f' : bool -> Prog bool),
    Eq_Prog eq (Share Fail >>= fun fx => fx >>= f') (pure Fail >>= fun fx => fx >>= f').
Proof. econstructor. Qed.

Theorem T__Fail_id :
    Eq_Prog eq (Share Fail >>= id) (pure Fail >>= id).
Proof. econstructor. Qed.

Definition const A B (x : A) (y : B) := x.

Theorem state_init : forall A n m (p : Prog A),
    (* runState n p = runState m p. *)
    Eq_list eq (Search.dfs Search.emptymap (runChoice (runSharing (runState n p))))
    (Search.dfs Search.emptymap (runChoice (runSharing (runState m p)))).
Proof.
  intros A n m p.
  induction p using Free_Ind.
  - repeat econstructor.
  - destruct s.
    + destruct s.
      * simpl.
Admitted.

Theorem T__Fail_const : forall A x,
    Eq_Prog eq (Share Fail >>= const x) (pure (@Fail A) >>= const x).
Proof. 
  intros A x. unfold const.
  unfold Eq_Prog, handle, Search.collectVals, Share', const. simpl.
Admitted.