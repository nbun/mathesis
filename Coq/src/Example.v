Require Import Thesis.Handler.
Require Import Thesis.Effect.
Require Import Thesis.Free.
Require Import Thesis.Base.

Set Implicit Arguments.

Example p1 : Prog (nat * nat) := Share Coin >>= fun x => duplicate x.
Lemma l1 : handle e1 = ((0, 0) :: (1, 1) :: Datatypes.nil)%list.

Example e2 : Prog nat := Share Coin >>= fun x => addM x x.
Lemma l2 : handle e2 = (0 :: 2 :: Datatypes.nil)%list.

Example e3 : Prog bool := orM (pure true) Fail.
Lemma l3 : handle e3 = (true :: Datatypes.nil)%list.

Definition ls := (l1 :: l2 :: l3 :: Datatypes.nil)%list.
