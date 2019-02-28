Require Import Thesis.HigherOrder.Base.
Require Import Thesis.HigherOrder.Classes.
Require Import Thesis.HigherOrder.Effect.
Require Import Thesis.HigherOrder.Prog.
Require Import Thesis.Search.

Set Implicit Arguments.

Definition run A (fz : Free C__Zero A) : A :=
  match fz with
  | pure x => x
  | impure e => match e with
                 ext s _ _ => match s with end
               end
  end.

Fixpoint runChoice A (fc : Free C__Choice A) : Tree A :=
  match fc with
  | pure x => Leaf x
  | impure (ext sfail   _ _)  => Empty A
  | impure (ext (schoice mid) pf _) => Branch mid (runChoice (pf true)) (runChoice (pf false))
  end.

Fixpoint runState A (n : nat * nat) (fc : Prog A) : Prog__SC A.
  destruct fc.
  - give_up.
  - destruct e.
    destruct s.
    + give_up.
    + destruct s.
      * destruct s.
        apply impure.
        apply ext with (s := inl (ssharing n A)).
        -- intros.
           apply runState.
           ++ apply n.
           ++ apply f.
              apply pcont.
              simpl. simpl in *.
              Admitted.

  (* match fc with *)
  (* | pure x => pure x *)
  (* | impure (ext (inl (sget _))    pf _) => runState n  (pf (pget n)) *)
  (* | impure (ext (inl (sput s'))   pf _) => runState s' (pf (pput s')) *)
  (* | impure (ext (inr (inr sfail)) _ _)  => Fail__SC *)
  (* | impure (ext (inr (inr (schoice mid))) pf _) => Choice__SC mid (runState n (pf true)) (runState n (pf false)) *)
  (* | impure (ext (inr (inl (ssharing m _ as s)))  pf pfx) => *)
  (*   let s : @Shape _ NDShare__SC := (inl (ssharing n A)) *)
  (*   in impure (ext s (fun p : @Pos _ NDShare__SC s => runState n (pf p)) *)
  (*                  (fun p : @PosX _ NDShare__SC s => match p with pshared _ => fs end)) *)
  (*   (* Share'__SC m (runState n (pfx (pshared s))) (fun x => (pf (pcont s x))) *) *)
  (* end. *)

(* Definition tripl A B C (p : A * B) (c : C) : A * B * C := *)
(*   let '(a,b) := p in (a,b,c). *)

(* Fixpoint runSharing A (fs : Free (C__Comb C__Sharing C__Choice) A) : Free C__Choice A := *)
(*   let fix nameChoices (next : nat) (scope : nat * nat) (scopes : list (nat * nat)) (fs : Prog__SC A) *)
(*   : Free C__Choice A  := *)
(*       match fs with *)
(*       | pure x => pure x *)
(*       | impure (ext (inl (sbsharing n)) pf) => *)
(*         nameChoices 1 n (cons n scopes) (pf (pbsharing n)) *)
(*       | impure (ext (inl (sesharing n)) pf) => *)
(*         match scopes with *)
(*         | cons _ (cons j js) as ks => nameChoices next j ks (pf (pesharing n))  *)
(*         | _                        => runSharing (pf (pesharing n)) *)
(*         end *)
(*       | impure (ext (inr sfail)        pf) => Fail__C *)
(*       | impure (ext (inr (schoice _))  pf) => *)
(*         let l := nameChoices (next + 1) scope scopes (pf true) in *)
(*         let r := nameChoices (next + 1) scope scopes (pf false) *)
(*         in Choice__C (Some (tripl scope next)) l r *)
(*       end *)
(*   in match fs with *)
(*      | pure x => pure x *)
(*      | impure (ext (inl (sbsharing n))  pf) => *)
(*        nameChoices 1 n (cons n nil) (pf (pbsharing n)) *)
(*      | impure (ext (inl (sesharing n))  pf) => runSharing (pf (pesharing n)) *)
(*      | impure (ext (inr sfail)         _)  => Fail__C *)
(*      | impure (ext (inr (schoice mid)) pf) => *)
(*        Choice__C mid (runSharing (pf true)) (runSharing (pf false)) *)
(*      end. *)

(* Definition handle A `{Normalform A A} (fs : Prog A) : list A := *)
(*   collectVals (runChoice (runSharing (runState (0,0) (nf fs)))). *)
