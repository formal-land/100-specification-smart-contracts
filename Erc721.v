Require Import FullSpecificationSmartContracts.Common.

Definition InitInput : Set :=
  string * string.

Definition InitOutput : Set :=
  unit.

Module State.
  Record t : Set := {
    name : string;
    symbol : string;
  }.
End State.

(** The commands representing the entrypoints of our smart contract, with the type of their
    output. *)
Module Command.
  Inductive t {init_output : InitOutput} : Set -> Set :=
  | Update (to : User) (token_id : TokenKind) : t unit
  | Mint (to : User) (token_id : TokenKind) : t unit
  | Approve (to : User) (token_id : TokenKind) : t unit.
  (* | ApproveForAll (to : User) : t unit. *)
  Arguments t : clear implicits.
End Command.

Definition smart_contract :
  SmartContract.t
    InitInput
    InitOutput
    Command.t
    State.t :=
{|
  (* The constructor function *)
  SmartContract.init _sender '(name, symbol) :=
    let state := {|
      State.name := name;
      State.symbol := symbol;
    |} in
    M.Pure (Some (tt, state));
  SmartContract.call A token_kind sender command state :=
    match command in Command.t _ A return M.t (option (A * _)) with
    (* The "update" entrypoint *)
    | Command.Update to token_id =>
      let! from := M.MakeAction (Action.GetUniqueTokenKindOwner token_id) in
      match from with
      | Some from =>
        let! is_eq := M.MakeAction (Action.UserEq from sender) in
        if is_eq then
          let! is_success := M.MakeAction (Action.Transfer token_id from to TokenQuantityOne) in
          if is_success then
            M.Pure (Some (tt, state))
          else
            M.Pure None
        else
          M.Pure None
      | None =>
        M.Pure None
      end
    | Command.Mint to token_id =>
      let! is_success := M.MakeAction (Action.Mint token_id to TokenQuantityOne) in
      if is_success then
        M.Pure (Some (tt, state))
      else
        M.Pure None
    | Command.Approve to token_id =>
      let! is_success := M.MakeAction (Action.Approve token_id sender to TokenQuantityOne) in
      if is_success then
        M.Pure (Some (tt, state))
      else
        M.Pure None
    (* | Command.ApproveForAll to => *)
    end;
|}.

Module IsSafe.
  Lemma is_safe : NoStealing.InSmartContract.t smart_contract.
  Proof.
    constructor; intros; cbn.
    { (* init *)
      destruct init_input as [name symbol].
      unfold NoStealing.InRun.t; cbn.
      apply ActionTree.Forall.Pure.
    }
    { (* call *)
      destruct command.
      { (* Update *)
        unfold NoStealing.InRun.t; cbn.
        destruct Primitives.get_unique_token_kind_owner; cbn.
        { destruct Primitives.user_eq eqn:?; cbn.
          { destruct Primitives.transfer; cbn.
            { apply ActionTree.Forall.Let. {
                apply ActionTree.Forall.MakeAction.
                cbn.
                trivial.
              }
              apply ActionTree.Forall.Let. {
                apply ActionTree.Forall.MakeAction.
                cbn.
                trivial.
              }
              apply ActionTree.Forall.Let. {
                apply ActionTree.Forall.MakeAction.
                cbn.
                apply Primitives.user_eq_is_valid.
                trivial.
              }
              apply ActionTree.Forall.Pure.
            }
            { apply ActionTree.Forall.Let. {
                apply ActionTree.Forall.MakeAction.
                cbn.
                trivial.
              }
              apply ActionTree.Forall.Let. {
                apply ActionTree.Forall.MakeAction.
                cbn.
                trivial.
              }
              apply ActionTree.Forall.Let. {
                apply ActionTree.Forall.MakeAction.
                cbn.
                apply Primitives.user_eq_is_valid.
                trivial.
              }
              apply ActionTree.Forall.Pure.
            }
          }
          { apply ActionTree.Forall.Let. {
              apply ActionTree.Forall.MakeAction.
              cbn.
              trivial.
            }
            apply ActionTree.Forall.Let. {
              apply ActionTree.Forall.MakeAction.
              cbn.
              trivial.
            }
            apply ActionTree.Forall.Pure.
          }
        }
        { apply ActionTree.Forall.Let. {
            apply ActionTree.Forall.MakeAction.
            cbn.
            trivial.
          }
          apply ActionTree.Forall.Pure.
        }
      }
      { (* Mint *)
        unfold NoStealing.InRun.t; cbn.
        destruct Primitives.mint; cbn.
        { apply ActionTree.Forall.Let. {
            apply ActionTree.Forall.MakeAction.
            cbn.
            trivial.
          }
          apply ActionTree.Forall.Pure.
        }
        { apply ActionTree.Forall.Let. {
            apply ActionTree.Forall.MakeAction.
            cbn.
            trivial.
          }
          apply ActionTree.Forall.Pure.
        }
      }
      { (* Approve *)
        unfold NoStealing.InRun.t; cbn.
        destruct Primitives.approve; cbn.
        { apply ActionTree.Forall.Let. {
            apply ActionTree.Forall.MakeAction.
            cbn.
            trivial.
          }
          apply ActionTree.Forall.Pure.
        }
        { apply ActionTree.Forall.Let. {
            apply ActionTree.Forall.MakeAction.
            cbn.
            trivial.
          }
          apply ActionTree.Forall.Pure.
        }
      }
    }
  Qed.
End IsSafe.
