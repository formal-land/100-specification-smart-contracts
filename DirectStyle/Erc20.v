Require Import FullSpecificationSmartContracts.DirectStyle.Common.

(** Here we give an application of our DSL above with a representation of a simplified version of
    an [ERC-20] smart contract. *)

(** The init parameters are a name and a symbol for the token we are creating. They do not play
    any role in the computations, but are there in the ERC-20 of OpenZeppelin that we study. *)
Definition InitInput : Set :=
  string * string.

(** The init outputs a new token kind *)
Definition InitOutput : Set :=
  TokenKind.

(** The state of the contract is just the name and the symbol of its token. The token balance for
    each user is stored in the global world and we do not have to handle it here. *)
Module State.
  Record t : Set := {
    name : string;
    symbol : string;
  }.
End State.

(** The commands representing the entrypoints of our smart contract, with the type of their
    output. *)
Module Command.
  Inductive t {token_kind : InitOutput} : Set -> Set :=
  | BalanceOf : User -> t (TokenQuantity token_kind)
  | GetAllowance : User -> User -> t (TokenQuantity token_kind)
  | Transfer : User -> TokenQuantity token_kind -> t unit
  | Approve (spender : User) (quantity : TokenQuantity token_kind) : t unit
  | Mint (account : User) (value : TokenQuantity token_kind) : t unit.
  Arguments t : clear implicits.
End Command.

(** The definition of our ERC-20 smart contract *)
Definition smart_contract :
  SmartContract.t
    InitInput
    InitOutput
    Command.t
    State.t :=
{|
  (* The constructor function *)
  SmartContract.init _sender '(name, symbol) :=
    let! token_kind := M.MakeAction Action.CreateTokenKind in
    let state := {|
      State.name := name;
      State.symbol := symbol;
    |} in
    M.Pure (Some (token_kind, state));
  SmartContract.call A token_kind sender command state :=
    match command in Command.t _ A return M.t (option (A * _)) with
    (* The "balanceOf" entrypoint *)
    | Command.BalanceOf user =>
      (* We run the action to get the balance *)
      let! balance := M.MakeAction (Action.GetBalance token_kind user) in
      M.Pure (Some (balance, state))
    (* The "allowance" entrypoint *)
    | Command.GetAllowance user spender =>
      let! allowance := M.MakeAction (Action.GetAllowance token_kind user spender) in
      M.Pure (Some (allowance, state))
    (* The "transfer" entrypoint *)
    | Command.Transfer to value =>
      (* We run the action to make the transfer and to know if it succeeded *)
      let! is_success := M.MakeAction (Action.Transfer token_kind sender to value) in
      if is_success then
        M.Pure (Some (tt, state))
      else
        M.Pure None
    (* The "approve" entrypoint *)
    | Command.Approve spender value =>
      let! _ := M.MakeAction (Action.Approve token_kind sender spender value) in
      M.Pure (Some (tt, state))
    | Command.Mint account value =>
      let! is_success := M.MakeAction (Action.Mint token_kind account value) in
      if is_success then
        M.Pure (Some (tt, state))
      else
        M.Pure None
    end;
|}.

(** Now we will verify that our ERC-20 smart contract is safe *)
Module IsSafe.
  (** Here is the specification saying that our smart contract is safe. It applies the predicate
      saying that a smart contract is safe to our definition of ERC-20. *)
  Lemma is_safe : NoStealing.InSmartContract.t Erc20.smart_contract.
  (** Here is the proof that the specification is correct. It should be executed in an IDE to see
      the proof state as we progress line by line.

      The general idea is to go over all the possible execution scenarios of the smart contract,
      with the init, the "balanceOf", and the "transfer" entrypoints, and to prove that they are all
      safe.
  *)
  Proof.
    constructor; intros; cbn.
    { (* init *)
      destruct init_input as [name symbol].
      unfold NoStealing.InRun.t; cbn.
      destruct Primitives.create_token_kind.
      apply ActionTree.Forall.Let. {
        (* The init is safe because the action we make to create a new token kind is safe *)
        apply ActionTree.Forall.MakeAction.
        cbn.
        trivial.
      }
      apply ActionTree.Forall.Pure.
    }
    { (* call *)
      destruct command.
      { (* BalanceOf *)
        unfold NoStealing.InRun.t; cbn.
        apply ActionTree.Forall.Let. {
          (* The "balanceOf" entrypoint is safe because the action we make to get the balance of a
             user is safe *)
          apply ActionTree.Forall.MakeAction.
          cbn.
          trivial.
        }
        apply ActionTree.Forall.Pure.
      }
      { (* GetAllowance *)
        cbn.
        unfold NoStealing.InActionTree.t.
        apply ActionTree.Forall.Let. {
          apply ActionTree.Forall.MakeAction.
          cbn.
          trivial.
        }
        apply ActionTree.Forall.Pure.
      }
      { (* Transfer *)
        unfold NoStealing.InRun.t; cbn.
        (* We have two cases, depending on whether the transfer succeeded or not. In both cases we
           make a single transfer (or transfer attempt) with the right user for the source account,
           so this is safe.
        *)
        destruct Primitives.transfer; cbn.
        { apply ActionTree.Forall.Let. {
            apply ActionTree.Forall.MakeAction.
            cbn.
            left. trivial.
          }
          apply ActionTree.Forall.Pure.
        }
        { apply ActionTree.Forall.Let. {
            apply ActionTree.Forall.MakeAction.
            cbn.
            left. trivial.
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
      { (* Mint *)
        unfold NoStealing.InRun.t; cbn.
        destruct Primitives.mint.
        { cbn.
          apply ActionTree.Forall.Let. {
            apply ActionTree.Forall.MakeAction.
            cbn.
            trivial.
          }
          apply ActionTree.Forall.Pure.
        }
        { cbn.
          apply ActionTree.Forall.Let. {
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
