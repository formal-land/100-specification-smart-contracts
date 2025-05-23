Require Import FullSpecificationSmartContracts.DirectStyle.Common.
Require Import Coq.Classes.RelationClasses.

Local Open Scope bool_scope.

Definition InitInput : Set :=
  unit.

(** The init outputs a new token kind *)
Definition InitOutput : Set :=
  TokenKind.

Module State.
  Definition t : Set :=
    unit.
End State.

(** Entrypoints of the contract *)
Module Command.
  Inductive t {payment_token_kind : InitOutput} : Set -> Set :=
  | ProposeItem
      (nft_type : TokenKind)
      (nft_quantity : TokenQuantity nft_type)
      (item_price : TokenQuantity payment_token_kind) :
      t unit
  | GetItem
      (nft_type : TokenKind)
      (payment_token_quantity : TokenQuantity payment_token_kind) :
      t bool
  .
  Arguments t : clear implicits.
End Command.

Definition smart_contract :
  SmartContract.t
    InitInput
    InitOutput
    Command.t
    State.t :=
{|
  SmartContract.init _sender _input :=
    let! payment_token_kind := M.MakeAction Action.CreateTokenKind in
    M.Pure (Some (payment_token_kind, tt));
  SmartContract.call A payment_token_kind sender command state :=
    match command in Command.t _ A return M.t (option (A * _)) with
    | Command.ProposeItem nft_type nft_quantity item_price =>
      let! _ :=
        M.MakeAction (Action.ProposeItem sender payment_token_kind nft_type nft_quantity item_price) in
      M.Pure (Some (tt, tt))
    | Command.GetItem nft_type payment_token_quantity =>
      let! seller :=
        M.MakeAction (Action.FindUserReadyToDoASwap
          payment_token_kind nft_type
          payment_token_quantity TokenQuantityOne
        ) in
      match seller with
      | Some seller =>
        let! is_swap_success :=
          M.MakeAction (Action.Swap
            sender
            seller
            payment_token_kind
            nft_type
            payment_token_quantity
            TokenQuantityOne
          ) in
        M.Pure (Some (is_swap_success, state))
      | None =>
        M.Pure (Some (false, state))
      end
    end
|}.

Module IsSafe.
  Lemma is_safe : NoStealing.InSmartContract.t smart_contract.
  Proof.
    constructor; intros; cbn.
    { (* init *)
      unfold NoStealing.InRun.t; cbn.
      destruct Primitives.create_token_kind.
      apply ActionTree.Forall.Let. {
        apply ActionTree.Forall.MakeAction.
        cbn.
        reflexivity.
      }
      apply ActionTree.Forall.Pure.
    }
    { (* call *)
      destruct command eqn:?.
      { (* ProposeItem *)
        unfold NoStealing.InRun.t; cbn.
        apply ActionTree.Forall.Let. {
          apply ActionTree.Forall.MakeAction.
          cbn.
          reflexivity.
        }
        apply ActionTree.Forall.Pure.
      }
      { (* FulfillOrder *)
        unfold NoStealing.InRun.t; cbn.
        destruct Primitives.find_user_ready_to_do_a_swap
          as [seller |]
          eqn:H_seller_ready_to_swap; cbn.
        { (* We found a seller *)
          destruct Primitives.swap; cbn.
          { (* The swap succeeded *)
            apply ActionTree.Forall.Let. {
              apply ActionTree.Forall.MakeAction.
              cbn.
              trivial.
            }
            apply ActionTree.Forall.Let. {
              apply ActionTree.Forall.MakeAction.
              cbn.
              apply Primitives.find_user_ready_to_do_a_swap_is_valid.
              exact H_seller_ready_to_swap.
            }
            apply ActionTree.Forall.Pure.
          }
          { (* The swap failed *)
            apply ActionTree.Forall.Let. {
              apply ActionTree.Forall.MakeAction.
                cbn.
                trivial.
            }
            apply ActionTree.Forall.Let. {
              apply ActionTree.Forall.MakeAction.
              cbn.
              apply Primitives.find_user_ready_to_do_a_swap_is_valid.
              exact H_seller_ready_to_swap.
            }
            apply ActionTree.Forall.Pure.
          }
        }
        { (* We did not find a selling price *)
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
