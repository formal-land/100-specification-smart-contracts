Require Import FullSpecificationSmartContracts.Common.

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
  | FulfillOrder
      (nft_type : TokenKind)
      (nft_quantity : TokenQuantity nft_type)
      (amount : TokenQuantity payment_token_kind) :
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
    | Command.FulfillOrder nft_type nft_quantity amount =>
      let! user := M.MakeAction (Action.FindUserWithEnoughBalance nft_type nft_quantity) in
      match user with
      | Some user =>
        let! selling_price :=
          M.MakeAction (Action.SellingPriceForNft payment_token_kind nft_type user) in
        match selling_price with
        | Some selling_price =>
          let! is_payment_success :=
            M.MakeAction (Action.Transfer payment_token_kind sender user selling_price) in
          let! is_nft_transfer_success :=
            M.MakeAction (Action.Transfer nft_type user sender nft_quantity) in
          M.Pure (Some (is_payment_success && is_nft_transfer_success, state))
        | None =>
          M.Pure (Some (false, state))
        end
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
        trivial.
      }
      apply ActionTree.Forall.Pure.
    }
    { (* call *)
      destruct command.
      { (* FulfillOrder *)
        unfold NoStealing.InRun.t; cbn.
        destruct Primitives.find_user_with_enough_balance; cbn.
        { (* We found a user with enough balance *)
          destruct Primitives.selling_price_for_nft; cbn.
          { (* We found a selling price *)
            destruct Primitives.transfer; cbn.
            { (* The payment transfer succeeded *)
              destruct Primitives.transfer; cbn.
              { (* The NFT transfer succeeded *)
                apply ActionTree.Forall.Let. {
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
                  trivial.
                }
                apply ActionTree.Forall.Let. {
                  apply ActionTree.Forall.MakeAction.
                  cbn.
                  (* TODO: make another formalization so that we can explicit that we are actually
                     not stealing the NFTs, as we just made the payment before. *)
                  admit.
                }
                apply ActionTree.Forall.Pure.
              }
              { (* The NFT transfer failed *)
                apply ActionTree.Forall.Let. {
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
                  trivial.
                }
                apply ActionTree.Forall.Let. {
                  apply ActionTree.Forall.MakeAction.
                  cbn.
                  (* Same issue as above *)
                  admit.
                }
                apply ActionTree.Forall.Pure.
              }
            }
            { (* The payment transfer failed *)
              destruct Primitives.transfer; cbn.
              { (* The NFT transfer succeeded *)
                apply ActionTree.Forall.Let. {
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
                  trivial.
                }
                apply ActionTree.Forall.Let. {
                  apply ActionTree.Forall.MakeAction.
                  cbn.
                  (* Same issue as above *)
                  admit.
                }
                apply ActionTree.Forall.Pure.
              }
              { (* The NFT transfer failed *)
                apply ActionTree.Forall.Let. {
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
                  trivial.
                }
                apply ActionTree.Forall.Let. {
                  apply ActionTree.Forall.MakeAction.
                  cbn.
                  (* Same issue as above *)
                  admit.
                }
                apply ActionTree.Forall.Pure.
              }
            }
          }
          { (* We did not find a user with enough balance *)
            apply ActionTree.Forall.Let. {
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
        { (* We did not find a user with enough balance *)
          apply ActionTree.Forall.Let. {
            apply ActionTree.Forall.MakeAction.
            cbn.
            trivial.
          }
          apply ActionTree.Forall.Pure.
        }
      }
    }
  Admitted.
End IsSafe.
