Require Import FullSpecificationSmartContracts.Promises.Common.

Module Promises.
  Inductive t {token_kind : TokenKind} : Set :=
  | Nothing : t
  | Approval (approved_spender : User) (quantity : TokenQuantity token_kind) : t.
  Arguments t : clear implicits.
End Promises.

Module Request.
  Inductive t {token_kind : TokenKind} : Set :=
  | UseOtherAccountToMakeTransfer
      (to : User)
      (value : TokenQuantity token_kind) :
      t.
  Arguments t : clear implicits.
End Request.

Definition execute_request {payment_token token_kind : TokenKind}
    (requested_user : User)
    (sender : User)
    (payment : TokenQuantity payment_token)
    (promises : Promises.t token_kind)
    (request : Request.t token_kind) :
  M.t bool :=
  match request with
  | Request.UseOtherAccountToMakeTransfer to value =>
    match promises with
    | Promises.Nothing =>
      M.Pure false
    | Promises.Approval spender quantity =>
      if token_quantity_leq value quantity then
        let! _ :=
          M.MakeAction (Action.Transfer token_kind requested_user to value) in
        let new_approved_quantity :=
          token_quantity_sub quantity value in
        match new_approved_quantity with
        | Some new_approved_quantity =>
          let! _ :=
            M.MakeAction (Action.RegisterPromiseForUser requested_user (Promises.Approval spender new_approved_quantity)) in
          M.Pure true
        | None =>
          M.Pure false
        end
      else
        M.Pure false
    end
  end.
