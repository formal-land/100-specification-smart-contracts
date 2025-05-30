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
          M.MakeAction (Action.Transfer token_kind to value) in
        let new_approved_quantity :=
          token_quantity_sub quantity value in
        match new_approved_quantity with
        | Some new_approved_quantity =>
          let! _ :=
            M.MakeAction (Action.RegisterPromiseForUser (Promises.Approval spender new_approved_quantity)) in
          M.Pure true
        | None =>
          M.Pure false
        end
      else
        M.Pure false
    end
  end.

Module Entrypoint.
  Inductive t {token_kind : TokenKind} : Set :=
  | Transfer (to : User) (value : TokenQuantity token_kind) : t
  | Approve (spender : User) (value : TokenQuantity token_kind) : t
  | TransferUsingApproval (from to : User) (value : TokenQuantity token_kind) : t.
  Arguments t : clear implicits.
End Entrypoint.

Definition execute_entrypoint {payment_token token_kind : TokenKind}
    (sender : User)
    (promises : Promises.t token_kind)
    (entrypoint : Entrypoint.t token_kind) :
  M.t bool :=
  match entrypoint with
  | Entrypoint.Transfer to value =>
    let! is_success :=
      M.MakeAction (Action.Transfer token_kind to value) in
    M.Pure is_success
  | Entrypoint.Approve spender value =>
    let! _ :=
      M.MakeAction (Action.RegisterPromiseForUser (Promises.Approval spender value)) in
    M.Pure true
  | Entrypoint.TransferUsingApproval from to value =>
    let! _ :=
      M.MakeAction (Action.EmitRequest
        (fun (user : User) (promises : Promises.t token_kind) =>
          user = from
        )
        (* This is free to make a transfer using an approval. *)
        (TokenQuantityZero (token_kind := payment_token))
        (Request.UseOtherAccountToMakeTransfer to value)
      ) in
    M.Pure true
  end.
