Require Import FullSpecificationSmartContracts.Promises.Common.
Require Import Coq.Classes.RelationClasses.

Local Open Scope bool_scope.

Module Promises.
  Inductive t {payment_token : TokenKind} : Set :=
  | Nothing : t
  | CanSell
      (nft_token : TokenKind)
      (cost : TokenQuantity payment_token) :
      t.
  Arguments t : clear implicits.
End Promises.

Module Request.
  Inductive t : Set :=
  | Buy (ntf_token : TokenKind) : t.
End Request.

Definition execute_request {payment_token : TokenKind}
    (sender : User)
    (payment : TokenQuantity payment_token)
    (promises : Promises.t payment_token)
    (request : Request.t) :
  M.t bool :=
  match request with
  | Request.Buy nft_token =>
    match promises with
    | Promises.Nothing =>
      M.Pure false
    | Promises.CanSell nft_token' cost =>
      if token_kind_eq nft_token nft_token' then
        if token_quantity_leq cost payment then
          let! _ :=
            M.MakeAction (Action.Transfer nft_token sender TokenQuantityOne) in
          let! _ :=
            M.MakeAction (Action.RegisterPromiseForUser (Promises.Nothing (payment_token := payment_token))) in
          M.Pure true
        else
          M.Pure false
      else
        M.Pure false
    end
  end.
