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

Module Entrypoint.
  Inductive t {payment_token : TokenKind} : Set :=
  | Buy (nft_token : TokenKind) (payment : TokenQuantity payment_token) : t
  | Propose (nft_token : TokenKind) (cost : TokenQuantity payment_token) : t.
  Arguments t : clear implicits.
End Entrypoint.

Definition execute_entrypoint {payment_token : TokenKind}
    (sender : User)
    (promises : Promises.t payment_token)
    (entrypoint : Entrypoint.t payment_token) :
  M.t bool :=
  match entrypoint with
  | Entrypoint.Buy nft_token payment =>
    let request := Request.Buy nft_token in
    let seller_selector (user : User) (promises : Promises.t payment_token) :=
      match promises with
      | Promises.CanSell nft_token' cost =>
        nft_token = nft_token' /\
        token_quantity_leq cost payment = true
      | _ => False
      end in
    let! _ :=
      M.MakeAction (Action.EmitRequest seller_selector payment request) in
    M.Pure true
  | Entrypoint.Propose nft_token cost =>
    let! _ :=
      M.MakeAction (Action.RegisterPromiseForUser (Promises.CanSell nft_token cost)) in
    M.Pure true
  end.
