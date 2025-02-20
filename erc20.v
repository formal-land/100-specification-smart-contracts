Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Import ListNotations.

Local Open Scope type.

Parameter World : Set.
Parameter User : Set.
Parameter TokenKind : Set.
Parameter TokenQuantity : forall (token_kind : TokenKind), Set.

Module Primitives.
  Parameter create_token_kind : World -> TokenKind * World.

  (** Get the quantity of token for a certain kind and a user *)
  Parameter get_balance :
    forall (token_kind : TokenKind),
    User ->
    World -> TokenQuantity token_kind.

  (** Transfer a certain quantity of tokens from a user to another *)
  Parameter transfer :
    forall (token_kind : TokenKind),
    User -> User -> TokenQuantity token_kind ->
    World -> option World.
End Primitives.

Module Action.
  Inductive t : Set -> Set :=
  | CreateTokenKind : t TokenKind
  | GetBalance (token_kind : TokenKind) (user : User) : t (TokenQuantity token_kind)
  | Transfer (token_kind : TokenKind) (from to : User) (value : TokenQuantity token_kind) : t bool.

  Definition run (world : World) {A : Set} (action : t A) : A * World :=
    match action with
    | CreateTokenKind =>
      Primitives.create_token_kind world
    | GetBalance token_kind user =>
      (Primitives.get_balance token_kind user world, world)
    | Transfer token_kind from to value =>
      match Primitives.transfer token_kind from to value world with
      | Some world' => (true, world')
      | None => (false, world)
      end
    end.
End Action.

Module ActionTree.
  Inductive t : Set :=
  | Pure
  | Let (tree1 tree2 : t)
  | MakeAction {A : Set} (action : Action.t A).

  Module Forall.
    Inductive t (P : forall {A : Set}, Action.t A -> Prop) : ActionTree.t -> Prop :=
    | Pure : t _ Pure
    | Let (tree1 tree2 : ActionTree.t) :
        t _ tree1 ->
        t _ tree2 ->
        t _ (Let tree1 tree2)
    | MakeAction {A : Set} (action : Action.t A) :
        P action ->
        t _ (MakeAction action).
  End Forall.
End ActionTree.

Module M.
  (** A free monad where we can run actions about the world but not manipulate it directly *)
  Inductive t (A : Set) : Set :=
  | Pure (value : A)
  | Let {B : Set} (e : t B) (k : B -> t A)
  | MakeAction (action : Action.t A).
  Arguments Pure {_}.
  Arguments Let {_ _}.
  Arguments MakeAction {_}.

  Fixpoint run {A : Set} (e : t A) (world : World) : A * World * ActionTree.t :=
    match e with
    | Pure value => (value, world, ActionTree.Pure)
    | Let e k =>
      let '(x, world', tree1) := run e world in
      let '(result, world'', tree2) := run (k x) world' in
      (result, world'', ActionTree.Let tree1 tree2)
    | MakeAction action =>
      let '(result, world') := Action.run world action in
      (result, world', ActionTree.MakeAction action)
    end.
End M.

Notation "'let!' a ':=' b 'in' c" :=
  (M.Let b (fun a => c))
  (at level 200, a pattern, b at level 100, c at level 200).

Module SmartContract.
  Record t {InitInput InitOutput : Set} {Command : InitOutput -> Set -> Set} {State : Set} : Set := {
    init
      (sender : User)
      (init_input : InitInput) :
      M.t (option (InitOutput * State));
    call {A : Set}
      (init_output : InitOutput)
      (sender : User)
      (command : Command init_output A)
      (state : State) :
      M.t (option (A * State));
  }.
  Arguments t : clear implicits.
End SmartContract.

Module Erc20.
  Definition InitInput : Set :=
    string * string.

  Definition InitOutput : Set :=
    TokenKind.

  Module State.
    Record t : Set := {
      name : string;
      symbol : string;
    }.
  End State.

  Module Command.
    Inductive t {token_kind : InitOutput} : Set -> Set :=
    | BalanceOf : User -> t (TokenQuantity token_kind)
    | Transfer : User -> TokenQuantity token_kind -> t unit.
    Arguments t : clear implicits.
  End Command.

  Definition smart_contract :
    SmartContract.t
      InitInput
      InitOutput
      Command.t
      State.t :=
  {|
    SmartContract.init _sender '(name, symbol) :=
      let! token_kind := M.MakeAction Action.CreateTokenKind in
      let state := {|
        State.name := name;
        State.symbol := symbol;
      |} in
      M.Pure (Some (token_kind, state));
    SmartContract.call A token_kind sender command state :=
      match command in Command.t _ A return M.t (option (A * _)) with
      | Command.BalanceOf user =>
        let! balance := M.MakeAction (Action.GetBalance token_kind user) in
        M.Pure (Some (balance, state))
      | Command.Transfer to value =>
        let! is_success := M.MakeAction (Action.Transfer token_kind sender to value) in
        if is_success then
          M.Pure (Some (tt, state))
        else
          M.Pure None
      end;
  |}.
End Erc20.

Module NoStealing.
  Module InAction.
    Definition t (sender : User) {A : Set} (action : Action.t A) : Prop :=
      match action with
      | Action.CreateTokenKind => True
      | Action.GetBalance _ _ => True
      | Action.Transfer token_kind from to value =>
        from = sender
      end.
  End InAction.

  Module InActionTree.
    Definition t (sender : User) (tree : ActionTree.t) : Prop :=
      ActionTree.Forall.t (@InAction.t sender) tree.
  End InActionTree.

  Module InRun.
    Definition t {A : Set} (world : World) (sender : User) (e : M.t A) : Prop :=
      let '(_, _, tree) := M.run e world in
      InActionTree.t sender tree.
  End InRun.

  Module InSmartContract.
    Record t {InitInput InitOutput : Set} {Command : InitOutput -> Set -> Set} {State : Set}
        (smart_contract : SmartContract.t InitInput InitOutput Command State) :
        Prop := {
      init (world : World) (sender : User) (init_input : InitInput) :
        InRun.t world sender (smart_contract.(SmartContract.init) sender init_input);
      call {A : Set}
        (world : World) (sender : User) (init_output : InitOutput) (command : Command init_output A) (state : State) :
        InRun.t world sender (smart_contract.(SmartContract.call) init_output sender command state);
    }.
  End InSmartContract.
End NoStealing.

Module Erc20IsSafe.
  Lemma is_safe : NoStealing.InSmartContract.t Erc20.smart_contract.
  Proof.
    constructor; intros; cbn.
    { (* init *)
      destruct init_input as [name symbol].
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
      { (* BalanceOf *)
        unfold NoStealing.InRun.t; cbn.
        apply ActionTree.Forall.Let. {
          apply ActionTree.Forall.MakeAction.
          cbn.
          trivial.
        }
        apply ActionTree.Forall.Pure.
      }
      { (* Transfer *)
        unfold NoStealing.InRun.t; cbn.
        destruct Primitives.transfer; cbn.
        { apply ActionTree.Forall.Let. {
            apply ActionTree.Forall.MakeAction.
            cbn.
            reflexivity.
          }
          apply ActionTree.Forall.Pure.
        }
        { apply ActionTree.Forall.Let. {
            apply ActionTree.Forall.MakeAction.
            cbn.
            reflexivity.
          }
          apply ActionTree.Forall.Pure.
        }
      }
    }
  Qed.
End Erc20IsSafe.
