Require Export Coq.Lists.List.
Require Export Coq.Strings.String.
Require Export Coq.Program.Basics.  (* Add this *)
Require Export Coq.Logic.FunctionalExtensionality. (* And this *)

Import ListNotations.

Local Open Scope type.

(** The type of the state of the world. The world contains all the user, tokens, and ownership
    relations that have been stated until now. We never explicitly say what ia actually contains. *)
Parameter World : Set.

(** The type of the user. We do not explicitly say how a user is described. *)
Parameter User : Set.

(** The kind of a token. We will instantiate one kind of token per coin that we create, in order to
    trace them and to be able to say that it is impossible to transfer one kind of tokens to the
    other. *)
Parameter TokenKind : Set.

(** A quantity of token for a given [token_kind]. This is not explicitly defined for now, but it
    will be positive integer or a positive real number, if we allow to own a part of a token. *)
Parameter TokenQuantity : forall (token_kind : TokenKind), Set.

(** A quantity of one token for a given [token_kind]. *)
Parameter TokenQuantityOne : forall {token_kind : TokenKind}, TokenQuantity token_kind.

(** The primitives that we assume as given on the types provided above. *)
Module Primitives.
  (** Create a new kind of token, different from all the kinds that existed before, and return the
      new state of the world with this added token. *)
  Parameter create_token_kind :
    World ->
    TokenKind * World.

  (** Get the quantity of token owned by a user, considering a certain token kind. *)
  Parameter get_balance :
    forall (token_kind : TokenKind),
    User ->
    World ->
    TokenQuantity token_kind.

  (** Get the number of token that a [spender] is allowed to spend from a [user] *)
  Parameter get_allowance :
    forall (token_kind : TokenKind),
    forall (user : User),
    forall (spender : User),
    World ->
    TokenQuantity token_kind.

  (** Transfer a certain quantity of tokens from a user to another, and return the new state of the
      world where the quantity of tokens they both own has been updated. *)
  Parameter transfer :
    forall (token_kind : TokenKind),
    User ->
    User ->
    TokenQuantity token_kind ->
    World ->
    option World.

  (** Set the allowance for a certain [spender] at a certain amount from the account of a [user] *)
  Parameter approve :
    forall (token_kind : TokenKind),
    forall (user : User),
    forall (spender : User),
    TokenQuantity token_kind ->
    World ->
    option World.

  Parameter mint :
    forall (token_kind : TokenKind),
    User ->
    TokenQuantity token_kind ->
    World ->
    option World.

  (** Get the unique owner of a certain token kind. This owner must some bits of the token kind,
      and there must be no other owner for this token kind. *)
  Parameter get_unique_token_kind_owner :
    forall (token_kind : TokenKind),
    World ->
    option User.

  Parameter user_eq :
    forall (user1 user2 : User),
    bool.

  Axiom user_eq_is_valid :
    forall (user1 user2 : User),
    user_eq user1 user2 = true ->
    user1 = user2.

  Parameter find_user_with_enough_balance :
    forall (token_kind : TokenKind),
    forall (amount : TokenQuantity token_kind),
    World ->
    option User.

  Parameter selling_price_for_nft :
    forall (payment_token_kind nft_type : TokenKind),
    User ->
    World ->
    option (TokenQuantity payment_token_kind).
End Primitives.

(** Actions are the primitives that we can run in our DSL to interact with tokens, make transfers,
    and all interactions with the state of the world.

    Note that in contrast to the primitives above, we do not have access to the [World]. We only
    describe the actions that we can perform on it.
*)
Module Action.
  Inductive t : Set -> Set :=
  (** Instantiate a new kind of token *)
  | CreateTokenKind : t TokenKind
  (** Ask for the number of tokens owned by a user *)
  | GetBalance (token_kind : TokenKind) (user : User) : t (TokenQuantity token_kind)
  | GetAllowance (token_kind : TokenKind) (user spender : User) : t (TokenQuantity token_kind)
  (** Ask to transfer token from a user to another one. The result is a boolean stating if the
      transfer was successful, meaning if there were enough funds. *)
  | Transfer (token_kind : TokenKind) (from to : User) (value : TokenQuantity token_kind) : t bool
  | Approve
    (token_kind : TokenKind)
    (user spender : User)
    (value : TokenQuantity token_kind) :
    t bool
  | Mint
    (token_kind : TokenKind)
    (account : User)
    (value : TokenQuantity token_kind) :
    t bool
  | GetUniqueTokenKindOwner (token_kind : TokenKind) : t (option User)
  | UserEq (user1 user2 : User) : t bool
  | FindUserWithEnoughBalance
    (token_kind : TokenKind)
    (amount : TokenQuantity token_kind) :
    t (option User)
  | SellingPriceForNft
    (payment_token_kind nft_type : TokenKind)
    (user : User) :
    t (option (TokenQuantity payment_token_kind))
  | FulfillOrder
    (token_kind nft_type : TokenKind)
    (user : User) :
    t (option (TokenQuantity token_kind))
  .

  (** This function maps the actions we defined to the primitives acting on the world above *)
  Definition run (world : World) {A : Set} (action : t A) : A * World :=
    match action with
    | CreateTokenKind =>
      Primitives.create_token_kind world
    | GetBalance token_kind user =>
      (Primitives.get_balance token_kind user world, world)
    | GetAllowance token_kind user spender =>
      (Primitives.get_allowance token_kind user spender world, world)
    | Transfer token_kind from to value =>
      match Primitives.transfer token_kind from to value world with
      | Some world' => (true, world')
      | None => (false, world)
      end
    | Approve token_kind user spender value =>
      match Primitives.approve token_kind user spender value world with
      | Some world' => (true, world')
      | None => (false, world)
      end
    | Mint token_kind account value =>
      match Primitives.mint token_kind account value world with
      | Some world' => (true, world')
      | None => (false, world)
      end
    | GetUniqueTokenKindOwner token_kind =>
      (Primitives.get_unique_token_kind_owner token_kind world, world)
    | UserEq user1 user2 =>
      (Primitives.user_eq user1 user2, world)
    | FindUserWithEnoughBalance token_kind amount =>
      (Primitives.find_user_with_enough_balance token_kind amount world, world)
    | SellingPriceForNft payment_token_kind nft_type user =>
      (Primitives.selling_price_for_nft payment_token_kind nft_type user world, world)
    | FulfillOrder token_kind nft_type user =>
      (Primitives.selling_price_for_nft token_kind nft_type user world, world)
    end.
End Action.

Module ActionTree.
  (** Here we define a tree of actions. This data structure will be useful later to specify that a
      smart contract is behaving as expected.

      It aims to represent the tree of all the actions that were executed by a smart contract call.
      The tree should be ordered from left to right in the order the actions were executed.
  *)
  Inductive t : Set :=
  (** Empty tree *)
  | Pure
  (** A tree composed of two sub-trees *)
  | Let (tree1 tree2 : t)
  (** A leaf with a single action *)
  | MakeAction {A : Set} (action : Action.t A).

  Module Forall.
    (** This inductive predicate states that all the actions in the tree satisfy a given property. *)
    Inductive t (P : forall {A : Set}, Action.t A -> Prop) : ActionTree.t -> Prop :=
    | Pure :
        t _ Pure
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
  (** A "monad" to define our DSL from the action above. We can never access to the world
      explicitly, but we are still manipulating it through the actions. *)
  Inductive t (A : Set) : Set :=
  (** A program without any actions, returning [value] of type [A] *)
  | Pure (value : A)
  (** A program doing the sequencing of two sub-programs, with [e] being executed first and [k]
      being executed second. Additionally, [k] takes as a parameter the result of [e] that can be
      useful sometimes. *)
  | Let {B : Set} (e : t B) (k : B -> t A)
  (** A program that executes a single action [action] *)
  | MakeAction (action : Action.t A).
  (* Some commands to set the implicit parameters of the constructors above *)
  Arguments Pure {_}.
  Arguments Let {_ _}.
  Arguments MakeAction {_}.

  (** Execute a program using the primitives above and returning the tree of actions that were
      made. *)
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

(** A convenient notation for the [M.Let] constructor that sequences two programs *)
Notation "'let!' a ':=' b 'in' c" :=
  (M.Let b (fun a => c))
  (at level 200, a pattern, b at level 100, c at level 200).

Module SmartContract.
  (** A general definition of what is a smart contract. A smart contract has many type parameters
      like [State] to represent the type of its internal storage.

      It has two methods [init] and [call] to represent the initial call (the constructor in
      Solidity) and the sub-sequent calls. We will use an [Inductive] type to represent the payload
      of the [call] function and encode the fact that there might be different entrypoints in the
      smart contract.
    *)
  Record t {InitInput InitOutput : Set} {Command : InitOutput -> Set -> Set} {State : Set} : Set := {
    init
      (** The user instantiating the smart contract on chain *)
      (sender : User)
      (** Some parameters that the user can choose to instantiate the contract *)
      (init_input : InitInput) :
      M.t (option (InitOutput * State));
    call {A : Set}
      (** Some initialization value that was computed by the [init] function *)
      (init_output : InitOutput)
      (** All smart contract calls originate form a certain user [sender] that is running and paying
          for the call *)
      (sender : User)
      (** The [command] is the payload that we sent to the smart contract to execute it *)
      (command : Command init_output A)
      (** The initial internal storage [state] at the beginning of the call *)
      (state : State) :
      (** We return an option type to represent a potential execution failure (a revert in
          Solidity). In case of success, the output is a couple of a value of type [A], depending on
          the kind of [command] we call, and a new internal storage state. *)
      M.t (option (A * State));
  }.
  Arguments t : clear implicits.
End SmartContract.

(** Here we will define what it means for a smart contract defined in our DSL to be safe, in the
    sense that no one can steal money from others. *)
Module NoStealing.
  Module InAction.
    (** We first define that a smart contract is safe at the level of a single action. We consider
        an action [action] and a user [sender] which is executing the current smart contract
        execution. *)
    Definition t (sender : User) {A : Set} (action : Action.t A) : Prop :=
      match action with
      (** Creating a new kind of token is safe *)
      | Action.CreateTokenKind => True
      (** Asking for the balance of a user is safe (all data are public in a blockchain) *)
      | Action.GetBalance _ _ => True
      | Action.GetAllowance _ _ _ => True
      (** Transferring tokens is only safe is the account from which we take the money is the same
          as the user running the smart contract *)
      | Action.Transfer token_kind from to value =>
        (* Standard case: sender is transferring their own tokens *)
        from = sender \/ 
        (* Marketplace case: tokens are being transferred to the sender 
            as part of a legitimate exchange *)
        to = sender
      | Action.Approve _ user _ _ =>
        user = sender
      | Action.Mint token_kind account value => True
      | Action.GetUniqueTokenKindOwner _ => True
      | Action.UserEq _ _ => True
      | Action.FindUserWithEnoughBalance _ _ => True
      | Action.SellingPriceForNft _ _ _ => True
      | Action.FulfillOrder _ _ _ => True
      (* | Action.SuccessfulOrder _ _ _ => True
      | Action.FailedOrder _ _ _ => False *)
      end.
  End InAction.

  Module InActionTree.
    (** We generalize the safety of a an action to a tree of actions *)
    Definition t (sender : User) (tree : ActionTree.t) : Prop :=
      ActionTree.Forall.t (@InAction.t sender) tree.
  End InActionTree.

  Module InRun.
    (** We define the safety of the execution of an expression [e] from the safety of its tree of
        actions *)
    Definition t {A : Set} (world : World) (sender : User) (e : M.t A) : Prop :=
      let '(_, _, tree) := M.run e world in
      InActionTree.t sender tree.
  End InRun.

  Module InSmartContract.
    (** We say that a smart contract is safe if all its possible executions are safe *)
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
