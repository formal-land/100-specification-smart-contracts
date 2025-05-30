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

Parameter TokenQuantityZero : forall {token_kind : TokenKind}, TokenQuantity token_kind.

Parameter token_kind_eq : forall (token_kind1 token_kind2 : TokenKind), bool.

Parameter token_quantity_leq : forall {token_kind : TokenKind},
  TokenQuantity token_kind ->
  TokenQuantity token_kind ->
  bool.

(** We return [None] is the result of the substraction is negative. *)
Parameter token_quantity_sub : forall {token_kind : TokenKind},
  TokenQuantity token_kind ->
  TokenQuantity token_kind ->
  option (TokenQuantity token_kind).

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

  (** Transfer a certain quantity of tokens from a user to another, and return the new state of the
      world where the quantity of tokens they both own has been updated. *)
  Parameter transfer :
    forall (token_kind : TokenKind),
    User ->
    User ->
    TokenQuantity token_kind ->
    World ->
    option World.

  Parameter user_eq :
    forall (user1 user2 : User),
    bool.

  Parameter register_promise_for_user :
    forall {Promise : Set},
    forall (user : User),
    forall (promise : Promise),
    World ->
    World.

  Parameter emit_request :
    forall {payment_token : TokenKind},
    forall {Promises Request : Set},
    forall (to_selector : User -> Promises -> Prop),
    forall (payment : TokenQuantity payment_token),
    forall (request : Request),
    World ->
    option World.
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
  | GetBalance
    (token_kind : TokenKind)
    (user : User) :
    t (TokenQuantity token_kind)
  (** Ask to transfer token from a user to another one. The result is a boolean stating if the
      transfer was successful, meaning if there were enough funds. *)
  | Transfer
    (token_kind : TokenKind)
    (to : User)
    (value : TokenQuantity token_kind) :
    t bool
  | UserEq (user1 user2 : User) : t bool
  | RegisterPromiseForUser
      {Promise : Set}
      (promise : Promise) :
      t unit
  | EmitRequest
      {payment_token : TokenKind}
      {Promises Request : Set}
      (** A property to select the user to which we are sending the request. If no users are found,
          the request returns [false]. If more than one user is found, the request is sent to
          exactly one of them.
      *)
      (to_selector : User -> Promises -> Prop)
      (payment : TokenQuantity payment_token)
      (request : Request) :
      t bool.

  (** This function maps the actions we defined to the primitives acting on the world above *)
  Definition run (world : World) (user : User) {A : Set} (action : t A) :
      A * World :=
    match action with
    | CreateTokenKind =>
      Primitives.create_token_kind world
    | GetBalance token_kind user =>
      (Primitives.get_balance token_kind user world, world)
    | Transfer token_kind to value =>
      match Primitives.transfer token_kind user to value world with
      | Some world' => (true, world')
      | None => (false, world)
      end
    | UserEq user1 user2 =>
      (Primitives.user_eq user1 user2, world)
    | RegisterPromiseForUser promise =>
      (tt, Primitives.register_promise_for_user user promise world)
    | EmitRequest to_selector payment request =>
      match Primitives.emit_request to_selector payment request world with
      | Some world' => (true, world')
      | None => (false, world)
      end
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
    Inductive t (P : forall {A : Set}, Action.t A -> Prop) :
      ActionTree.t -> Prop :=
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
      made. We have access to the current user executing the code in context. *)
  Fixpoint run {A : Set} (e : t A) (world : World) (user : User) :
      A * World * ActionTree.t :=
    match e with
    | Pure value => (value, world, ActionTree.Pure)
    | Let e k =>
      let '(x, world', tree1) := run e world user in
      let '(result, world'', tree2) := run (k x) world' user in
      (result, world'', ActionTree.Let tree1 tree2)
    | MakeAction action =>
      let '(result, world') := Action.run world user action in
      (result, world', ActionTree.MakeAction action)
    end.
End M.

(** A convenient notation for the [M.Let] constructor that sequences two programs *)
Notation "'let!' a ':=' b 'in' c" :=
  (M.Let b (fun a => c))
  (at level 200, a pattern, b at level 100, c at level 200).
