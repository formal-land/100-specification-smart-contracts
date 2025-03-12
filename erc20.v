Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

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

  (* Get the total supply of a token kind *)
  Parameter get_total_supply :
    forall (token_kind : TokenKind),
    list User ->
    World ->
    TokenQuantity token_kind.
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
  (** Ask to transfer token from a user to another one. The result is a boolean stating if the
      transfer was successful, meaning if there were enough funds. *)
  | Transfer (token_kind : TokenKind) (from to : User) (value : TokenQuantity token_kind) : t bool

  (* Apologies for the massive comments, but I am very lost *)
  (* This is a function that takes a token kind and a list of users and returns the total supply of
     the token kind. *)
  | GetTotalSupply (token_kind : TokenKind) (users : list User) : t (TokenQuantity token_kind). 
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
    | GetTotalSupply token_kind users =>
      (Primitives.get_total_supply token_kind users world, world)
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

(** Here we give an application of our DSL above with a representation of a simplified version of
    an [ERC-20] smart contract. *)
Module Erc20.
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
    | Transfer : User -> TokenQuantity token_kind -> t unit
    | TotalSupply : list User -> t (TokenQuantity token_kind).
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
      (* The "transfer" entrypoint *)
      | Command.Transfer to value =>
        (* We run the action to make the transfer and to know if it succeeded *)
        let! is_success := M.MakeAction (Action.Transfer token_kind sender to value) in
        if is_success then
          M.Pure (Some (tt, state))
        else
          M.Pure None
      (* New command - get the total supply of the token *)
      | Command.TotalSupply users => 
        let! total_supply := M.MakeAction (Action.GetTotalSupply token_kind users) in
        M.Pure (Some (total_supply, state))
      end;
  |}.
End Erc20.

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
      (** Transferring tokens is only safe is the account from which we take the money is the same
          as the user running the smart contract *)
      | Action.Transfer token_kind from to value =>
        from = sender
      | Action.GetTotalSupply _ _ => True
      (* Get total supply is safe because it is a read-only operation *)

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

(** Now we will verify that our ERC-20 smart contract is safe *)
Module Erc20IsSafe.
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
      { (* TotalSupply *)
        unfold NoStealing.InRun.t; cbn. (* This is the same as the balanceOf case *)
        apply ActionTree.Forall.Let. { 
          (* The "totalSupply" entrypoint is safe because the action we make to get the total supply
             of a token is safe *)
          apply ActionTree.Forall.MakeAction.
          cbn.
          trivial.
        }
        apply ActionTree.Forall.Pure.
      }
    }
  Qed.
End Erc20IsSafe.
