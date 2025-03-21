Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z.

(* pure function example *)
Definition plus_two (n : nat) : nat :=
  n + 2.

(* Functions with side effects: not possible in Coq but possible in other programming languages *)
(* side-effect 1 : input-output operation *)
(* Definition get_current_time_in_seconds : nat :=
  Time.get_current_time (). *)

(* side-effect 2: modify a state *)

(* Definition global_bar := 2.

Definition increment () : unit :=
  global_var += 1.

(* side-effect 3: propagate an error *)

(* side-effect: errors *)
Definition divide_by_zero n :=
  n / 0. *)

(* To represent side effects in purely functional language: monads *)

(* Monads *)
(* M A: monadic type: "computations that returns a value of type A" *)
(* Two primitive operations *)
(* return/pure: A -> M A : to convert pure operations to monadic operations *)
(* bind: M A -> (A -> M B) -> M B : to sequence two monadic operations *)

(* Example of monads: *)
(* Error *)
Inductive ErrorMonad (A : Set) : Set :=
| Success (value : A)
| Error (message : string).
Arguments Success {_}.
Arguments Error {_}.

Definition pure_error_monad {A : Set} (value : A) : ErrorMonad A :=
  Success value.

Definition bind_error_monad {A B : Set} (first : ErrorMonad A) (second : A -> ErrorMonad B) : ErrorMonad B :=
  match first with
  | Success value => second value
  | Error message => Error message
  end.

Definition division_by_something (z1 z2 : Z) : ErrorMonad Z :=
  if z2 =? 0 then
    Error "division by zero"
  else
    Success (z1 / z2).

(* a1 / a2 + b1 / b2 *)
Definition sum_of_two_divisions (a1 a2 b1 b2 : Z) : ErrorMonad Z :=
  bind_error_monad (division_by_something a1 a2) (fun x =>
    bind_error_monad (division_by_something b1 b2) (fun y =>
      pure_error_monad (x + y)%Z
    )
  ).

Compute sum_of_two_divisions 4 3 2 1. (* => Success value *)
Compute sum_of_two_divisions 4 0 2 1. (* => Error message *)

(* IO example *)
Inductive PossibleIO : Set -> Set :=
| GetTime : PossibleIO Z
| ReadFile (filename : string) : PossibleIO (option string)
| WriteFile (filename : string) (new_content : string) : PossibleIO bool.

(* With the IO monad, everything is data, we do not actually compute anything *)
Inductive IO (A : Set) : Set :=
| Pure (value : A)
| Impure (io : PossibleIO A)
| Bind {B : Set} (first : IO B) (second : B -> IO A).
Arguments Pure {_}.
Arguments Impure {_}.
Arguments Bind {_ _}.

Definition get_time : IO Z :=
  Impure GetTime.

Definition read_file_and_return_duration (filename : string) : IO Z :=
  Bind get_time (fun initial_time =>
  Bind (Impure (ReadFile filename)) (fun _ =>
  Bind get_time (fun final_time =>
    Pure (final_time - initial_time)
  ))).

(* The output is very verbose, as this is the code above that is printed expanding all the
   definitions, but nothing is computed. *)
Compute read_file_and_return_duration "example.txt".

(* We can still specify things about programs in the IO monands, even if we cannot compute. Here is
   an example of a simple function that checks if a computation is actually just a pure value
   without any IO. *)
Definition is_IO_without_IO {A : Set} (computation : IO A) : bool :=
  match computation with
  | Pure _ => true
  | _ => false
  end.

Compute is_IO_without_IO get_time. (* => false *)
Compute is_IO_without_IO (Pure (1 + 2)%Z). (* => true *)

(* State monad *)
(* The idea is to add the input state as an additional parameter to the functions, and the output
   state as an addition result *)
Definition StateMonad (State : Set) (A : Set) : Set :=
  State (* input *) -> A * State (* output *).

(* We assume that our state is a global variable of type [Z] *)
Definition State : Set :=
  Z.

(* We do not change the state in the pure operator *)
Definition pure_state {A : Set} (value : A) : StateMonad State A :=
  fun state => (value, state).

(* We propagate the updated state in the bind operator *)
Definition bind_state {A B : Set} (first : StateMonad State A) (second : A -> StateMonad State B) : StateMonad State B :=
  fun state =>
    let (value, new_state) := first state in
    second value new_state.

(* We can now define the increment operation *)
Definition increment : StateMonad State unit :=
  fun state => (tt, state + 1).

(* We can apply the increment three times *)
Definition increment_three_times : StateMonad State unit :=
  bind_state increment (fun _ =>
  bind_state increment (fun _ =>
  bind_state increment (fun _ =>
    pure_state tt
  ))).

Definition initial_state : State :=
  12.

Compute increment initial_state. (* => (tt, 13  ) *)
Compute increment_three_times initial_state. (* => (tt, 15) *)
