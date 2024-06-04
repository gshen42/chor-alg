(* Relevant manual page: https://ocaml.org/manual/5.1/effects.html *)

open Effect
open Effect.Deep

open Process

(* Located Values *)

type 'a located = Here of 'a | Empty

exception Unwrap_empty

let un x =
  match x with
  | Here a -> a
  | Empty  -> raise Unwrap_empty

(* Define choreographic operators as effects and endpont projection as effect handlers *)

type _ Effect.t += Comm : string * string * 'a -> ('a located) Effect.t

let alice, bob, carol = "alice", "bob", "carol"

let foo () =
  let x = perform (Comm (alice, bob, 42)) in
  let y = perform (Comm (alice, bob, un x + 1)) in
  y
