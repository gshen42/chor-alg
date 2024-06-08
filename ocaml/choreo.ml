(* Relevant manual page: https://ocaml.org/manual/5.1/effects.html *)

open Effect
open Effect.Deep
open Printf

(* Located Values *)

type 'a located = Present of 'a | Absent

exception Unwrap_empty

let un x =
  match x with
  | Present a -> a
  | Absent  -> raise Unwrap_empty

(* Functions for processes to send and receive messages (in binary format) *)

let send msg dst =
  printf "* Sending a message %s to destination %s. Press ENTER to contiunue.\n" (Marshal.to_string msg []) dst

let recv src =
  printf "* Receiving a message from source %s. Type in the message to continue.\n" src;
  let s = read_line () in
  Marshal.from_string s 0

(* Choreographic operators as effects *)

type _ Effect.t += Comm : string * string * ('a Lazy.t) -> ('a located) Effect.t

(* Endpoint projection as effect handlers *)

let epp c l = match_with c () {
  retc = (fun x -> x);
  exnc = raise;
  effc = fun (type a) (eff : a Effect.t) ->
    match eff with
    | Comm (src, dst, msg) -> Some (fun (k : (a, _) continuation) ->
        if src == l && dst == l
          then continue k (Present (Lazy.force msg))
          else if src == l
            then
              let _ = send (Lazy.force msg) dst in
              continue k Absent
            else if dst == l
              then
                let x = recv src in
                continue k (Present x)
              else continue k Absent)
    | _ -> None
}

let alice, bob, carol = "alice", "bob", "carol"

let foo () =
  let x = perform (Comm (alice, bob, lazy 42)) in
  let y = perform (Comm (bob, alice, lazy (un x + 1))) in
  y

let _ = epp foo bob