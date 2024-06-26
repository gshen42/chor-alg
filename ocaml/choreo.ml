(* Relevant manual page: https://ocaml.org/manual/5.1/effects.html *)

open Effect
open Effect.Deep
open Printf

(* Locations *)

type loc = string

(* Located Values *)

type 'a located =
  | Present of 'a
  | Absent

exception Unwrap_absent

let un x =
  match x with
  | Present a -> a
  | Absent -> raise Unwrap_absent

(* Functions for processes to send and receive messages (in binary format) *)

let buffer_file = "buffer"

let send msg dst =
  Out_channel.with_open_bin buffer_file (fun c ->
    printf "* Sending a message to destination %s. Press ENTER to contiunue.\n" dst;
    let _ = read_line () in
    Marshal.to_channel c msg [])

let recv src =
  In_channel.with_open_bin buffer_file (fun c ->
    printf "* Receiving a message from source %s. Type in the message to continue.\n" src;
    let _ = read_line () in
    Marshal.from_channel c)

(* Choreographic operators as effects *)

type _ Effect.t +=
    Comm : string * string * ('a Lazy.t) -> ('a located) Effect.t
  | Announce : string * string list * ('a Lazy.t) -> ('a located) Effect.t
  | Enclave : loc list * (unit -> 'a) -> ('a located) Effect.t

let locally l msg = perform (Comm (l, l, msg))
let comm s r msg = perform (Comm (s, r, msg))

(* Endpoint projection as effect handlers *)

let rec epp : type t. (unit -> t) -> loc -> t = fun c l ->
  match_with c () {
    retc = (fun x -> x);
    exnc = raise;
    effc = fun (type a) (eff : a Effect.t) ->
      match eff with
      | Comm (src, dst, msg) -> Some (fun (k : (a, _) continuation) ->
          if src = l && dst = l then (* l performs a local computation *)
            let x = (Lazy.force msg) in
            continue k (Present x)
          else if src = l then (* l is the sender *)
            let _ = send (Lazy.force msg) dst in
            continue k Absent
          else if dst = l then (* l is receiver *)
            let x = recv src in
            continue k (Present x)
          else (* l is not involved *)
            continue k Absent)
      | Announce (src, dsts, msg) -> Some (fun (k : (a, _) continuation) ->
          if src == l then
            let _ = List.iter (send (Lazy.force msg)) dsts in
            continue k Absent
          else if List.mem l dsts then
            let x = recv src in
            continue k (Present x)
          else
            continue k Absent)
      | Enclave (locs, c)  -> Some (fun (k : (a, _) continuation) ->
          if List.mem l locs then
            continue k (Present (epp c l))
          else
            continue k Absent)
      | _ -> None
  }

let alice, bob, carol = "alice", "bob", "carol"

let foo () =
  let x = perform (Comm (alice, bob, lazy 42)) in
  let y = perform (Comm (bob, alice, lazy (un x + 1))) in
  perform (Comm (alice, alice, lazy (printf "The number I receied is %n\n" (un y))))

let bar () =
  let x = perform (Comm (alice, bob, lazy 42)) in
  perform (Enclave ([bob], (fun () ->
    if (un x) > 40 then
      perform (Comm (bob, bob, lazy (printf "hello")))
    else
      perform (Comm (bob, bob, lazy (printf "world"))))))

let double2 () =
  let x = comm alice bob (lazy (read_int ())) in
  let y = comm bob alice (lazy (un x * 2)) in
  locally alice (lazy (printf "%d\n" (un y)))

let _ = epp double2 alice
