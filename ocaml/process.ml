(*
  This module defines a cooperative process library using effect handlers.
  Multiple processes can run concurrently and exchange messages, and they're
  the result of endpoint projection of a choreography.
*)

open Effect
open Effect.Deep

type id = string

type _ Effect.t +=
    Send : bytes * id -> unit Effect.t
  | Recv : id -> bytes Effect.t

type 'a prog = {id: id; f: unit -> 'a}

type _ task =
    Completed : 'a -> 'a task
  | Failed : exn -> 'a task
  | WaitToSend : {msg: bytes; dst: string; cont: (unit, 'a task) continuation } -> 'a task
  | WaitToRecv : {src: string; cont: (bytes, 'a task) continuation } -> 'a task

let is_done task =
  match task with
    Completed _ -> true
  | Failed _  -> true
  | _ -> false

type 'a proc = {id: id; t: 'a task}

let step {id; f} =
  let t = match_with f () {
    retc = (fun v -> Completed v);
    exnc = (fun e -> Failed e);
    effc = fun (type b) (eff: b Effect.t) ->
      match eff with
        Send (msg, dst) -> Some (fun (cont: (b, _) continuation) ->
          WaitToSend {msg; dst; cont})
      | Recv src -> Some (fun (cont: (b, _) continuation) ->
          WaitToRecv {src; cont})
      | _ -> None
  }
  in
  {id; t}

let xchg ({id = id1; t = t1}, {id = id2; t = t2}) =
    match (t1, t2) with
      (WaitToSend {msg; dst; cont = cont1}, WaitToRecv {src; cont = cont2}) when dst = id2 && src == id1 ->
        Some ({id = id1; t = continue cont1 ()}, {id = id2; t = continue cont2 msg})
    | (WaitToRecv {src; cont = cont1}, WaitToSend {msg; dst; cont = cont2}) when dst = id2 && src == id1 ->
        Some ({id = id1; t = continue cont1 msg}, {id = id2; t = continue cont2 ()})
    | _ ->
        None

let run progs =
  let tasks = Hashtbl.create (List.length progs) in
  let _ = List.iter (fun {id; f} -> Hashtbl.add tasks id (step f)) progs in
  ()