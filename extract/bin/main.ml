open Stdlib

open Coq_extracted
open ITreeDefinition
open Events
open Datatypes
open Any

let rec to_int = function | O -> 0 | S n -> succ (to_int n)
let rec of_int n = assert(n >= 0); if(n == 0) then O else S (of_int (pred n))

let string_of_nat n =
  string_of_int (to_int n)

let string_of_ret a =
  match (Any.downcast a) with
  | Some n -> string_of_nat n
  | None -> raise (Failure "return value is not natural number")

let handle_Event = fun e k ->
  match e with
  | Choose -> raise (Failure "nondeterminism(choose) error")
  | Take -> raise (Failure "nondeterminism(take) error")
  | IO (str, arg) -> 
    match str with
    | "dprint" -> print_endline ("Debug : " ^ (Obj.obj arg)); k (Obj.repr ())
    | "choose_index" -> 
      let n = List.length (Obj.obj arg) in
      let idx = Random.int n in
      k (Obj.repr (of_int idx))
    | "choose_optbool" -> 
      let random_optbool =
        match Random.int 3 with
        | 0 -> None
        | 1 -> Some false
        | _ -> Some true in
      k (Obj.repr random_optbool)
    | _ -> raise (Failure "system call error")

let rec run t =
  match observe t with
  | RetF r -> print_endline ("Return : " ^ (string_of_ret r))
  | TauF t -> run t
  | VisF (e, k) -> handle_Event e (fun x -> run (k x))

let main =
  print_endline "start test";
  Random.self_init ();
  run (Example0.ttitr)
