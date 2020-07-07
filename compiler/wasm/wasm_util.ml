exception Unsupported of string

let unsupported : type a. string -> a = fun s -> raise (Unsupported s)

module Table : sig
  type 'a t (** A table with elements of type ['a]. *)

  val create : initial_offset:int -> element_size:('a -> int) -> 'a t
  (** Create an empty table for elements of type ['a].
   *  The [element_size] function defines the size of a single element.
  *)

  val insert : 'a t -> 'a -> int
  (** Return the offset of a table element within the table. If the element is
   *  not in the table, it will be appended.
  *)

  val lookup : 'a t -> 'a -> int option
  (** Return the offset of a table element within the table if present. *)

  val elements : 'a t -> (int * 'a) list
  (** Return all elements of the table together with their offset.
   *  The returned list is ordered by increasing offset. *)

  val size : 'a t -> int
  (** Return the size of the table. This is also the offset of the next element
   *  that is appended to the table. *)
end = struct
  type pos =
    { offset: int
    ; nth : int
    }

  type 'a t =
    { ht: ('a, pos) Hashtbl.t
    ; mutable size: int
    ; mutable n: int
    ; element_size: 'a -> int
    }

  let create ~initial_offset ~element_size =
    { ht = Hashtbl.create 7
    ; size = initial_offset
    ; element_size
    ; n = 0
    }

  let lookup t el =
    match Hashtbl.find_opt t.ht el with
    | Some pos -> Some pos.offset
    | None -> None

  let insert t el =
    match Hashtbl.find_opt t.ht el with
    | Some pos -> pos.offset
    | None ->
      let offset = t.size in
      Hashtbl.add t.ht el {offset; nth = t.n};
      t.n <- t.n + 1;
      t.size <- t.element_size el + t.size;
      offset

  let elements t =
    let a = Array.make t.n None in
    Hashtbl.iter (fun el pos -> a.(pos.nth) <- Some (pos.offset, el)) t.ht;
    Array.map Option.get a
    |> Array.to_list

  let size t = t.size
end
