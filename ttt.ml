type player = O | X

type cell = Empty | P of player

type grid = cell list list

module ListUtils = struct 
let rec foldl (f: 'b -> 'a -> 'b) (v: 'b) (l: 'a list) : 'b =
  match l with
  | [] -> v
  | h::t -> foldl (f) (f v h) (t)

let rec get_index (element: 'a) (lst: 'a list) : int option =
  match lst with
  | [] -> None
  | h::t when h = element -> Some 0
  | h::t -> 
    match (get_index element t) with
    | None -> None
    | Some i -> Some (i+1)

let rec get_element (index: int) (l: 'a list) : 'a option = 
  match (index, l) with
  | (_, []) -> None
  | (0, h::t) -> Some h
  | (i, h::t) -> get_element (i-1) t


let rec forall (pred: 'a -> bool) (l: 'a list) : bool = 
  foldl (fun x y -> x && pred (y)) (true) (l)

let length (l: 'a list) : int = 
  let rec length_helper (lst: 'a list) (acc: int) : int = 
    match lst with
    | [] -> acc
    | h::t -> length_helper (t) (acc + 1) in
  length_helper l 0

(* range returns a list with values from 0 to (n-1) *)
let range b = 
  let rec range_helper (a: int) (b: int) : int list = 
    match (a >= b) with
    | true -> []
    | false -> a :: range_helper (a+1) (b)
  in range_helper 0 b


let if_exists (pred: 'a -> bool) (lst: 'a list) : bool =
  foldl (fun x y -> x || pred(y)) (false) (lst)

end;;

module TicTacToe = struct

let opponent (p: player) = 
  match p with
  | X -> O
  | O -> X

let check_line (p: player) (row: cell list)  = 
  ListUtils.forall (fun x -> if x = P(p) then true else false) (row)

let is_winning_row (p: player) (g: grid) = 
  ListUtils.if_exists (check_line p) (g)

let is_winning_diagonal (p: player) (g: grid): bool = 
  match g with
  | [] -> false
  | [row1;row2;row3] -> 
    if (ListUtils.get_element (0) (row1) = Some (P p) && ListUtils.get_element (1) (row2) = Some (P p) && ListUtils.get_element (2) (row3) = Some (P p)) 
      || (ListUtils.get_element (2) (row1) = Some (P p) && ListUtils.get_element (1) (row2) = Some (P p) && ListUtils.get_element (0) (row3) = Some (P p))
    then true else false
  | _ -> failwith "Invalid Grid"
  

(* function to check if any column in g is all O *)
let is_winning_column (p: player) (g: grid) : bool = 
  match g with
  | [] -> false
  | row1::_ -> 
      let check_ith_elements (p: player) (i) : bool =
        ListUtils.forall (fun row -> ListUtils.get_element i row = Some (P p)) g (*check_ith_element checks if the index i in all rows in g is the same.*)
      in
      ListUtils.if_exists (check_ith_elements (p)) (ListUtils.range (ListUtils.length row1)) (*if exists takes a predicate and a list and checks if the predicate holds for at least one element in a list
        here the predicate is check_ith_element first takes in 0 then 1 then 2 until length(row 1). if there is at least one index where all the rows have O in that index, it returns true.*)

let is_winning_grid (p: player) (g: grid) : bool =
  if (is_winning_column p g) || (is_winning_diagonal p g) || (is_winning_row p g) = true then true else false


(* this function will return all moves for O that are possible to play when one or more cells are empty as cell list list. *)

(* 
requires: a row
ensures: that it returns all possible unique placements for O in the given row as different elements of a list.
*)

let replace_empty_cell (p: player) (row: cell list) : cell list list = 
  match row with
  | [cell1; cell2; cell3] when cell1 <> Empty && cell2 <> Empty && cell3 <> Empty -> [[cell1; cell2; cell3]]
  | [Empty; cell2; cell3] when cell2 <> Empty && cell3 <> Empty -> [[P p; cell2; cell3]]
  | [cell1; Empty; cell3] when cell1 <> Empty && cell3 <> Empty -> [[cell1; P p; cell3]]
  | [cell1; cell2; Empty] when cell1 <> Empty && cell2 <> Empty -> [[cell1; cell2; P p]]
  | [Empty; Empty; cell3] when cell3 <> Empty -> [[P p; Empty; cell3]; [Empty; P p; cell3]]
  | [cell1; Empty; Empty] when cell1 <> Empty -> [[cell1; P p; Empty]; [cell1; Empty; P p]]
  | [Empty; cell2; Empty] when cell2 <> Empty -> [[P p; cell2; Empty]; [Empty; cell2; P p]]
  | [Empty; Empty; Empty] -> [[Empty; Empty; P p]; [Empty; P p; Empty]; [P p; Empty; Empty]]
  | _ -> failwith "invalid row." 

(* 
requires: three rows of a grid.
ensures: checks if row1 has an empty cell and if it does then it returns the possible places to play O on, if there is one place to play O, a new row is returned for r1 rest remain same. if there are more than one move possible, then the grid list contains more than one grid. 
essentially, it is the set of all playable positions and thus grids.
*)

let create_new_grids_r1 (p: player) (r1: cell list) (r2: cell list) (r3: cell list) : grid list =
  match replace_empty_cell p r1 with
  | [a] -> [[a; r2; r3]]
  | [a;b] -> [[a; r2; r3]; [b; r2; r3]]
  | [a;b;c] -> [[a; r2; r3];[b;r2;r3]; [c;r2;r3]]
  | _ -> failwith "Unreachable Case.."

let create_new_grids_r2 (p: player) (r1: cell list) (r2: cell list) (r3: cell list) : grid list =
  match replace_empty_cell p r2 with
  | [a] -> [[r1; a; r3]]
  | [a;b] -> [[r1; a; r3]; [r1; b; r3]]
  | [a;b;c] -> [[r1; a; r3];[r1;b;r3]; [r1;c;r3]]
  | _ -> failwith "Unreachable Case.."
  
let create_new_grids_r3 (p: player) (r1: cell list) (r2: cell list) (r3: cell list) : grid list =
  match replace_empty_cell p r3 with
  | [a] -> [[r1; r2; a]]
  | [a;b] -> [[r1; r2; a]; [r1; r2; b]]
  | [a;b;c] -> [[r1; r2; a];[r1; r2; b]; [r1; r2; c]]
  | _ -> failwith "Unreachable Case.."


let list_all_moves (p: player) (g: grid) : grid list =
  match g with
  | [row1; row2; row3] ->
      let gl1 = create_new_grids_r1 p row1 row2 row3 in
      let gl2 = create_new_grids_r2 p row1 row2 row3 in
      let gl3 = create_new_grids_r3 p row1 row2 row3 in
      gl1 @ gl2 @ gl3 
  | _ -> failwith "Invalid grid"

(* 
requires: a grid list
ensures: returns the first encounter of a winning grid if it exists otherwise returns None.
 *)

let rec first_winning_grid (p: player) (gl: grid list) : grid option = 
  match gl with
  | [] -> None
  | g::rest -> 
    if (is_winning_grid p g) then Some g else first_winning_grid p rest

end;;


(* take a grid, play all possible moves, if any of it is a winning move, return else return none. *)

let play_winning_move (p: player) (g: grid) : grid option =
  let moves = TicTacToe.list_all_moves p g in
  let rec aux (p: player) (g: grid) (gl: grid list) : grid option =
    match gl with
    | [] -> None
    | h::t -> 
      if TicTacToe.is_winning_grid p h = true then Some h 
      else aux p g t
    in 
    aux p g moves



(* The goal now is whatever grid I give to the program, it plays the 'best possible move' and returns it *)
(* 

defining 'best possible move', 
  1. if a winning move is possible, it is the best possible move, otherwise
  2. if placing a O in an empty cell in a row (call it move z) leads to a winning move for X, then z is not the best possible move. 
  3. if placing a O in an empty cell does not lead to an immediate win for X, then for every possible move for X (say every possible move is stored as a new grid G'), check if a winning grid is possible for O, if not then repeat from step 1 for G'. 
*)

(* function to check a winning move for X implemented by changing the type and making the previous functions take another argument.*)


(* let rec best_moves (p: player) (g: grid) : grid list =
  match play_winning_move p g with
  | Some x -> [x] 
  | None -> 

    let rec try_next_moves (p: player) (gl: grid list) = 
      match gl with
      | [] -> []
      | x::xs -> 
        if TicTacToe.is_winning_grid (TicTacToe.opponent p) x then try_next_moves p xs
        else if TicTacToe.is_winning_grid (p) x then [x]
        else best_moves p (x)           
    in try_next_moves (p) (gl1 @ gl2 @ gl3)
    | _ -> failwith "Invalid row" *)


