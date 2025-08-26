type player = O | X

type cell = Empty | P of player

type grid = cell list list

type move_outcome = 
  | Win of grid
  | Lose
  | Draw of grid

module ListUtils = struct 
let rec foldl (f: 'b -> 'a -> 'b) (v: 'b) (l: 'a list) : 'b =
  match l with
  | [] -> v
  | h::t -> foldl (f) (f v h) (t)

let filter_rev (pred: 'a -> bool) (l: 'a list) : 'a list = 
  foldl (fun x y -> if pred y then (y :: x) else x) ([]) (l)

let reverse (l: 'a list) : 'a list =
  foldl(fun x y -> y::x) ([]) (l)

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


let is_there (pred: 'a -> bool) (lst: 'a list) : bool =
  foldl (fun x y -> x || pred(y)) (false) (lst)

let rec if_exists (ele: 'a) (l: 'a list) : bool = 
  match l with
  | [] -> false
  | h::t -> if ele = h then true else if_exists ele t

let append_unique (element: 'a) (lst: 'a list) : 'a list =
  match lst with
  | [] -> [element]
  | _ -> if (is_there (fun x -> if x = element then true else false) lst) = true then lst else element::lst

let remove_duplicates (l: 'a list) : 'a list =
  let rec aux l1 l2 = 
    match l with
    | [] -> [] 
    | h::t -> 
      if if_exists h l1 = true then aux t l2 else h::l2
  in
  aux l []

(* requires: two lists, say l1 & l2
   ensures: say l3 is the output, for all e in l1 or l2, e is in l3 but the count of all e in l3 = 1.
 *)
let rec concatenate_unique (l1: 'a list) (l2: 'a list) : 'a list =
    match l1 with
    | [] -> l2
    | h1::t1 -> remove_duplicates (concatenate_unique t1 (h1::l2))

(* flatten. requires: takes in a list, l of type 'a list list
            ensures:  return l' (of type 'a list) such that all the elements inside all the lists in l are now in l'.
*)
let flatten_lst (l: 'a list list) = 
  let rec flatten_helper (l1: 'a list list) (l2: 'a list) = 
    match l1 with
    | [] -> reverse l2
    | innlist::innlist_rest -> 
      let rec flatten_helper_2 (innerlists: 'a list) (l2: 'a list) =
        match innerlists with
        | [] -> flatten_helper (innlist_rest) (l2)
        | x::xs -> flatten_helper_2 (xs) (x::l2)
      in 
      flatten_helper_2 innlist l2
    in
    flatten_helper l []

end;;

module TicTacToe = struct

let opponent (p: player) : player = 
  match p with
  | X -> O
  | O -> X

let check_line (p: player) (row: cell list) : bool = 
  ListUtils.forall (fun x -> if x = P(p) then true else false) (row)

let is_winning_row (p: player) (g: grid) : bool = 
  ListUtils.is_there (check_line p) (g)

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
      ListUtils.is_there (check_ith_elements (p)) (ListUtils.range (ListUtils.length row1)) (*if exists takes a predicate and a list and checks if the predicate holds for at least one element in a list
        here the predicate is check_ith_element first takes in 0 then 1 then 2 until length(row 1). if there is at least one index where all the rows have O in that index, it returns true.*)

let is_winning_grid (p: player) (g: grid) : bool =
  if (is_winning_column p g) || (is_winning_diagonal p g) || (is_winning_row p g) = true then true else false


let is_full (g: grid) : bool =
  ListUtils.forall (ListUtils.forall (fun x -> if x = Empty then false else true)) (g)

(* this function will return all moves for O that are possible to play when one or more cells are empty as cell list list. *)

(* 
requires: a row
ensures: that it returns all possible unique placements for O in the given row as different elements of a list.
*)

let replace_empty_cell (p: player) (row: cell list) : cell list list option = 
  match row with
  | [cell1; cell2; cell3] when cell1 <> Empty && cell2 <> Empty && cell3 <> Empty -> None
  | [Empty; cell2; cell3] when cell2 <> Empty && cell3 <> Empty -> Some [[P p; cell2; cell3]]
  | [cell1; Empty; cell3] when cell1 <> Empty && cell3 <> Empty -> Some [[cell1; P p; cell3]]
  | [cell1; cell2; Empty] when cell1 <> Empty && cell2 <> Empty -> Some [[cell1; cell2; P p]]
  | [Empty; Empty; cell3] when cell3 <> Empty -> Some [[P p; Empty; cell3]; [Empty; P p; cell3]]
  | [cell1; Empty; Empty] when cell1 <> Empty -> Some [[cell1; P p; Empty]; [cell1; Empty; P p]]
  | [Empty; cell2; Empty] when cell2 <> Empty -> Some [[P p; cell2; Empty]; [Empty; cell2; P p]]
  | [Empty; Empty; Empty] -> Some [[Empty; Empty; P p]; [Empty; P p; Empty]; [P p; Empty; Empty]]
  | _ -> failwith "invalid row." 

(* 
requires: three rows of a grid.
ensures: checks if row1 has an empty cell and if it does then it returns the possible places to play O on, if there is one place to play O, a new row is returned for r1 rest remain same. if there are more than one move possible, then the grid list contains more than one grid. 
essentially, it is the set of all playable positions and thus grids.
*)

let create_new_grids_r1 (p: player) (r1: cell list) (r2: cell list) (r3: cell list) : grid list =
  match replace_empty_cell p r1 with
  | Some [a] -> [[a; r2; r3]]
  | Some [a;b] -> [[a; r2; r3]; [b; r2; r3]]
  | Some [a;b;c] -> [[a; r2; r3];[b;r2;r3]; [c;r2;r3]]
  | None -> []
  | _ -> failwith "Invalid grid."

let create_new_grids_r2 (p: player) (r1: cell list) (r2: cell list) (r3: cell list) : grid list =
  match replace_empty_cell p r2 with
  | Some [a] -> [[r1; a; r3]]
  | Some [a;b] -> [[r1; a; r3]; [r1; b; r3]]
  | Some [a;b;c] -> [[r1; a; r3];[r1;b;r3]; [r1;c;r3]]
  | None -> []
  | _ -> failwith "Invalid grid."
  
let create_new_grids_r3 (p: player) (r1: cell list) (r2: cell list) (r3: cell list) : grid list =
  match replace_empty_cell p r3 with
  | Some [a] -> [[r1; r2; a]]
  | Some [a;b] -> [[r1; r2; a]; [r1; r2; b]]
  | Some [a;b;c] -> [[r1; r2; a];[r1; r2; b]; [r1; r2; c]]
  | None -> []
  | _ -> failwith "Invalid grid."



let list_all_moves (p: player) (g: grid) : grid list list =
  match g with
  | [row1; row2; row3] ->
      (* make changes in row1 and create new grids *)
      let rc1_g = create_new_grids_r1 p row1 row2 row3 in
      (* make changes in row2 and create new grids *)
      let rc2_g = create_new_grids_r2 p row1 row2 row3 in
      (* make changes in row3 and create new grids *)
      let rc3_g = create_new_grids_r3 p row1 row2 row3 in
      (* [rc1_g] @ [rc2_g] @ [rc3_g] is essentially [rc1_g; rc2_g; rc3_g] (3 elements), where each element is a list of possible new grids. *)
      [rc1_g] @ [rc2_g] @ [rc3_g]
  | _ -> failwith "Invalid grid"

(* 
requires: a grid list
ensures: returns the first encounter of a winning grid if it exists otherwise returns None.
 *)

let rec winning_grid (p: player) (gl: grid list) : grid option = 
  match gl with
  | [] -> None
  | g::rest -> 
    if (is_winning_grid p g) then Some g else winning_grid p rest
  

let rec remove_grid (g: grid) (gl: grid list) : grid list =
  ListUtils.filter_rev (fun x -> if x = g then true else false) (gl)
end;;


(* take a grid, play all possible moves, if any of it is a winning move, return else return none. *)

let play_winning_move (p: player) (g: grid) : grid option =
  let rec aux (pl: player) (gr: grid list list) =
      match gr with
      | [] -> None
      | x::xs -> 
        match (TicTacToe.winning_grid p x) with
        | None -> aux p xs
        | Some g -> Some g
  in 
  aux p (TicTacToe.list_all_moves p g)


  (* let rec aux (p: player) (g: grid) (gl: grid list) : grid option =
    match gl with
    | [] -> None
    | h::t -> 
      if TicTacToe.is_winning_grid p h = true then Some h 
      else aux p g t
    in 
    aux p g moves *)


(* The goal now is whatever grid I give to the program, it plays the 'best possible move' and returns it *)
(* 

defining 'best possible move', 
  1. if a winning move is possible, it is the best possible move, otherwise
  2. if placing a O in an empty cell in a row (call it move z) leads to a winning move for X, then z is not the best possible move. 
  3. if placing a O in an empty cell does not lead to an immediate win for X, then for every possible move for X (say every possible move is stored as a new grid G'), check if a winning grid is possible for O, if not then repeat from step 1 for G'. 
*)

(* function to check a winning move for (either) X (or O) implemented by changing the type and making the previous functions take another argument.*)

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


(* let best_moves (p: player) (g: grid) : grid option =
  let rec bmoves_aux (p: player) (gl: grid list) : grid option =
  let new_moves = TicTacToe.new_grids_from_grids p gl in
  (* if there's a winning move possible, play it *)
    match TicTacToe.winning_grid p new_moves with
    | Some g -> Some g
    | None ->
        (* if not, then in the new moves is opponent winning? *)
        match TicTacToe.winning_grid (TicTacToe.opponent p) (new_moves) with
        | None -> 
          (* no? go deeper and check next moves for p *)
          let new_moves' = TicTacToe.new_grids_from_grids p new_moves in
            (match new_moves' with
            | [] -> None
            | gls -> bmoves_aux p gls)
        | Some x -> 
          (* yes? well then don't play that move, remove that move from the option we're considering. *)
          let playable_grids = TicTacToe.remove_grid (x) (new_moves) in
          (* since opponent is also not winning, see if any new moves after that lead to the two things (either you winning or the opponent winning)*)
          let new_moves' = TicTacToe.new_grids_from_grids p new_moves in
            (match new_moves' with
            | [] -> Some []
            | gls -> bmoves_aux p playable_grids)
      in 
        bmoves_aux p [g] *)

(* note to check if a new move is even possible, if the old move is the same as the new move then *)
      

(* Assumption, input doesn't allow hollow grid (empty list as grid) *)
let rec minimax (p: player) (g: grid): move_outcome = 
  (* If current player has won *)
  if TicTacToe.is_winning_grid p g then Win g
  (* has opponent won? *)
  else if TicTacToe.is_winning_grid (TicTacToe.opponent p) g then Lose
  (* is board full? yes & since p hasn't wo & opp hasn't won -> must be a draw *)
  else if TicTacToe.is_full g then Draw g
  (* neither, then consider possible moves for p *)
  else
  let moves_list = TicTacToe.list_all_moves p g in (* contains list of list of grids *)
  let all_moves = ListUtils.flatten_lst moves_list in (* contains list of grids. *)
  match TicTacToe.winning_grid p all_moves with
  | Some grid -> Win grid
  | None ->
    let rec try_moves (moves: grid list) : move_outcome = 
      match moves with
      | [] -> Lose (* Nothing to play, opponent wins *)
      | x::xs ->
        match minimax (TicTacToe.opponent p) x with
        | Win w -> try_moves xs
        | Lose -> Win x
        | Draw d -> 
          (* try other moves and see if any of those may lead to a win for p *)
          match try_moves xs with 
          | Win w' -> Win w'
          | Lose -> Draw d
          | Draw d' -> Draw d (*or Draw d', it's draw either ways.*)
    in 
    try_moves all_moves



(* let rec best_moves (p: player) (g: grid) : move_outcome = 
  (* If current player has won *)
  if TicTacToe.is_winning_grid p g then Win g
  (* has opponent won? *)
  else if TicTacToe.is_winning_grid (TicTacToe.opponent p) g then Lose
  (* is board full? yes & since p hasn't wo & opp hasn't won -> must be a draw *)
  else if TicTacToe.is_full g then Draw g
  else
  let moves = TicTacToe.list_all_moves p g in
    let rec try_moves (ms: grid list) : move_outcome = 
    (* Explore Opponent's respones to these moves *)
    match ms with
    |  *)



(* let play_best_move (p: player) (g: grid) : grid = 
  let best_move = best_moves p g in 
  match best_move with
  | Win m -> m 
  | Draw m -> m
  | Lose -> (* Play whatever move is available. *)
    match TicTacToe.list_all_moves p g with
    | [] -> g
    | x::xs -> x
   *)





let draw_scenario : grid = [
  [P O; P X; P O];
  [P O; P X; P X];
  [P X; P O; Empty];
]

let empty_board : grid = [
  [Empty; Empty; Empty];
  [Empty; Empty; Empty];
  [Empty; Empty; Empty];
]
