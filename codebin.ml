type cell = Empty | O | X

type grid = cell list list

(* Assumptions about grid and rows. A grid always contains three rows. Each row always contains three cells. *)

(* 
requires: a grid that is a list of lists of type cell; and the player, either O or X.
ensures: 
        the next best move for the player in the form of a grid with the move played is returned as.
*)

let rec foldl (f: 'b -> 'a -> 'b) (v: 'b) (l: 'a list) : 'b =
  match l with
  | [] -> v
  | h::t -> foldl (f) (f v h) (t)

(* let's first try defining linear search *)

(* function to get the index of an element in the list if the element exists in the list *) 
(* let rec index (element: 'a) (lst: 'a list) : int =
  match lst with
  | [] -> failwith "Empty List"
  | h::t when h = element -> 0
  | h::t -> 1 + index element t *)


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




(* 
let winning_grids_for_O : grid list = [
  (* 3 rows *)
  [[O; O; O]; [Empty; Empty; Empty]; [Empty; Empty; Empty]];
  [[Empty; Empty; Empty]; [O; O; O]; [Empty; Empty; Empty]];
  [[Empty; Empty; Empty]; [Empty; Empty; Empty]; [O; O; O]];

  (* 3 columns *)
  [[O; Empty; Empty]; [O; Empty; Empty]; [O; Empty; Empty]];
  [[Empty; O; Empty]; [Empty; O; Empty]; [Empty; O; Empty]];
  [[Empty; Empty; O]; [Empty; Empty; O]; [Empty; Empty; O]];

  (* 2 diagonals *)
  [[O; Empty; Empty]; [Empty; O; Empty]; [Empty; Empty; O]];
  [[Empty; Empty; O]; [Empty; O; Empty]; [O; Empty; Empty]];
] *)

(* requires: a grid (list of list of cells => list of three rows of three cells where each row is a list and contains three cells where cells are basically either O or X or Empty.*)
(* ensures: if at least one winning grid is possible to create by placing an O in any of the empty cells, return a new grid with that move played. else return an error for now.*)

(* 
operational steps: 
step 1: replace Empty with Os in one of the cell that is empty in row1.
step 2: check if the new grid is a winning grid.
step 3: if yes then return that new grid
step 3: if no then repeat step 1 for another row.
*)

(* inconsistent return types with this function.

let rec traverse_grid (g: grid) : grid =
  match g with
  | [] -> g
  | row1::other_rows -> 
    let rec traverse_row (row: cell list) = 
      match row with
      | [] -> row :: traverse_grid other_rows
      | cell1 :: other_cells -> 
        match cell1 with
        | Empty -> (O: cell) :: traverse_row other_cells 
        | anything_else -> anything_else :: traverse_row other_cells
      in traverse_row row1 *)



(* replaces all empty cells in a row with O *)
(* let rec replace_empty_in_row (row: cell list) : cell list =
  match row with
  | [] -> row
  | cell::rest -> 
    match cell with
    | Empty -> O :: replace_empty_in_row rest
    | other -> other :: replace_empty_in_row rest *)


(* replaces one empty cell at a time with O *)
(* let rec replace_empty_in_row (row: cell list) : cell list =
  let winning = false in
  match (row, winning) with
  |  *)


(* let rec forall (pred: 'a -> bool) (l: 'a list): bool =
  match l with
  | [] -> true
  | h::t -> 
    match pred(h) with
    | true -> true && forall pred t
    | false -> false *)

(* requires: forall needs a predicate and a list of any type
   ensures: checks if the predicate holds true for all arguments in the list, if it does then forall returns true else it returns false
            returns true if the list is empty.
*)

let rec forall (pred: 'a -> bool) (l: 'a list) : bool = 
  foldl (fun x y -> x && pred (y)) (true) (l)


  (* checking if forall works fine *)
(* let () = 
  let is_even x = if x mod 2 = 0 then true else false in 
  let check_forall = forall is_even ([2;6;8;10]) in
  let check_forall_fold = forall_fold is_even ([2;6;8;10]) in
  let check_forall_2 = forall is_even ([3;7;8;10]) in
  let check_forall_fold_2 = forall_fold is_even ([3;7;8;10]) in
  Printf.printf "%b\n" (check_forall);
  Printf.printf "%b\n" (check_forall_fold);
  Printf.printf "%b\n" (check_forall_2);
  Printf.printf "%b\n" (check_forall_fold_2); *)

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



(* i have to now write a if exists function that
requires: takes in a list and a condition (a predicate)
ensures: return true if any of the elements satisfy the predicate, return false if none of the elements satisfy that condition.
         return false when list is empty.
  *)
let if_exists (pred: 'a -> bool) (lst: 'a list) : bool =
  foldl (fun x y -> x || pred(y)) (false) (lst)


let check_line (row: cell list) = 
  forall (fun x -> if x = (O: cell) then true else false) (row)




let is_winning_row (g: grid) = 
  if_exists (check_line) (g)

let is_winning_diagonal (g: grid) : bool = 
  match g with
  | [] -> false
  | [row1;row2;row3] -> 
    if (get_element (0) (row1) = Some O && get_element (1) (row2) = Some O && get_element (2) (row3) = Some O) 
      || (get_element (2) (row1) = Some O && get_element (1) (row2) = Some O && get_element (0) (row3) = Some O)
    then true else false
  | _ -> failwith "Invalid Grid"
  


(* function to check if any column in g is all O *)
let is_any_column_all_o (g: grid) : bool = 
  match g with
  | [] -> false
  | row1::_ -> 
      let check_ith_elements i =
        forall (fun row -> get_element i row = Some O) g (*check_ith_element checks if the index i in all rows in g is the same.*)
      in
      if_exists check_ith_elements (range (length row1)) (*if exists takes a predicate and a list and checks if the predicate holds for at least one element in a list
        here the predicate is check_ith_element first takes in 0 then 1 then 2 until length(row 1). if there is at least one index where all the rows have O in that index, it returns true.*)

let is_winning_grid (g: grid) : bool =
  if (is_any_column_all_o g) || (is_winning_diagonal g) || (is_winning_row g) = true then true else false


(* we don't need this *)
(* let is_winning_column (g: grid) : bool =
  match g with
  | [] -> false
  | _ -> is_any_column_all_o (g) *)



(* let check_empty_cell (row: cell list) : cell list = 
  match row with
  | [] -> failwith "row is hollow."
  | [cell1; cell2; cell3] -> 
    if cell1 = Empty then [O; cell2; cell3]
    else if cell2 = Empty then [cell1; O; cell3]
    else if cell3 = Empty then [cell1; cell2; O]
    else [cell1; cell2; cell3]
  | _ -> failwith "invalid row." *)
(* but what if there are multiple Empty cells in a row? *)

(* let replace_empty_cell (cell: cell) (m: cell) : cell =
  match cell with
  | Empty -> m
  | _ -> cell *)

(* this function will return all moves for O that are possible to play when one or more cells are empty as cell list list. *)

(* 
requires: a row
ensures: that it returns all possible unique placements for O in the given row as different elements of a list.
*)

let replace_empty_cell (row: cell list) : cell list list = 
  match row with
  | [cell1; cell2; cell3] when cell1 <> Empty && cell2 <> Empty && cell3 <> Empty -> [[cell1; cell2; cell3]]
  | [Empty; cell2; cell3] when cell2 <> Empty && cell3 <> Empty -> [[O; cell2; cell3]]
  | [cell1; Empty; cell3] when cell1 <> Empty && cell3 <> Empty -> [[cell1; O; cell3]]
  | [cell1; cell2; Empty] when cell1 <> Empty && cell2 <> Empty -> [[cell1; cell2; O]]
  | [Empty; Empty; cell3] when cell3 <> Empty -> [[O; Empty; cell3]; [Empty; O; cell3]]
  | [cell1; Empty; Empty] when cell1 <> Empty -> [[cell1; O; Empty]; [cell1; Empty; O]]
  | [Empty; cell2; Empty] when cell2 <> Empty -> [[O; cell2; Empty]; [Empty; cell2; O]]
  | [Empty; Empty; Empty] -> [[Empty; Empty; O]; [Empty; O; Empty]; [O; Empty; Empty]]
  | _ -> failwith "invalid row." 

(* 
requires: input is a grid. no rows are hollow.
ensures: returns true if a winning move is possible, else returns false.
          
 *)

(* let is_winning_possible (g: grid) : bool =
  match g with
  | [] -> failwith "Hollow Grid."
  | r1::rest -> 
    let rec is_winning_row_possible (r: cell list) : bool =
      if (check_empty_cell r) = [r] then
        match rest with
        | [] -> false
        | r2::rest2 -> is_winning_row_possible r2
      else
        true *)


(* 
  requires: grid and an index for the row.
  ensures: replaces the row at the given index with the first row in the check_empty_cell function's output. if it's a winning move, it plays it. if it's not, then it checks if the second row in the check_empty_cell function's output is a if there is one is a winning move, and so on. if none of the new rows in the grid lead to a winning move, it outputs false.

*)



(* 
requires: three rows of a grid.
ensures: checks if row1 has an empty cell and if it does then it returns the possible places to play O on, if there is one place to play O, a new row is returned for r1 rest remain same. if there are more than one move possible, then the grid list contains more than one grid. 
essentially, it is the set of all playable positions and thus grids.
*)
let create_new_grids_r1 (r1: cell list) (r2: cell list) (r3: cell list) : grid list =
  match replace_empty_cell r1 with
  | [a] -> [[a; r2; r3]]
  | [a;b] -> [[a; r2; r3]; [b; r2; r3]]
  | [a;b;c] -> [[a; r2; r3];[b;r2;r3]; [c;r2;r3]]
  | _ -> failwith "Unreachable Case.."

let create_new_grids_r2 (r1: cell list) (r2: cell list) (r3: cell list) : grid list =
  match replace_empty_cell r2 with
  | [a] -> [[r1; a; r3]]
  | [a;b] -> [[r1; a; r3]; [r1; b; r3]]
  | [a;b;c] -> [[r1; a; r3];[r1;b;r3]; [r1;c;r3]]
  | _ -> failwith "Unreachable Case.."
  
let create_new_grids_r3 (r1: cell list) (r2: cell list) (r3: cell list) : grid list =
  match replace_empty_cell r3 with
  | [a] -> [[r1; r2; a]]
  | [a;b] -> [[r1; r2; a]; [r1; r2; b]]
  | [a;b;c] -> [[r1; r2; a];[r1; r2; b]; [r1; r2; c]]
  | _ -> failwith "Unreachable Case.."

(* 
requires: a grid list
ensures: returns the first encounter of a winning grid if it exists otherwise returns None.
 *)
let rec first_winning_grid (gl: grid list) : grid option = 
  match gl with
  | [] -> None
  | g::rest -> 
    if (is_winning_grid g) then Some g else first_winning_grid rest


(* create_new_grids_r1, r2, r3 already take 3 rows and return list of grids with possible moves on those rows *)

let play_winning_move (g: grid) : grid option =
  match g with
  | [row1; row2; row3] ->
      let g1 = create_new_grids_r1 row1 row2 row3 in (* Make unique possible changes in row1, store it as a set of new grids *)
      let g2 = create_new_grids_r2 row1 row2 row3 in (* Make unique possible changes in row2, store it as a set of new grids *)
      let g3 = create_new_grids_r3 row1 row2 row3 in (* Make unique possible changes in row3, store it as a set of new grids *)

      (* Try the winning grids generated by new moves on row1 *)
      (match first_winning_grid g1 with
      | Some w -> Some w
      | None ->
          (* If none found for row1, try row2 *)
          (match first_winning_grid g2 with
          | Some w -> Some w
          | None ->
              (* If none found for row3 *)
              first_winning_grid g3))
  | _ -> failwith "Invalid input: grid must be 3 rows"


(* The goal now is whatever grid I give to the program, it plays the 'best possible move' and returns it *)
(* 

defining 'best possible move', 
  1. if a winning move is possible, it is the best possible move, otherwise
  2. if placing a O in an empty cell in a row (call it move z) leads to a winning move for X, then z is not the best possible move. 
  3. else if placing a O in an empty cell does not lead to an immediate win for X, then for every possible move for X (say every possible move is stored as a new grid G'), check if a winning grid is possible for O, if not then repeat from step 1 for G'. 
*)

(* function to check a winning move for z *)