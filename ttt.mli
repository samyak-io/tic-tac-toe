type player = O | X
type cell = Empty | P of player
type grid = cell list list
type move_outcome = Win of grid | Lose | Draw of grid
module ListUtils :
  sig
    val foldl : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b
    val filter_rev : ('a -> bool) -> 'a list -> 'a list
    val get_index : 'a -> 'a list -> int option
    val get_element : int -> 'a list -> 'a option
    val forall : ('a -> bool) -> 'a list -> bool
    val length : 'a list -> int
    val range : int -> int list
    val if_exists : ('a -> bool) -> 'a list -> bool
    val append_unique : 'a -> 'a list -> 'a list
  end
module TicTacToe :
  sig
    val opponent : player -> player
    val check_line : player -> cell list -> bool
    val is_winning_row : player -> grid -> bool
    val is_winning_diagonal : player -> grid -> bool
    val is_winning_column : player -> grid -> bool
    val is_winning_grid : player -> grid -> bool
    val is_full : grid -> bool
    val replace_empty_cell : player -> cell list -> cell list list
    val create_new_grids_r1 :
      player -> cell list -> cell list -> cell list -> grid list
    val create_new_grids_r2 :
      player -> cell list -> cell list -> cell list -> grid list
    val create_new_grids_r3 :
      player -> cell list -> cell list -> cell list -> grid list
    val list_all_moves : player -> grid -> grid list
    val winning_grid : player -> grid list -> grid option
    val new_grids_from_grids : player -> grid list -> grid list
    val remove_grid : grid -> grid list -> grid list
  end
val play_winning_move : player -> grid -> grid option
val best_moves : player -> grid -> move_outcome
val play_best_move : player -> grid -> grid
val draw_scenario : grid
val empty_board : grid
