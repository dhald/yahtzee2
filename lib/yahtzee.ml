open! Core
open! Async

module Dice : sig
  type t = int

  val empty : t
  val get : t -> die_value:int -> int
  val combine : t -> t -> t
  val n_dice : t -> int
  val sum : t -> int
  val has_n_of_a_kind : t -> int -> bool
  val max_straight : t -> int
  val has_full_house : t -> bool
  val probability_to_roll : t -> float
  val all_keeps : t array
  val all_rolls : t array
  val possible_rolls : num_dice:int -> t array
  val possible_keeps : t -> t list
  val dice_per_roll : int
  val pp : t -> Sexp.t

  val iter_rolls_and_keeps :
    f:
      (roll_idx:int ->
      roll:t ->
      keep_idx:int ->
      keep:t ->
      probability:float ->
      unit) ->
    unit

  module Expert : sig
    val roll_evs_buffer : float array
    val keep_evs_buffer : float array
    val clear_keep_evs_buffer : unit -> unit
    val clear_roll_evs_buffer : unit -> unit
  end
end = struct
  type t = int

  let bits_per_die_value = 3
  let die_values = 6
  let dice_per_roll = 5
  let empty = 0
  let combine t1 t2 = t1 + t2
  let[@inline always] start_bit n = bits_per_die_value * (n - 1)
  let mask = 0b111
  let[@inline always] get t n = 0b111 land (t lsr start_bit n)

  let pp t =
    let ones = get t 1 in
    let twos = get t 2 in
    let threes = get t 3 in
    let fours = get t 4 in
    let fives = get t 5 in
    let sixes = get t 6 in
    [%message
      (ones : int)
        (twos : int)
        (threes : int)
        (fours : int)
        (fives : int)
        (sixes : int)]

  let[@inline always] set t n x =
    t land lnot (mask lsl start_bit n) lor (x lsl start_bit n)

  let[@inline always] fold ~init ~f =
    init |> f 1 |> f 2 |> f 3 |> f 4 |> f 5 |> f 6

  let[@inline always] fold_direct t ~init ~f =
    init
    |> f (get t 1)
    |> f (get t 2)
    |> f (get t 3)
    |> f (get t 4)
    |> f (get t 5)
    |> f (get t 6)

  let[@inline always] foldi_direct t ~init ~f =
    init
    |> f (get t 1) 1
    |> f (get t 2) 2
    |> f (get t 3) 3
    |> f (get t 4) 4
    |> f (get t 5) 5
    |> f (get t 6) 6

  let n_dice t = fold_direct t ~init:0 ~f:Int.( + )
  let sum t = foldi_direct t ~init:0 ~f:(fun n i acc -> acc + (n * i))

  let has_n_of_a_kind t n =
    fold_direct t ~init:false ~f:(fun n' acc ->
        Bool.Non_short_circuiting.( || ) acc (n' >= n))

  let max_straight t =
    let _curr_len, max_len =
      fold_direct t ~init:(0, 0) ~f:(fun n (curr_len, max_len) ->
          if n > 0 then
            let curr_len = curr_len + 1 in
            let max_len = max max_len curr_len in
            (curr_len, max_len)
          else (0, max_len))
    in
    max_len

  let has_full_house t =
    let has3, has2 =
      fold_direct t ~init:(false, false) ~f:(fun n (has3, has2) ->
          if n = 3 then (true, has2)
          else if n = 2 then (has3, true)
          else (has3, has2))
    in
    has3 && has2

  (* Should never ask for factorial of number > 5. Want to be fast. *)
  let factorial = function
    | 0 -> 1
    | 1 -> 1
    | 2 -> 2
    | 3 -> 6
    | 4 -> 24
    | 5 -> 120
    | _ -> failwith "unexpected number for factorial"

  (* todo: speed this up. probably just precompute. *)
  let probability_to_roll t =
    let n_dice = n_dice t in
    let multinomial_denominator =
      fold_direct t ~init:1 ~f:(fun n acc -> acc * factorial n)
    in
    Float.of_int (factorial n_dice)
    /. Float.of_int (Int.pow 6 n_dice * multinomial_denominator)

  let all_keeps =
    fold ~init:[ empty ] ~f:(fun n keeps ->
        List.concat_map keeps ~f:(fun keep ->
            let dice_used = n_dice keep in
            let dice_remaining = dice_per_roll - dice_used in
            List.range ~start:`inclusive ~stop:`inclusive 0 dice_remaining
            |> List.map ~f:(set keep n)))
    |> Array.of_list

  let possible_keeps t =
    foldi_direct t ~init:[ empty ] ~f:(fun n i keeps ->
        List.concat_map keeps ~f:(fun keep ->
            List.range ~start:`inclusive ~stop:`inclusive 0 n
            |> List.map ~f:(set keep i)))

  let possible_rolls' num_dice =
    Array.filter all_keeps ~f:(fun keep -> n_dice keep = num_dice)

  let possible_rolls_0 = possible_rolls' 0
  let possible_rolls_1 = possible_rolls' 1
  let possible_rolls_2 = possible_rolls' 2
  let possible_rolls_3 = possible_rolls' 3
  let possible_rolls_4 = possible_rolls' 4
  let possible_rolls_5 = possible_rolls' 5
  let all_rolls = possible_rolls_5

  let possible_rolls ~num_dice =
    match num_dice with
    | 0 -> possible_rolls_0
    | 1 -> possible_rolls_1
    | 2 -> possible_rolls_2
    | 3 -> possible_rolls_3
    | 4 -> possible_rolls_4
    | 5 -> possible_rolls_5
    | _ -> failwith "invalid num_dice"

  let keep_idxs, keeps, roll_idxs, rolls, probabilities =
    Array.concat_mapi all_keeps ~f:(fun keep_idx keep ->
        Array.filter_mapi all_rolls ~f:(fun roll_idx roll ->
            let is_subset =
              fold ~init:true ~f:(fun n acc -> acc && get keep n <= get roll n)
            in
            if is_subset then
              let diff =
                fold ~init:empty ~f:(fun n acc ->
                    set acc n (get roll n - get keep n))
              in
              let probability = probability_to_roll diff in
              Some (keep_idx, keep, roll_idx, roll, probability)
            else None))
    |> Array.fold ~init:([], [], [], [], [])
         ~f:(fun
             (keep_idxs, keeps, roll_idxs, rolls, probabilities)
             (keep_idx, keep, roll_idx, roll, probability)
           ->
           ( keep_idx :: keep_idxs,
             keep :: keeps,
             roll_idx :: roll_idxs,
             roll :: rolls,
             probability :: probabilities ))

  let keep_idxs = Array.of_list keep_idxs
  let keeps = Array.of_list keeps
  let roll_idxs = Array.of_list roll_idxs
  let rolls = Array.of_list rolls
  let probabilities = Array.of_list probabilities
  let n_tuples = Array.length keeps

  let iter_rolls_and_keeps ~f =
    for i = 0 to n_tuples - 1 do
      let keep_idx = keep_idxs.(i) in
      let keep = keeps.(i) in
      let roll_idx = roll_idxs.(i) in
      let roll = rolls.(i) in
      let probability = probabilities.(i) in
      f ~roll_idx ~roll ~keep_idx ~keep ~probability
    done

  let rec fold_rolls_and_keeps' i acc ~f =
    if i = n_tuples then acc
    else
      let keep_idx = keep_idxs.(i) in
      let keep = keeps.(i) in
      let roll_idx = roll_idxs.(i) in
      let roll = rolls.(i) in
      let probability = probabilities.(i) in
      let acc = f acc ~roll_idx ~roll ~keep_idx ~keep ~probability in
      fold_rolls_and_keeps' (i + 1) acc ~f

  let fold_rolls_and_keeps ~f ~init = fold_rolls_and_keeps' 0 init ~f

  (* Shadowing like this is probably bad form *)
  let get t ~die_value = get t die_value

  module Expert = struct
    let max_value_as_int = set empty 6 5
    let roll_evs_buffer = Array.create ~len:(Array.length all_rolls) 0.
    let keep_evs_buffer = Array.create ~len:(Array.length all_keeps) 0.

    let clear_keep_evs_buffer () =
      Array.fill keep_evs_buffer ~pos:0 ~len:(Array.length keep_evs_buffer) 0.

    let clear_roll_evs_buffer () =
      Array.fill roll_evs_buffer ~pos:0 ~len:(Array.length roll_evs_buffer) 0.
  end
end

module Category = struct
  type t =
    | Ones
    | Twos
    | Threes
    | Fours
    | Fives
    | Sixes
    | Chance
    | Three_of_a_kind
    | Four_of_a_kind
    | Full_house
    | Small_straight
    | Large_straight
    | Yahtzee
  [@@deriving compare, sexp, enumerate, hash, variants]

  let n_of_a_kind_score n roll =
    if Dice.has_n_of_a_kind roll n then Dice.sum roll else 0

  let straight_score min_len score roll =
    if Dice.max_straight roll >= min_len then score else 0

  let full_house_score roll = if Dice.has_full_house roll then 25 else 0

  let score t (roll : Dice.t) =
    match t with
    | Ones -> 1 * Dice.get roll ~die_value:1
    | Twos -> 2 * Dice.get roll ~die_value:2
    | Threes -> 3 * Dice.get roll ~die_value:3
    | Fours -> 4 * Dice.get roll ~die_value:4
    | Fives -> 5 * Dice.get roll ~die_value:5
    | Sixes -> 6 * Dice.get roll ~die_value:6
    | Chance -> Dice.sum roll
    | Three_of_a_kind -> n_of_a_kind_score 3 roll
    | Four_of_a_kind -> n_of_a_kind_score 4 roll
    | Full_house -> full_house_score roll
    | Small_straight -> straight_score 4 30 roll
    | Large_straight -> straight_score 4 40 roll
    | Yahtzee -> if Dice.has_n_of_a_kind roll 5 then 50 else 0

  let is_upper_category = function
    | Ones | Twos | Threes | Fours | Fives | Sixes -> true
    | Chance | Three_of_a_kind | Four_of_a_kind | Full_house | Small_straight
    | Large_straight | Yahtzee ->
        false

  let n_categories = List.length all

  module Set = struct
    type outer = t [@@deriving sexp_of]
    type t = int [@@deriving sexp, hash, compare]

    let empty = 0
    let mem t category = not (t land (1 lsl Variants.to_rank category) = 0)
    let add t category = t lor (1 lsl Variants.to_rank category)

    let length t =
      let rec aux t n = if t = 0 then n else aux (t lsr 1) (n + (t land 1)) in
      aux t 0

    let pp t =
      let categories = List.filter all ~f:(mem t) in
      [%sexp (categories : outer list)]
  end
end

module Turn = struct
  type t = int [@@deriving sexp_of]

  let used_categories_offset = 0
  let used_categories_bits = 13
  let upper_category_score_offset = 13
  let upper_category_score_bits = 6

  let create ~upper_category_score ~used_categories =
    (upper_category_score lsl upper_category_score_offset) lor used_categories

  let used_categories t = t land 0b1111111111111
  let upper_category_score t = (t lsr upper_category_score_offset) land 0b111111
  let max_as_int = Int.pow 2 19 - 1

  let pp t =
    let used_categories = used_categories t |> Category.Set.pp in
    let upper_category_score = upper_category_score t in

    [%message "" (used_categories : Sexp.t) (upper_category_score : int)]
end

let compute_post_third_roll_evs ~turn ~begin_turn_state_evs =
  let used_categories = Turn.used_categories turn in
  let upper_category_score = Turn.upper_category_score turn in
  let unused_categories =
    List.filter Category.all ~f:(fun category ->
        not (Category.Set.mem used_categories category))
    |> Array.of_list
  in
  Array.iteri Dice.all_rolls ~f:(fun roll_idx roll ->
      let ev =
        Array.fold unused_categories ~init:0. ~f:(fun max_ev category ->
            let score = Category.score category roll in
            let next_turn =
              let upper_category_score =
                if Category.is_upper_category category then
                  Int.min (upper_category_score + score) 63
                else upper_category_score
              in
              let used_categories = Category.Set.add used_categories category in
              Turn.create ~upper_category_score ~used_categories
            in
            let ev = begin_turn_state_evs.(next_turn) +. Float.of_int score in
            Float.max ev max_ev)
      in
      Dice.Expert.roll_evs_buffer.(roll_idx) <- ev)

let compute_post_roll_evs () =
  Dice.Expert.clear_roll_evs_buffer ();
  Dice.iter_rolls_and_keeps
    ~f:(fun ~roll_idx ~roll ~keep_idx ~keep ~probability:_ ->
      let prev_ev = Dice.Expert.roll_evs_buffer.(roll_idx) in
      let new_ev = Dice.Expert.keep_evs_buffer.(keep_idx) in
      Dice.Expert.roll_evs_buffer.(roll_idx) <- Float.max prev_ev new_ev)

let compute_post_keep_evs () =
  Dice.Expert.clear_keep_evs_buffer ();
  Dice.iter_rolls_and_keeps
    ~f:(fun ~roll_idx ~roll ~keep_idx ~keep ~probability ->
      let added_ev = probability *. Dice.Expert.roll_evs_buffer.(roll_idx) in
      let prev_ev = Dice.Expert.keep_evs_buffer.(keep_idx) in
      Dice.Expert.keep_evs_buffer.(keep_idx) <- prev_ev +. added_ev)

let compute_begin_turn_ev () =
  Array.foldi Dice.all_rolls ~init:0. ~f:(fun roll_idx acc roll ->
      let p = Dice.probability_to_roll roll in
      let ev = Dice.Expert.roll_evs_buffer.(roll_idx) in
      acc +. (p *. ev))

let compute_begin_turn_ev turn begin_turn_state_evs =
  let used_categories = Turn.used_categories turn in
  let upper_category_score = Turn.upper_category_score turn in
  let unused_categories =
    List.filter Category.all ~f:(fun category ->
        not (Category.Set.mem used_categories category))
  in
  if List.is_empty unused_categories then
    if upper_category_score >= 63 then 35. else 0.
  else (
    compute_post_third_roll_evs ~turn ~begin_turn_state_evs;
    compute_post_keep_evs ();
    compute_post_roll_evs ();
    compute_post_keep_evs ();
    compute_post_roll_evs ();
    compute_begin_turn_ev ())

let compute_begin_turn_evs () =
  let category_subsets =
    List.fold Category.all ~init:[ Category.Set.empty ]
      ~f:(fun subsets category ->
        subsets @ List.map subsets ~f:(fun set -> Category.Set.add set category))
  in
  let upper_category_scores =
    List.range ~start:`inclusive ~stop:`inclusive 0 63
  in
  let all_begin_turn_states =
    List.cartesian_product category_subsets upper_category_scores
    |> List.map ~f:(fun (used_categories, upper_category_score) ->
           Turn.create ~used_categories ~upper_category_score)
  in
  let sorted_begin_turn_states =
    List.sort all_begin_turn_states
      ~compare:
        (Comparable.lift Int.compare ~f:(fun state ->
             state |> Turn.used_categories |> Category.Set.length))
    |> List.rev |> Array.of_list
  in
  let begin_turn_state_evs = Array.create ~len:(Turn.max_as_int + 1) 0. in
  let time_source = Synchronous_time_source.wall_clock () in
  let start_time = Synchronous_time_source.now time_source in
  Array.iteri sorted_begin_turn_states ~f:(fun i begin_turn_state ->
      let ev = compute_begin_turn_ev begin_turn_state begin_turn_state_evs in
      begin_turn_state_evs.(begin_turn_state) <- ev);

  let end_time = Synchronous_time_source.now time_source in
  let time_elapsed = Time_ns.diff end_time start_time in
  print_s
    [%message
      "Did some shit"
        (upper_category_scores : int list)
        (time_elapsed : Time_ns.Span.t)
        (List.length all_begin_turn_states : int)
        (Array.length Dice.all_rolls : int)
        (Array.length Dice.all_keeps : int)];
  ()

let generate_ev_table =
  Command.async_or_error ~summary:""
    [%map_open.Command
      let file = flag "file" (required string) ~doc:"" in
      fun () ->
        print_endline file;
        compute_begin_turn_evs ();
        Deferred.Or_error.return ()]

let play_game =
  Command.async_or_error ~summary:""
    [%map_open.Command
      let () = return () in
      fun () -> Deferred.Or_error.return ()]

let command =
  Command.group ~summary:""
    [ ("generate", generate_ev_table); ("play", play_game) ]
