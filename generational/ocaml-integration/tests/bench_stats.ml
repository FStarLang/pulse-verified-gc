let starts_with prefix s =
  let prefix_len = String.length prefix in
  String.length s >= prefix_len && String.sub s 0 prefix_len = prefix

let parse_kb line =
  let len = String.length line in
  let rec first_digit i =
    if i >= len then None
    else
      match line.[i] with
      | '0' .. '9' -> Some i
      | _ -> first_digit (i + 1)
  in
  let rec last_digit i =
    if i >= len then i
    else
      match line.[i] with
      | '0' .. '9' -> last_digit (i + 1)
      | _ -> i
  in
  match first_digit 0 with
  | None -> None
  | Some first ->
      let last = last_digit first in
      try Some (int_of_string (String.sub line first (last - first))) with
      | Failure _ -> None

let peak_rss_kb () =
  let path = "/proc/self/status" in
  if not (Sys.file_exists path) then None
  else
    let ic = open_in path in
    let rec loop rss =
      match input_line ic with
      | line when starts_with "VmHWM:" line ->
          let hwm = parse_kb line in
          close_in ic;
          hwm
      | line when starts_with "VmRSS:" line ->
          loop (parse_kb line)
      | _ -> loop rss
      | exception End_of_file ->
          close_in ic;
          rss
    in
    loop None

let () =
  at_exit (fun () ->
      let s = Gc.quick_stat () in
      let total_allocated_words =
        s.Gc.minor_words +. s.Gc.major_words -. s.Gc.promoted_words
      in
      let rss_mb =
        match peak_rss_kb () with
        | Some kb -> float_of_int kb /. 1024.0
        | None -> nan
      in
      Printf.eprintf
        "BENCH_STATS,%.0f,%.0f,%.0f,%.0f,%d,%d,%d,%d,%d,%.3f\n%!"
        total_allocated_words s.Gc.minor_words s.Gc.major_words
        s.Gc.promoted_words s.Gc.minor_collections s.Gc.major_collections
        s.Gc.forced_major_collections s.Gc.heap_words s.Gc.top_heap_words rss_mb)

