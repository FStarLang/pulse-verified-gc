(*
 * The Computer Language Benchmarks Game
 * https://salsa.debian.org/benchmarksgame-team/benchmarksgame/
 *
 * Contributed by Paolo Ribeca
 * (Based on the Java version by Oleg Mazurov)
 *
 * Usage: ./fannkuchredux <n>  (default: 12)
 *)

let workers = 4  (* Reduced for testing *)

module Perm = struct
  type t = { p: int array; pp: int array; c: int array }
  
  let facts =
    let n = 20 in
    let res = Array.make (n + 1) 1 in
    for i = 1 to n do
      res.(i) <- i * res.(i - 1)
    done;
    res

  let setup n idx =
    let res = { p = Array.init n (fun i -> i);
                pp = Array.make n 1;
                c = Array.make n 1 }
    and idx = ref idx in
    for i = n - 1 downto 0 do
      let d = !idx / facts.(i) in
      res.c.(i) <- d;
      idx := !idx mod facts.(i);
      Array.blit res.p 0 res.pp 0 (i + 1);
      for j = 0 to i do
        res.p.(j) <- if j + d <= i then res.pp.(j + d) else res.pp.(j + d - i - 1)
      done
    done;
    res

  let next { p = p; c = c } =
    let f = ref p.(1) in
    p.(1) <- p.(0);
    p.(0) <- !f;
    let i = ref 1 in
    while let aug_c = c.(!i) + 1 in c.(!i) <- aug_c; aug_c > !i do
      c.(!i) <- 0;
      incr i;
      let n = p.(1) in
      p.(0) <- n;
      let red_i = !i - 1 in
      for j = 1 to red_i do
        p.(j) <- p.(j + 1)
      done;
      p.(!i) <- !f;
      f := n
    done

  let count { p = p; pp = pp } =
    let f = ref p.(0) and res = ref 1 in
    if p.(!f) <> 0 then begin
      let len = Array.length p in
      let red_len = len - 1 in
      for i = 0 to red_len do pp.(i) <- p.(i) done;
      while pp.(!f) <> 0 do
        incr res;
        let lo = ref 1 and hi = ref (!f - 1) in
        while !lo < !hi do
          let t = pp.(!lo) in
          pp.(!lo) <- pp.(!hi);
          pp.(!hi) <- t;
          incr lo;
          decr hi
        done;
        let ff = !f in
        let t = pp.(ff) in
        pp.(ff) <- ff;
        f := t
      done
    end;
    !res
end

let run_chunk n idx_min idx_max =
  let perm = Perm.setup n idx_min in
  let cs = ref 0 and fs = ref 0 in
  for idx = idx_min to idx_max - 1 do
    let c = Perm.count perm in
    fs := max !fs c;
    cs := !cs + (if idx land 1 = 0 then c else -c);
    Perm.next perm
  done;
  (!cs, !fs)

let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 12 in
  let chunk_size = Perm.facts.(n) / workers
  and rem = Perm.facts.(n) mod workers in
  
  let domains = Array.init workers (fun i ->
    let idx_min = chunk_size * i + min i rem in
    let idx_max = idx_min + chunk_size + (if i < rem then 1 else 0) in
    Domain.spawn (fun () -> run_chunk n idx_min idx_max)
  ) in
  
  let cs = ref 0 and fs = ref 0 in
  Array.iter (fun d ->
    let (c, f) = Domain.join d in
    cs := !cs + c;
    fs := max !fs f
  ) domains;
  
  Printf.printf "%d\nPfannkuchen(%d) = %d\n" !cs n !fs
