(* Empty replacement for the stdlib's Std_exit, which would pull in all of
   Stdlib.  tiny_globals.ml is linked against this one so that its DATA
   section stays small enough to be allocated in the minor heap. *)
