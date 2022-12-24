
open Printf
open String
open Str
open Array

let infile = "results-2021-04-29-new"
let infile1 = "all-benchmarks-cvc4_cvc5_0.0.4"

let array1 = Array.create 80000 "" ;;
let array2 = Array.create 80000 "" ;;

let rec readin ic i =
  let lname = input_line ic in
   (if lname <> "end" then ((set array1 i lname);
	let c= input_line ic in
	let c= input_line ic in
	print_string (array1.(i));
	readin ic (i+1))
   else
(i))
;;




let rec compare ic regex =
    let lname = input_line ic in
try
if lname <> "end" then (
        let a = Str.search_forward regex lname 0 in
let c = input_line ic in
let c = input_line ic in
let t = float_of_string c in
(Printf.printf "%F\n" t))
else (print_string "end")
with e -> compare ic regex
;;

let rec take ic =
  try
let line = input_line ic in
if line <> "end" then (
    let line = String.sub line 24 20 in
    print_string (line ^ "\n");
    let r = Str.regexp line in
    let ic1 = open_in infile1 in
    compare ic1 r;
    close_in ic1;
    let ig = input_line ic in
    let ig = input_line ic in
    take ic)
else (close_in ic)
with e -> close_in ic; raise e

let sat_small = ref (0.0,0);;
let sat_big = ref (0.0,0);;
let unsat_small = ref (0.0,0);;
let unsat_big = ref (0.0,0);;
let rsatsmall = Str.regexp "/sat/small" ;;
let rsatbig = Str.regexp "/sat/big" ;;
let runsatsmall = Str.regexp "/unsat/small" ;;
let runsatbig = Str.regexp "/unsat/big" ;;

let matched reg str =
try
   let c =  Str.search_forward reg str 0 in
   true
with e -> false ;;

let readtime ic =
let c = input_line ic in
let c = input_line ic in
(float_of_string c) ;;

let addpair p f =
   let (p1,r1) = !p in
p := (p1 +. f, r1 + 1) ;;

let test () = (
	       addpair sat_small 0.3;
		       addpair sat_small 0.3;
		       addpair sat_small 0.7;
let (p1,p2) = !sat_small in
(Printf.printf "%F,%d\n" p1 p2) );;

exception Foo of string
let rec compute ic =   
   let line = input_line ic in
   (if line <> "end" then
       (if (matched rsatsmall line) then (addpair sat_small (readtime ic); compute ic)
	   else if (matched rsatbig line) then (addpair sat_big (readtime ic) ; compute ic)
	   else if (matched runsatsmall line) then (addpair unsat_small (readtime ic) ; compute ic)
	   else if matched runsatbig line then (addpair unsat_big (readtime ic); compute ic)
	   else raise (Foo "not in the scope"))
   else
   ());;

let print_value () =
let (p1,n1) = !sat_small in
(Printf.printf "%F, %F, %d\n" (p1/. (float_of_int n1)) p1 n1);
let (p2,n2) = !sat_big in
(Printf.printf "%F, %F, %d\n" (p2/. (float_of_int n2)) p2 n2);
let (p3,n3) = !unsat_small in
(Printf.printf "%F, %F, %d\n" (p3/. (float_of_int n3)) p3 n3);
let (p4,n4) = !unsat_big in
(Printf.printf "%F, %F, %d\n" (p4/. (float_of_int n4)) p4 n4);
;;


let () =
let ic = open_in infile1 in
compute ic;
print_value() ;;
