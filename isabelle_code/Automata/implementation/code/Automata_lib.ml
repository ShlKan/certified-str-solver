module Uint : sig
  type t = int
  val dflt_size : Z.t
  val less : t -> t -> bool
  val less_eq : t -> t -> bool
  val set_bit : t -> Z.t -> bool -> t
  val shiftl : t -> Z.t -> t
  val shiftr : t -> Z.t -> t
  val shiftr_signed : t -> Z.t -> t
  val test_bit : t -> Z.t -> bool
  val int_mask : int
  val int32_mask : int32
  val int64_mask : int64
end = struct

type t = int

let dflt_size = Z.of_int Sys.int_size;;

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if x<0 then
    y<0 && x<y
  else y < 0 || x < y;;

let less_eq x y =
  if x < 0 then
    y < 0 &&  x <= y
  else y < 0 || x <= y;;

let set_bit x n b =
  let mask = 1 lsl (Z.to_int n)
  in if b then x lor mask
     else x land (lnot mask);;

let shiftl x n = x lsl (Z.to_int n);;

let shiftr x n = x lsr (Z.to_int n);;

let shiftr_signed x n = x asr (Z.to_int n);;

let test_bit x n = x land (1 lsl (Z.to_int n)) <> 0;;

let int_mask =
  if Sys.int_size < 32 then lnot 0 else 0xFFFFFFFF;;

let int32_mask = 
  if Sys.int_size < 32 then Int32.pred (Int32.shift_left Int32.one Sys.int_size)
  else Int32.of_string "0xFFFFFFFF";;

let int64_mask = 
  if Sys.int_size < 64 then Int64.pred (Int64.shift_left Int64.one Sys.int_size)
  else Int64.of_string "0xFFFFFFFFFFFFFFFF";;

end;; (*struct Uint*)

module Uint32 : sig
  val less : int32 -> int32 -> bool
  val less_eq : int32 -> int32 -> bool
  val set_bit : int32 -> Z.t -> bool -> int32
  val shiftl : int32 -> Z.t -> int32
  val shiftr : int32 -> Z.t -> int32
  val shiftr_signed : int32 -> Z.t -> int32
  val test_bit : int32 -> Z.t -> bool
end = struct

(* negative numbers have their highest bit set, 
   so they are greater than positive ones *)
let less x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y < 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y < 0;;

let less_eq x y =
  if Int32.compare x Int32.zero < 0 then
    Int32.compare y Int32.zero < 0 && Int32.compare x y <= 0
  else Int32.compare y Int32.zero < 0 || Int32.compare x y <= 0;;

let set_bit x n b =
  let mask = Int32.shift_left Int32.one (Z.to_int n)
  in if b then Int32.logor x mask
     else Int32.logand x (Int32.lognot mask);;

let shiftl x n = Int32.shift_left x (Z.to_int n);;

let shiftr x n = Int32.shift_right_logical x (Z.to_int n);;

let shiftr_signed x n = Int32.shift_right x (Z.to_int n);;

let test_bit x n =
  Int32.compare 
    (Int32.logand x (Int32.shift_left Int32.one (Z.to_int n)))
    Int32.zero
  <> 0;;

end;; (*struct Uint32*)

module Bits_Integer : sig
  val shiftl : Z.t -> Z.t -> Z.t
  val shiftr : Z.t -> Z.t -> Z.t
  val test_bit : Z.t -> Z.t -> bool
end = struct

(* We do not need an explicit range checks here,
   because Big_int.int_of_big_int raises Failure 
   if the argument does not fit into an int. *)
let shiftl x n = Z.shift_left x (Z.to_int n);;

let shiftr x n = Z.shift_right x (Z.to_int n);;

let test_bit x n =  Z.testbit x (Z.to_int n);;

end;; (*struct Bits_Integer*)

module Automata_lib = struct

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec less_eq_prod _A _B
  (x1, y1) (x2, y2) = less _A x1 x2 || less_eq _A x1 x2 && less_eq _B y1 y2;;

let rec less_prod _A _B
  (x1, y1) (x2, y2) = less _A x1 x2 || less_eq _A x1 x2 && less _B y1 y2;;

let rec ord_prod _A _B =
  ({less_eq = less_eq_prod _A _B; less = less_prod _A _B} : ('a * 'b) ord);;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

let rec preorder_prod _A _B =
  ({ord_preorder = (ord_prod _A.ord_preorder _B.ord_preorder)} :
    ('a * 'b) preorder);;

let rec order_prod _A _B =
  ({preorder_order = (preorder_prod _A.preorder_order _B.preorder_order)} :
    ('a * 'b) order);;

type 'a linorder = {order_linorder : 'a order};;

let rec linorder_prod _A _B =
  ({order_linorder = (order_prod _A.order_linorder _B.order_linorder)} :
    ('a * 'b) linorder);;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

type nat = Nat of Z.t;;

type 'a nFA_states = {states_enumerate : nat -> 'a};;
let states_enumerate _A = _A.states_enumerate;;

type num = One | Bit0 of num | Bit1 of num;;

type color = R | B;;

type ('a, 'b) rbta = Empty |
  Branch of color * ('a, 'b) rbta * 'a * 'b * ('a, 'b) rbta;;

type ('b, 'a) rbt = RBT of ('b, 'a) rbta;;

let rec id x = (fun xa -> xa) x;;

let rec integer_of_nat (Nat x) = x;;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Z.of_int 1);;

let rec suc n = plus_nat n one_nat;;

let rec comp f g = (fun x -> f (g x));;

let rec empty _A = RBT Empty;;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec balance
  x0 s t x3 = match x0, s, t, x3 with
    Branch (R, a, w, x, b), s, t, Branch (R, c, y, z, d) ->
      Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z, Empty ->
        Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (R, a, w, x, b), s, t, c), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, a, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z, Empty ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c)), y,
        z, Empty
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (R, Empty, w, x, Branch (R, b, s, t, c)), y, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c)), y,
        z, Branch (B, va, vb, vc, vd)
        -> Branch
             (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Empty, w, x, Branch (R, b, s, t, Branch (R, c, y, z, d)) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, b, s, t, Branch (R, c, y, z, d))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, d))
    | Empty, w, x, Branch (R, Branch (R, b, s, t, c), y, z, Empty) ->
        Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
    | Empty, w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))
        -> Branch
             (R, Branch (B, Empty, w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Empty)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Empty))
    | Branch (B, va, vb, vc, vd), w, x,
        Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
               Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
    | Empty, s, t, Empty -> Branch (B, Empty, s, t, Empty)
    | Empty, s, t, Branch (B, va, vb, vc, vd) ->
        Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
    | Empty, s, t, Branch (v, Empty, vb, vc, Empty) ->
        Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
    | Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
    | Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)) ->
        Branch
          (B, Empty, s, t,
            Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
    | Empty, s, t,
        Branch
          (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi))
        -> Branch
             (B, Empty, s, t,
               Branch
                 (v, Branch (B, ve, vj, vk, vl), vb, vc,
                   Branch (B, vf, vg, vh, vi)))
    | Branch (B, va, vb, vc, vd), s, t, Empty ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
    | Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh) ->
        Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
    | Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty) ->
        Branch
          (B, Branch (B, va, vb, vc, vd), s, t,
            Branch (v, Empty, vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
    | Branch (B, va, vb, vc, vd), s, t,
        Branch
          (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm))
        -> Branch
             (B, Branch (B, va, vb, vc, vd), s, t,
               Branch
                 (v, Branch (B, vi, vn, vo, vp), vf, vg,
                   Branch (B, vj, vk, vl, vm)))
    | Branch (v, Empty, vb, vc, Empty), s, t, Empty ->
        Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
    | Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty ->
        Branch
          (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t,
            Empty)
    | Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty ->
        Branch
          (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t,
            Empty)
    | Branch
        (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty
        -> Branch
             (B, Branch
                   (v, Branch (B, vf, vg, vh, vi), vb, vc,
                     Branch (B, ve, vj, vk, vl)),
               s, t, Empty)
    | Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd) ->
        Branch
          (B, Branch (v, Empty, vf, vg, Empty), s, t,
            Branch (B, va, vb, vc, vd))
    | Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
               Branch (B, va, vb, vc, vd))
    | Branch
        (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd)
        -> Branch
             (B, Branch
                   (v, Branch (B, vj, vk, vl, vm), vf, vg,
                     Branch (B, vi, vn, vo, vp)),
               s, t, Branch (B, va, vb, vc, vd));;

let rec rbt_ins _A
  f k v x3 = match f, k, v, x3 with
    f, k, v, Empty -> Branch (R, Empty, k, v, Empty)
    | f, k, v, Branch (B, l, x, y, r) ->
        (if less _A k x then balance (rbt_ins _A f k v l) x y r
          else (if less _A x k then balance l x y (rbt_ins _A f k v r)
                 else Branch (B, l, x, f k y v, r)))
    | f, k, v, Branch (R, l, x, y, r) ->
        (if less _A k x then Branch (R, rbt_ins _A f k v l, x, y, r)
          else (if less _A x k then Branch (R, l, x, y, rbt_ins _A f k v r)
                 else Branch (R, l, x, f k y v, r)));;

let rec paint c x1 = match c, x1 with c, Empty -> Empty
                | c, Branch (uu, l, k, v, r) -> Branch (c, l, k, v, r);;

let rec rbt_insert_with_key _A f k v t = paint B (rbt_ins _A f k v t);;

let rec rbt_insert _A = rbt_insert_with_key _A (fun _ _ nv -> nv);;

let rec impl_of _B (RBT x) = x;;

let rec insert _A
  xc xd xe =
    RBT (rbt_insert _A.order_linorder.preorder_order.ord_preorder xc xd
          (impl_of _A xe));;

let rec rbt_lookup _A
  x0 k = match x0, k with Empty, k -> None
    | Branch (uu, l, x, y, r), k ->
        (if less _A k x then rbt_lookup _A l k
          else (if less _A x k then rbt_lookup _A r k else Some y));;

let rec lookup _A
  x = rbt_lookup _A.order_linorder.preorder_order.ord_preorder (impl_of _A x);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec product x0 uu = match x0, uu with [], uu -> []
                  | x :: xs, ys -> map (fun a -> (x, a)) ys @ product xs ys;;

let rec snd (x1, x2) = x2;;

let rec fst (x1, x2) = x1;;

let rec nempI _A s = less_eq _A (fst s) (snd s);;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec worklist
  b f x2 = match b, f, x2 with
    b, f, (s, e :: wl) ->
      (if b s then (let (sa, n) = f s e in worklist b f (sa, n @ wl))
        else (s, e :: wl))
    | b, f, (s, []) -> (s, []);;

let rec ltsga_image
  imf f =
    imf f (fun _ -> true) (fun _ -> true) (fun _ -> true) (fun _ -> true);;

let rec the (Some x2) = x2;;

let rec apsnd f (x, y) = (x, f y);;

let rec intersectI _A _B
  s1 s2 =
    ((if less _A (fst s1) (fst s2) then fst s2 else fst s1),
      (if less _B (snd s1) (snd s2) then snd s1 else snd s2));;

let rec iterate_to_list it = it (fun _ -> true) (fun a b -> a :: b) [];;

let rec ltsga_to_list it = comp iterate_to_list it;;

let rec ltsga_iterator
  it = it (fun _ -> true) (fun _ -> true) (fun _ -> true) (fun _ -> true);;

let rec rm_iterateoi
  x0 c f sigma = match x0, c, f, sigma with Empty, c, f, sigma -> sigma
    | Branch (col, l, k, v, r), c, f, sigma ->
        (if c sigma
          then (let sigmaa = rm_iterateoi l c f sigma in
                 (if c sigmaa then rm_iterateoi r c f (f (k, v) sigmaa)
                   else sigmaa))
          else sigma);;

let rec iteratei_set_op_list_it_rs_ops _A
  s = (fun c f -> rm_iterateoi (impl_of _A s) c (comp f fst));;

let rec iteratei_map_op_list_it_rm_ops _A s = rm_iterateoi (impl_of _A s);;

let rec map_iterator_key_filter
  p it =
    (fun c f ->
      it c (fun x sigma -> (if p (fst x) then f x sigma else sigma)));;

let rec map_iterator_product
  it_a it_b =
    (fun c f -> it_a c (fun a -> it_b (snd a) c (fun b -> f (fst a, b))));;

let rec set_iterator_filter
  p it = (fun c f -> it c (fun x sigma -> (if p x then f x sigma else sigma)));;

let rec map_to_set_iterator m it = it m;;

let rec ltsbm_filter_it
  it1 it2 it3 p_v1 p_e p_v2 p m1 =
    set_iterator_filter (fun (v, (e, va)) -> p_v2 va && p (v, (e, va)))
      (map_iterator_product
        (map_iterator_key_filter p_v1 (map_to_set_iterator m1 it1))
        (fun m2 ->
          map_iterator_product
            (map_iterator_key_filter p_e (map_to_set_iterator m2 it2)) it3));;

let rec ltsbm_it it1 it2 it3 = ltsga_iterator (ltsbm_filter_it it1 it2 it3);;

let rec rs_lts_it _A _B _C
  = ltsbm_it (iteratei_map_op_list_it_rm_ops _A)
      (iteratei_map_op_list_it_rm_ops _B) (iteratei_set_op_list_it_rs_ops _C);;

let rec divmod_integer
  k l = (if Z.equal k Z.zero then (Z.zero, Z.zero)
          else (if Z.lt Z.zero l
                 then (if Z.lt Z.zero k
                        then (fun k l -> if Z.equal Z.zero l then
                               (Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
                               k l
                        else (let (r, s) =
                                (fun k l -> if Z.equal Z.zero l then
                                  (Z.zero, l) else Z.div_rem (Z.abs k)
                                  (Z.abs l))
                                  k l
                                in
                               (if Z.equal s Z.zero then (Z.neg r, Z.zero)
                                 else (Z.sub (Z.neg r) (Z.of_int 1),
Z.sub l s))))
                 else (if Z.equal l Z.zero then (Z.zero, k)
                        else apsnd Z.neg
                               (if Z.lt k Z.zero
                                 then (fun k l -> if Z.equal Z.zero l then
(Z.zero, l) else Z.div_rem (Z.abs k) (Z.abs l))
k l
                                 else (let (r, s) =
 (fun k l -> if Z.equal Z.zero l then (Z.zero, l) else Z.div_rem (Z.abs k)
   (Z.abs l))
   k l
 in
(if Z.equal s Z.zero then (Z.neg r, Z.zero)
  else (Z.sub (Z.neg r) (Z.of_int 1), Z.sub (Z.neg l) s)))))));;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec times_nat m n = Nat (Z.mul (integer_of_nat m) (integer_of_nat n));;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec triangle
  n = divide_nat (times_nat n (suc n)) (nat_of_integer (Z.of_int 2));;

let rec empty_rm_basic_ops _A = (fun _ -> empty _A);;

let rec ins_rm_basic_ops _A x s = insert _A x () s;;

let rec g_sng_dflt_basic_oops_rm_basic_ops _A
  x = ins_rm_basic_ops _A x (empty_rm_basic_ops _A ());;

let rec g_sng_rm_basic_ops _A k v = insert _A k v (empty _A);;

let rec rs_lts_add _A _B
  = (fun v w va l ->
      (match lookup _A l v
        with None ->
          insert _A v
            (g_sng_rm_basic_ops _B w (g_sng_dflt_basic_oops_rm_basic_ops _A va))
            l
        | Some m2 ->
          (match lookup _B m2 w
            with None ->
              insert _A v
                (insert _B w (g_sng_dflt_basic_oops_rm_basic_ops _A va) m2) l
            | Some s3 ->
              insert _A v (insert _B w (ins_rm_basic_ops _A va s3) m2) l)));;

let rec ltsga_image_filter
  e a it f p_v1 p_e p_v2 p l =
    it p_v1 p_e p_v2 p l (fun _ -> true)
      (fun vev la -> (let (v, (ea, va)) = f vev in a v ea va la))
      e;;

let rec rs_lts_empty _A _B = empty _A;;

let rec rs_lts_filter_it _A _B _C
  = ltsbm_filter_it (iteratei_map_op_list_it_rm_ops _A)
      (iteratei_map_op_list_it_rm_ops _B) (iteratei_set_op_list_it_rs_ops _C);;

let rec rs_lts_image_filter _A _B _C _D
  = ltsga_image_filter (rs_lts_empty _C _D) (rs_lts_add _C _D)
      (rs_lts_filter_it _A _B _A);;

let rec rs_lts_image _A _B _C _D
  = ltsga_image (rs_lts_image_filter _A _B _C _D);;

let rec prod_encode x = (fun (m, n) -> plus_nat (triangle (plus_nat m n)) m) x;;

let zero_nat : nat = Nat Z.zero;;

let rec set_iterator_emp c f sigma_0 = sigma_0;;

let rec rs_lts_succ_it _A _B
  = (fun m1 v _ ->
      (match lookup _A m1 v with None -> set_iterator_emp
        | Some m2 ->
          map_iterator_product (iteratei_map_op_list_it_rm_ops _B m2)
            (iteratei_set_op_list_it_rs_ops _A)));;

let rec rs_lts_to_list _A _B = ltsga_to_list (rs_lts_it _A _B _A);;

let rec iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops _A
  s = (fun c f -> rm_iterateoi (impl_of _A s) c (comp f fst));;

let rec g_to_list_dflt_basic_oops_rm_basic_ops _A
  s = iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops _A s (fun _ -> true)
        (fun a b -> a :: b) [];;

let rec g_isEmpty_dflt_basic_oops_rm_basic_ops _A
  s = iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops _A s (fun c -> c)
        (fun _ _ -> false) true;;

let rec ins_dj_rm_basic_ops _A x s = insert _A x () s;;

let rec memb_rm_basic_ops _A x s = not (is_none (lookup _A s x));;

let rec g_inter_dflt_basic_oops_rm_basic_ops _A
  s1 s2 =
    iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops _A s1 (fun _ -> true)
      (fun x s ->
        (if memb_rm_basic_ops _A x s2 then ins_dj_rm_basic_ops _A x s else s))
      (empty_rm_basic_ops _A ());;

let rec set_iterator_union
  it_a it_b = (fun c f sigma_0 -> it_b c f (it_a c f sigma_0));;

let rec rs_lts_succ_label_it _A _B
  = (fun m1 v ->
      (match lookup _A m1 v with None -> set_iterator_emp
        | Some m2 ->
          map_iterator_product (iteratei_map_op_list_it_rm_ops _B m2)
            (iteratei_set_op_list_it_rs_ops _A)));;

let rec set_iterator_image_filter
  g it =
    (fun c f ->
      it c (fun x sigma ->
             (match g x with None -> sigma | Some xa -> f xa sigma)));;

let rec rs_lts_connect_it _A _B _C
  = (fun m1 sa si v ->
      (match lookup _A m1 v with None -> (fun _ _ sigma_0 -> sigma_0)
        | Some m2 ->
          map_iterator_product
            (set_iterator_image_filter
              (fun a ->
                (if not (g_isEmpty_dflt_basic_oops_rm_basic_ops _A
                          (g_inter_dflt_basic_oops_rm_basic_ops _A (snd a) sa))
                  then Some a else None))
              (iteratei_map_op_list_it_rm_ops _B m2))
            (fun _ -> iteratei_set_op_list_it_rs_ops _C si)));;

let rec rs_nfa_concate (_A1, _A2) _B
  (q1, (d1, (i1, f1))) (q2, (d2, (i2, f2))) =
    (let a =
       foldl (fun (a, b) ->
               (let (qm, n) = a in
                 (fun is q ->
                   ((insert _A2 (id q) (states_enumerate _A1 n) qm, suc n),
                     ins_dj_rm_basic_ops _A2 (states_enumerate _A1 n) is)))
                 b)
         ((empty _A2, zero_nat), empty_rm_basic_ops _A2 ())
         (if not (g_isEmpty_dflt_basic_oops_rm_basic_ops _A2
                   (g_inter_dflt_basic_oops_rm_basic_ops _A2 i1 f1))
           then g_to_list_dflt_basic_oops_rm_basic_ops _A2 i1 @
                  g_to_list_dflt_basic_oops_rm_basic_ops _A2 i2
           else g_to_list_dflt_basic_oops_rm_basic_ops _A2 i1)
       in
     let (aa, b) = a in
      (let (qm, n) = aa in
        (fun is ->
          (let ab =
             worklist (fun _ -> true)
               (fun (ab, ba) ->
                 (let (qma, na) = ab in
                   (fun (qs, (dd, (isa, fs))) q ->
                     (let r = the (lookup _A2 qma (id q)) in
                       (if memb_rm_basic_ops _A2 r qs
                         then (((qma, na), (qs, (dd, (isa, fs)))), [])
                         else (let ac =
                                 set_iterator_union
                                   (rs_lts_succ_label_it _A2
                                     (linorder_prod _B _B) d1 q)
                                   (set_iterator_union
                                     (rs_lts_succ_label_it _A2
                                       (linorder_prod _B _B) d2 q)
                                     (rs_lts_connect_it _A2
                                       (linorder_prod _B _B) _A2 d1 f1 i2 q))
                                   (fun _ -> true)
                                   (fun (ac, qa) (bb, c) ->
                                     (let (qmb, nb) = bb in
                                       (fun (dda, naa) ->
 (if nempI _B.order_linorder.preorder_order.ord_preorder ac
   then (let r_opt = lookup _A2 qmb (id qa) in
         let bc =
           (if is_none r_opt
             then (let ra = states_enumerate _A1 nb in
                    ((insert _A2 (id qa) ra qmb, suc nb), ra))
             else ((qmb, nb), the r_opt))
           in
         let (bd, ca) = bc in
          (let (qmc, nc) = bd in
            (fun ra ->
              ((qmc, nc),
                (rs_lts_add _A2 (linorder_prod _B _B) r ac ra dda, qa :: naa))))
            ca)
   else ((qmb, nb), (dda, naa)))))
                                       c)
                                   ((qma, na), (dd, []))
                                 in
                               let (ad, bb) = ac in
                                (let (qmb, nb) = ad in
                                  (fun (dda, ae) ->
                                    (((qmb, nb),
                                       (ins_dj_rm_basic_ops _A2 r qs,
 (dda, (isa, (if memb_rm_basic_ops _A2 q f2 then ins_dj_rm_basic_ops _A2 r fs
               else fs))))),
                                      ae)))
                                  bb)))))
                   ba)
               (((qm, n),
                  (empty_rm_basic_ops _A2 (),
                    (rs_lts_empty _A2 (linorder_prod _B _B),
                      (is, empty_rm_basic_ops _A2 ())))),
                 (if not (g_isEmpty_dflt_basic_oops_rm_basic_ops _A2
                           (g_inter_dflt_basic_oops_rm_basic_ops _A2 i1 f1))
                   then g_to_list_dflt_basic_oops_rm_basic_ops _A2 i1 @
                          g_to_list_dflt_basic_oops_rm_basic_ops _A2 i2
                   else g_to_list_dflt_basic_oops_rm_basic_ops _A2 i1))
             in
           let (ac, ba) = ab in
            (let (_, aaa) = ac in (fun _ -> aaa)) ba)))
        b);;

let rec ltsga_to_collect_list to_list l = to_list l;;

let rec rs_lts_to_collect_list _A _B
  = ltsga_to_collect_list (rs_lts_to_list _A _B);;

let rec rs_nfa_destruct (_A1, _A2) _B
  (q, (d, (i, f))) =
    (g_to_list_dflt_basic_oops_rm_basic_ops _A2 q,
      (rs_lts_to_collect_list _A2 (linorder_prod _B _B) d,
        (g_to_list_dflt_basic_oops_rm_basic_ops _A2 i,
          g_to_list_dflt_basic_oops_rm_basic_ops _A2 f)));;

let rec rs_nfa_bool_comb (_A1, _A2) _B
  bc (q1, (d1, (i1, f1))) (q2, (d2, (i2, f2))) =
    (let a =
       foldl (fun (a, b) ->
               (let (qm, n) = a in
                 (fun is q ->
                   ((insert (linorder_prod _A2 _A2) (id q)
                       (states_enumerate _A1 n) qm,
                      suc n),
                     ins_dj_rm_basic_ops _A2 (states_enumerate _A1 n) is)))
                 b)
         ((empty (linorder_prod _A2 _A2), zero_nat), empty_rm_basic_ops _A2 ())
         (product (g_to_list_dflt_basic_oops_rm_basic_ops _A2 i1)
           (g_to_list_dflt_basic_oops_rm_basic_ops _A2 i2))
       in
     let (aa, b) = a in
      (let (qm, n) = aa in
        (fun is ->
          (let ab =
             worklist (fun _ -> true)
               (fun (ab, ba) ->
                 (let (qma, na) = ab in
                   (fun (qs, (dd, (isa, fs))) q ->
                     (let r = the (lookup (linorder_prod _A2 _A2) qma (id q)) in
                       (if memb_rm_basic_ops _A2 r qs
                         then (((qma, na), (qs, (dd, (isa, fs)))), [])
                         else (let ac =
                                 (let (q1a, q2a) = q in
                                   (fun c f ->
                                     rs_lts_succ_label_it _A2
                                       (linorder_prod _B _B) d1 q1a c
                                       (fun (a1, q1b) ->
 rs_lts_succ_it _A2 (linorder_prod _B _B) d2 q2a a1 c
   (fun (a2, q2b) -> f ((a1, a2), (q1b, q2b))))))
                                   (fun _ -> true)
                                   (fun (ac, qa) (bb, c) ->
                                     (let (qmb, nb) = bb in
                                       (fun (dda, naa) ->
 (if nempI _B.order_linorder.preorder_order.ord_preorder
       (intersectI _B.order_linorder.preorder_order.ord_preorder
         _B.order_linorder.preorder_order.ord_preorder (fst ac) (snd ac))
   then (let r_opt = lookup (linorder_prod _A2 _A2) qmb (id qa) in
         let bd =
           (if is_none r_opt
             then (let ra = states_enumerate _A1 nb in
                    ((insert (linorder_prod _A2 _A2) (id qa) ra qmb, suc nb),
                      ra))
             else ((qmb, nb), the r_opt))
           in
         let (be, ca) = bd in
          (let (qmc, nc) = be in
            (fun ra ->
              ((qmc, nc),
                (rs_lts_add _A2 (linorder_prod _B _B) r
                   (intersectI _B.order_linorder.preorder_order.ord_preorder
                     _B.order_linorder.preorder_order.ord_preorder (fst ac)
                     (snd ac))
                   ra dda,
                  qa :: naa))))
            ca)
   else ((qmb, nb), (dda, naa)))))
                                       c)
                                   ((qma, na), (dd, []))
                                 in
                               let (ad, bb) = ac in
                                (let (qmb, nb) = ad in
                                  (fun (dda, ae) ->
                                    (((qmb, nb),
                                       (ins_dj_rm_basic_ops _A2 r qs,
 (dda, (isa, (if (let (q1a, q2a) = q in
                   bc (memb_rm_basic_ops _A2 q1a f1)
                     (memb_rm_basic_ops _A2 q2a f2))
               then ins_dj_rm_basic_ops _A2 r fs else fs))))),
                                      ae)))
                                  bb)))))
                   ba)
               (((qm, n),
                  (empty_rm_basic_ops _A2 (),
                    (rs_lts_empty _A2 (linorder_prod _B _B),
                      (is, empty_rm_basic_ops _A2 ())))),
                 product (g_to_list_dflt_basic_oops_rm_basic_ops _A2 i1)
                   (g_to_list_dflt_basic_oops_rm_basic_ops _A2 i2))
             in
           let (ac, ba) = ab in
            (let (_, aaa) = ac in (fun _ -> aaa)) ba)))
        b);;

let rec nfa_acceptingp a = snd (snd (snd a));;

let rec nfa_initialp a = fst (snd (snd a));;

let rec nfa_transp a = fst (snd a);;

let rec rs_nfa_concate_rename (_A1, _A2) _B
  f1a f2a (q1, (d1, (i1, f1))) (q2, (d2, (i2, f2))) =
    (let nA1 =
       (iteratei_set_op_list_it_rs_ops _A2 q1 (fun _ -> true)
          (fun b -> ins_rm_basic_ops (linorder_prod _A2 _A2) (f1a b))
          (empty_rm_basic_ops (linorder_prod _A2 _A2) ()),
         (rs_lts_image _A2 (linorder_prod _B _B) (linorder_prod _A2 _A2)
            (linorder_prod _B _B)
            (fun qaq -> (f1a (fst qaq), (fst (snd qaq), f1a (snd (snd qaq)))))
            d1,
           (iteratei_set_op_list_it_rs_ops _A2 i1 (fun _ -> true)
              (fun b -> ins_rm_basic_ops (linorder_prod _A2 _A2) (f1a b))
              (empty_rm_basic_ops (linorder_prod _A2 _A2) ()),
             iteratei_set_op_list_it_rs_ops _A2 f1 (fun _ -> true)
               (fun b -> ins_rm_basic_ops (linorder_prod _A2 _A2) (f1a b))
               (empty_rm_basic_ops (linorder_prod _A2 _A2) ()))))
       in
     let aA2 =
       (iteratei_set_op_list_it_rs_ops _A2 q2 (fun _ -> true)
          (fun b -> ins_rm_basic_ops (linorder_prod _A2 _A2) (f2a b))
          (empty_rm_basic_ops (linorder_prod _A2 _A2) ()),
         (rs_lts_image _A2 (linorder_prod _B _B) (linorder_prod _A2 _A2)
            (linorder_prod _B _B)
            (fun qaq -> (f2a (fst qaq), (fst (snd qaq), f2a (snd (snd qaq)))))
            d2,
           (iteratei_set_op_list_it_rs_ops _A2 i2 (fun _ -> true)
              (fun b -> ins_rm_basic_ops (linorder_prod _A2 _A2) (f2a b))
              (empty_rm_basic_ops (linorder_prod _A2 _A2) ()),
             iteratei_set_op_list_it_rs_ops _A2 f2 (fun _ -> true)
               (fun b -> ins_rm_basic_ops (linorder_prod _A2 _A2) (f2a b))
               (empty_rm_basic_ops (linorder_prod _A2 _A2) ()))))
       in
     let a =
       foldl (fun (a, b) ->
               (let (qm, n) = a in
                 (fun is q ->
                   ((insert (linorder_prod _A2 _A2) (id q)
                       (states_enumerate _A1 n) qm,
                      suc n),
                     ins_dj_rm_basic_ops _A2 (states_enumerate _A1 n) is)))
                 b)
         ((empty (linorder_prod _A2 _A2), zero_nat), empty_rm_basic_ops _A2 ())
         (if not (g_isEmpty_dflt_basic_oops_rm_basic_ops (linorder_prod _A2 _A2)
                   (g_inter_dflt_basic_oops_rm_basic_ops (linorder_prod _A2 _A2)
                     (nfa_initialp nA1) (nfa_acceptingp nA1)))
           then g_to_list_dflt_basic_oops_rm_basic_ops (linorder_prod _A2 _A2)
                  (nfa_initialp nA1) @
                  g_to_list_dflt_basic_oops_rm_basic_ops (linorder_prod _A2 _A2)
                    (nfa_initialp aA2)
           else g_to_list_dflt_basic_oops_rm_basic_ops (linorder_prod _A2 _A2)
                  (nfa_initialp nA1))
       in
     let (aa, b) = a in
      (let (qm, n) = aa in
        (fun is ->
          (let ab =
             worklist (fun _ -> true)
               (fun (ab, ba) ->
                 (let (qma, na) = ab in
                   (fun (qs, (dd, (isa, fs))) q ->
                     (let r = the (lookup (linorder_prod _A2 _A2) qma (id q)) in
                       (if memb_rm_basic_ops _A2 r qs
                         then (((qma, na), (qs, (dd, (isa, fs)))), [])
                         else (let ac =
                                 set_iterator_union
                                   (rs_lts_succ_label_it (linorder_prod _A2 _A2)
                                     (linorder_prod _B _B) (nfa_transp nA1) q)
                                   (set_iterator_union
                                     (rs_lts_succ_label_it
                                       (linorder_prod _A2 _A2)
                                       (linorder_prod _B _B) (nfa_transp aA2) q)
                                     (rs_lts_connect_it (linorder_prod _A2 _A2)
                                       (linorder_prod _B _B)
                                       (linorder_prod _A2 _A2) (nfa_transp nA1)
                                       (nfa_acceptingp nA1) (nfa_initialp aA2)
                                       q))
                                   (fun _ -> true)
                                   (fun (ac, qa) (bb, c) ->
                                     (let (qmb, nb) = bb in
                                       (fun (dda, naa) ->
 (if nempI _B.order_linorder.preorder_order.ord_preorder ac
   then (let r_opt = lookup (linorder_prod _A2 _A2) qmb (id qa) in
         let bc =
           (if is_none r_opt
             then (let ra = states_enumerate _A1 nb in
                    ((insert (linorder_prod _A2 _A2) (id qa) ra qmb, suc nb),
                      ra))
             else ((qmb, nb), the r_opt))
           in
         let (bd, ca) = bc in
          (let (qmc, nc) = bd in
            (fun ra ->
              ((qmc, nc),
                (rs_lts_add _A2 (linorder_prod _B _B) r ac ra dda, qa :: naa))))
            ca)
   else ((qmb, nb), (dda, naa)))))
                                       c)
                                   ((qma, na), (dd, []))
                                 in
                               let (ad, bb) = ac in
                                (let (qmb, nb) = ad in
                                  (fun (dda, ae) ->
                                    (((qmb, nb),
                                       (ins_dj_rm_basic_ops _A2 r qs,
 (dda, (isa, (if memb_rm_basic_ops (linorder_prod _A2 _A2) q
                   (nfa_acceptingp aA2)
               then ins_dj_rm_basic_ops _A2 r fs else fs))))),
                                      ae)))
                                  bb)))))
                   ba)
               (((qm, n),
                  (empty_rm_basic_ops _A2 (),
                    (rs_lts_empty _A2 (linorder_prod _B _B),
                      (is, empty_rm_basic_ops _A2 ())))),
                 (if not (g_isEmpty_dflt_basic_oops_rm_basic_ops
                           (linorder_prod _A2 _A2)
                           (g_inter_dflt_basic_oops_rm_basic_ops
                             (linorder_prod _A2 _A2) (nfa_initialp nA1)
                             (nfa_acceptingp nA1)))
                   then g_to_list_dflt_basic_oops_rm_basic_ops
                          (linorder_prod _A2 _A2) (nfa_initialp nA1) @
                          g_to_list_dflt_basic_oops_rm_basic_ops
                            (linorder_prod _A2 _A2) (nfa_initialp aA2)
                   else g_to_list_dflt_basic_oops_rm_basic_ops
                          (linorder_prod _A2 _A2) (nfa_initialp nA1)))
             in
           let (ac, ba) = ab in
            (let (_, aaa) = ac in (fun _ -> aaa)) ba)))
        b);;

let rec g_from_list_aux_dflt_basic_oops_rm_basic_ops _A
  accs x1 = match accs, x1 with
    accs, x :: l ->
      g_from_list_aux_dflt_basic_oops_rm_basic_ops _A
        (ins_rm_basic_ops _A x accs) l
    | y, [] -> y;;

let rec g_from_list_dflt_basic_oops_rm_basic_ops _A
  l = g_from_list_aux_dflt_basic_oops_rm_basic_ops _A (empty_rm_basic_ops _A ())
        l;;

let rec rs_nfa_construct_interval (_A1, _A2) _B
  (ql, (dl, (il, fl))) =
    foldl (fun (q, (d, (i, f))) (q1, (l, q2)) ->
            (ins_rm_basic_ops _A2 q1 (ins_rm_basic_ops _A2 q2 q),
              (rs_lts_add _A2 (linorder_prod _B _B) q1 l q2 d, (i, f))))
      (g_from_list_dflt_basic_oops_rm_basic_ops _A2 (ql @ il @ fl),
        (rs_lts_empty _A2 (linorder_prod _B _B),
          (g_from_list_dflt_basic_oops_rm_basic_ops _A2 il,
            g_from_list_dflt_basic_oops_rm_basic_ops _A2 fl)))
      dl;;

end;; (*struct Automata_lib*)
