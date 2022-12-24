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

module Fun : sig
  val id : 'a -> 'a
  val comp : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
end = struct

let rec id x = (fun xa -> xa) x;;

let rec comp f g = (fun x -> f (g x));;

end;; (*struct Fun*)

module Orderings : sig
  type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool}
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  type 'a preorder = {ord_preorder : 'a ord}
  type 'a order = {preorder_order : 'a preorder}
  type 'a linorder = {order_linorder : 'a order}
end = struct

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

type 'a linorder = {order_linorder : 'a order};;

end;; (*struct Orderings*)

module RBT_Impl : sig
  type color
  type ('a, 'b) rbt = Empty |
    Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt
  val rbt_delete : 'a Orderings.ord -> 'a -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rbt_insert : 'a Orderings.ord -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val rbt_lookup : 'a Orderings.ord -> ('a, 'b) rbt -> 'a -> 'b option
end = struct

type color = R | B;;

type ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;;

let rec paint c x1 = match c, x1 with c, Empty -> Empty
                | c, Branch (uu, l, k, v, r) -> Branch (c, l, k, v, r);;

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

let rec balance_left
  x0 s y c = match x0, s, y, c with
    Branch (R, a, k, x, b), s, y, c ->
      Branch (R, Branch (B, a, k, x, b), s, y, c)
    | Empty, k, x, Branch (B, a, s, y, b) ->
        balance Empty k x (Branch (R, a, s, y, b))
    | Branch (B, va, vb, vc, vd), k, x, Branch (B, a, s, y, b) ->
        balance (Branch (B, va, vb, vc, vd)) k x (Branch (R, a, s, y, b))
    | Empty, k, x, Branch (R, Branch (B, a, s, y, b), t, z, c) ->
        Branch (R, Branch (B, Empty, k, x, a), s, y, balance b t z (paint R c))
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (B, a, s, y, b), t, z, c)
        -> Branch
             (R, Branch (B, Branch (B, va, vb, vc, vd), k, x, a), s, y,
               balance b t z (paint R c))
    | Empty, k, x, Empty -> Empty
    | Empty, k, x, Branch (R, Empty, vb, vc, vd) -> Empty
    | Empty, k, x, Branch (R, Branch (R, ve, vf, vg, vh), vb, vc, vd) -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Empty -> Empty
    | Branch (B, va, vb, vc, vd), k, x, Branch (R, Empty, vf, vg, vh) -> Empty
    | Branch (B, va, vb, vc, vd), k, x,
        Branch (R, Branch (R, vi, vj, vk, vl), vf, vg, vh)
        -> Empty;;

let rec combine
  xa0 x = match xa0, x with Empty, x -> x
    | Branch (v, va, vb, vc, vd), Empty -> Branch (v, va, vb, vc, vd)
    | Branch (R, a, k, x, b), Branch (R, c, s, y, d) ->
        (match combine b c
          with Empty -> Branch (R, a, k, x, Branch (R, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, a, k, x, b), Branch (B, c, s, y, d) ->
        (match combine b c
          with Empty -> balance_left a k x (Branch (B, Empty, s, y, d))
          | Branch (R, b2, t, z, c2) ->
            Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
          | Branch (B, b2, t, z, c2) ->
            balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
    | Branch (B, va, vb, vc, vd), Branch (R, b, k, x, c) ->
        Branch (R, combine (Branch (B, va, vb, vc, vd)) b, k, x, c)
    | Branch (R, a, k, x, b), Branch (B, va, vb, vc, vd) ->
        Branch (R, a, k, x, combine b (Branch (B, va, vb, vc, vd)));;

let rec balance_right
  a k x xa3 = match a, k, x, xa3 with
    a, k, x, Branch (R, b, s, y, c) ->
      Branch (R, a, k, x, Branch (B, b, s, y, c))
    | Branch (B, a, k, x, b), s, y, Empty ->
        balance (Branch (R, a, k, x, b)) s y Empty
    | Branch (B, a, k, x, b), s, y, Branch (B, va, vb, vc, vd) ->
        balance (Branch (R, a, k, x, b)) s y (Branch (B, va, vb, vc, vd))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z, Empty ->
        Branch (R, balance (paint R a) k x b, s, y, Branch (B, c, t, z, Empty))
    | Branch (R, a, k, x, Branch (B, b, s, y, c)), t, z,
        Branch (B, va, vb, vc, vd)
        -> Branch
             (R, balance (paint R a) k x b, s, y,
               Branch (B, c, t, z, Branch (B, va, vb, vc, vd)))
    | Empty, k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Empty), k, x, Empty -> Empty
    | Branch (R, va, vb, vc, Branch (R, ve, vf, vg, vh)), k, x, Empty -> Empty
    | Empty, k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Empty), k, x, Branch (B, va, vb, vc, vd) -> Empty
    | Branch (R, ve, vf, vg, Branch (R, vi, vj, vk, vl)), k, x,
        Branch (B, va, vb, vc, vd)
        -> Empty;;

let rec rbt_del _A
  x xa1 = match x, xa1 with x, Empty -> Empty
    | x, Branch (c, a, y, s, b) ->
        (if Orderings.less _A x y then rbt_del_from_left _A x a y s b
          else (if Orderings.less _A y x then rbt_del_from_right _A x a y s b
                 else combine a b))
and rbt_del_from_left _A
  x xa1 y s b = match x, xa1, y, s, b with
    x, Branch (B, lt, z, v, rt), y, s, b ->
      balance_left (rbt_del _A x (Branch (B, lt, z, v, rt))) y s b
    | x, Empty, y, s, b -> Branch (R, rbt_del _A x Empty, y, s, b)
    | x, Branch (R, va, vb, vc, vd), y, s, b ->
        Branch (R, rbt_del _A x (Branch (R, va, vb, vc, vd)), y, s, b)
and rbt_del_from_right _A
  x a y s xa4 = match x, a, y, s, xa4 with
    x, a, y, s, Branch (B, lt, z, v, rt) ->
      balance_right a y s (rbt_del _A x (Branch (B, lt, z, v, rt)))
    | x, a, y, s, Empty -> Branch (R, a, y, s, rbt_del _A x Empty)
    | x, a, y, s, Branch (R, va, vb, vc, vd) ->
        Branch (R, a, y, s, rbt_del _A x (Branch (R, va, vb, vc, vd)));;

let rec rbt_ins _A
  f k v x3 = match f, k, v, x3 with
    f, k, v, Empty -> Branch (R, Empty, k, v, Empty)
    | f, k, v, Branch (B, l, x, y, r) ->
        (if Orderings.less _A k x then balance (rbt_ins _A f k v l) x y r
          else (if Orderings.less _A x k then balance l x y (rbt_ins _A f k v r)
                 else Branch (B, l, x, f k y v, r)))
    | f, k, v, Branch (R, l, x, y, r) ->
        (if Orderings.less _A k x then Branch (R, rbt_ins _A f k v l, x, y, r)
          else (if Orderings.less _A x k
                 then Branch (R, l, x, y, rbt_ins _A f k v r)
                 else Branch (R, l, x, f k y v, r)));;

let rec rbt_delete _A k t = paint B (rbt_del _A k t);;

let rec rbt_insert_with_key _A f k v t = paint B (rbt_ins _A f k v t);;

let rec rbt_insert _A = rbt_insert_with_key _A (fun _ _ nv -> nv);;

let rec rbt_lookup _A
  x0 k = match x0, k with Empty, k -> None
    | Branch (uu, l, x, y, r), k ->
        (if Orderings.less _A k x then rbt_lookup _A l k
          else (if Orderings.less _A x k then rbt_lookup _A r k else Some y));;

end;; (*struct RBT_Impl*)

module RBT : sig
  type ('b, 'a) rbt
  val empty : 'a Orderings.linorder -> ('a, 'b) rbt
  val impl_of : 'b Orderings.linorder -> ('b, 'a) rbt -> ('b, 'a) RBT_Impl.rbt
  val delete : 'a Orderings.linorder -> 'a -> ('a, 'b) rbt -> ('a, 'b) rbt
  val insert : 'a Orderings.linorder -> 'a -> 'b -> ('a, 'b) rbt -> ('a, 'b) rbt
  val lookup : 'a Orderings.linorder -> ('a, 'b) rbt -> 'a -> 'b option
end = struct

type ('b, 'a) rbt = RBT of ('b, 'a) RBT_Impl.rbt;;

let rec empty _A = RBT RBT_Impl.Empty;;

let rec impl_of _B (RBT x) = x;;

let rec delete _A
  xb xc =
    RBT (RBT_Impl.rbt_delete
          _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
          xb (impl_of _A xc));;

let rec insert _A
  xc xd xe =
    RBT (RBT_Impl.rbt_insert
          _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
          xc xd (impl_of _A xe));;

let rec lookup _A
  x = RBT_Impl.rbt_lookup
        _A.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
        (impl_of _A x);;

end;; (*struct RBT*)

module Arith : sig
  type nat
  val suc : nat -> nat
  val zero_nat : nat
end = struct

type nat = Nat of Z.t;;

type num = One | Bit0 of num | Bit1 of num;;

let rec integer_of_nat (Nat x) = x;;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Z.of_int 1);;

let rec suc n = plus_nat n one_nat;;

let zero_nat : nat = Nat Z.zero;;

end;; (*struct Arith*)

module Product_Type : sig
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
end = struct

let rec fst (x1, x2) = x1;;

let rec snd (x1, x2) = x2;;

end;; (*struct Product_Type*)

module LTSGA : sig
  val ltsga_image :
    ('a ->
      ('b -> bool) -> ('c -> bool) -> ('d -> bool) -> ('e -> bool) -> 'f) ->
      'a -> 'f
  val ltsga_image_filter :
    'a -> ('b -> 'c -> 'd -> 'a -> 'a) ->
            (('e -> bool) ->
              ('f -> bool) ->
                ('e -> bool) ->
                  ('e * ('f * 'e) -> bool) ->
                    'g -> ('a -> bool) ->
                            ('e * ('f * 'e) -> 'a -> 'a) -> 'a -> 'a) ->
              ('e * ('f * 'e) -> 'b * ('c * 'd)) ->
                ('e -> bool) ->
                  ('f -> bool) ->
                    ('e -> bool) -> ('e * ('f * 'e) -> bool) -> 'g -> 'a
end = struct

let rec ltsga_image
  imf f =
    imf f (fun _ -> true) (fun _ -> true) (fun _ -> true) (fun _ -> true);;

let rec ltsga_image_filter
  e a it f p_v1 p_e p_v2 p l =
    it p_v1 p_e p_v2 p l (fun _ -> true)
      (fun vev la -> (let (v, (ea, va)) = f vev in a v ea va la))
      e;;

end;; (*struct LTSGA*)

module Lista : sig
  val foldl : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val product : 'a list -> 'b list -> ('a * 'b) list
end = struct

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec product x0 uu = match x0, uu with [], uu -> []
                  | x :: xs, ys -> map (fun a -> (x, a)) ys @ product xs ys;;

end;; (*struct Lista*)

module Option : sig
  val is_none : 'a option -> bool
  val the : 'a option -> 'a
end = struct

let rec is_none = function Some x -> false
                  | None -> true;;

let rec the (Some x2) = x2;;

end;; (*struct Option*)

module NFA_set : sig
  type 'a nFA_states = {states_enumerate : Arith.nat -> 'a}
  val states_enumerate : 'a nFA_states -> Arith.nat -> 'a
end = struct

type 'a nFA_states = {states_enumerate : Arith.nat -> 'a};;
let states_enumerate _A = _A.states_enumerate;;

end;; (*struct NFA_set*)

module RBT_add : sig
  val rm_iterateoi :
    ('a, 'b) RBT_Impl.rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
end = struct

let rec rm_iterateoi
  x0 c f sigma = match x0, c, f, sigma with RBT_Impl.Empty, c, f, sigma -> sigma
    | RBT_Impl.Branch (col, l, k, v, r), c, f, sigma ->
        (if c sigma
          then (let sigmaa = rm_iterateoi l c f sigma in
                 (if c sigmaa then rm_iterateoi r c f (f (k, v) sigmaa)
                   else sigmaa))
          else sigma);;

end;; (*struct RBT_add*)

module Workset : sig
  val worklist :
    ('a -> bool) -> ('a -> 'b -> 'a * 'b list) -> 'a * 'b list -> 'a * 'b list
end = struct

let rec worklist
  b f x2 = match b, f, x2 with
    b, f, (s, e :: wl) ->
      (if b s then (let (sa, n) = f s e in worklist b f (sa, n @ wl))
        else (s, e :: wl))
    | b, f, (s, []) -> (s, []);;

end;; (*struct Workset*)

module Interval : sig
  val nempI : 'a Orderings.ord -> 'a * 'a -> bool
  val intersectI :
    'a Orderings.ord -> 'b Orderings.ord -> 'a * 'b -> 'a * 'b -> 'a * 'b
end = struct

let rec nempI _A
  s = Orderings.less_eq _A (Product_Type.fst s) (Product_Type.snd s);;

let rec intersectI _A _B
  s1 s2 =
    ((if Orderings.less _A (Product_Type.fst s1) (Product_Type.fst s2)
       then Product_Type.fst s2 else Product_Type.fst s1),
      (if Orderings.less _B (Product_Type.snd s1) (Product_Type.snd s2)
        then Product_Type.snd s1 else Product_Type.snd s2));;

end;; (*struct Interval*)

module SetIteratorOperations : sig
  val set_iterator_emp : ('a -> bool) -> ('b -> 'a -> 'a) -> 'a -> 'a
  val set_iterator_image :
    ('a -> 'b) ->
      (('c -> bool) -> ('a -> 'c -> 'c) -> 'c -> 'c) ->
        ('c -> bool) -> ('b -> 'c -> 'c) -> 'c -> 'c
  val set_iterator_union :
    (('a -> bool) -> ('b -> 'a -> 'a) -> 'a -> 'a) ->
      (('a -> bool) -> ('b -> 'a -> 'a) -> 'a -> 'a) ->
        ('a -> bool) -> ('b -> 'a -> 'a) -> 'a -> 'a
  val set_iterator_filter :
    ('a -> bool) ->
      (('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b) ->
        ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val map_iterator_product :
    (('a -> bool) -> ('b * 'c -> 'a -> 'a) -> 'a -> 'a) ->
      ('c -> ('a -> bool) -> ('d -> 'a -> 'a) -> 'a -> 'a) ->
        ('a -> bool) -> ('b * 'd -> 'a -> 'a) -> 'a -> 'a
  val set_iterator_product :
    (('a -> bool) -> ('b -> 'a -> 'a) -> 'a -> 'a) ->
      ('b -> ('a -> bool) -> ('c -> 'a -> 'a) -> 'a -> 'a) ->
        ('a -> bool) -> ('b * 'c -> 'a -> 'a) -> 'a -> 'a
  val map_iterator_key_filter :
    ('a -> bool) ->
      (('b -> bool) -> ('a * 'c -> 'b -> 'b) -> 'b -> 'b) ->
        ('b -> bool) -> ('a * 'c -> 'b -> 'b) -> 'b -> 'b
  val set_iterator_image_filter :
    ('a -> 'b option) ->
      (('c -> bool) -> ('a -> 'c -> 'c) -> 'c -> 'c) ->
        ('c -> bool) -> ('b -> 'c -> 'c) -> 'c -> 'c
end = struct

let rec set_iterator_emp c f sigma_0 = sigma_0;;

let rec set_iterator_image g it = (fun c f -> it c (fun x -> f (g x)));;

let rec set_iterator_union
  it_a it_b = (fun c f sigma_0 -> it_b c f (it_a c f sigma_0));;

let rec set_iterator_filter
  p it = (fun c f -> it c (fun x sigma -> (if p x then f x sigma else sigma)));;

let rec map_iterator_product
  it_a it_b =
    (fun c f ->
      it_a c
        (fun a ->
          it_b (Product_Type.snd a) c (fun b -> f (Product_Type.fst a, b))));;

let rec set_iterator_product
  it_a it_b = (fun c f -> it_a c (fun a -> it_b a c (fun b -> f (a, b))));;

let rec map_iterator_key_filter
  p it =
    (fun c f ->
      it c (fun x sigma ->
             (if p (Product_Type.fst x) then f x sigma else sigma)));;

let rec set_iterator_image_filter
  g it =
    (fun c f ->
      it c (fun x sigma ->
             (match g x with None -> sigma | Some xa -> f xa sigma)));;

end;; (*struct SetIteratorOperations*)

module Set_map_extend : sig
  val map_to_set_iterator : 'a -> ('a -> 'b -> 'c -> 'd) -> 'b -> 'c -> 'd
end = struct

let rec map_to_set_iterator m it = it m;;

end;; (*struct set_map_extend*)

module LTSByMap : sig
  val ltsbm_filter_it :
    ('a -> ('b -> bool) -> ('c * 'd -> 'b -> 'b) -> 'b -> 'b) ->
      ('d -> ('b -> bool) -> ('e * 'f -> 'b -> 'b) -> 'b -> 'b) ->
        ('f -> ('b -> bool) -> ('g -> 'b -> 'b) -> 'b -> 'b) ->
          ('c -> bool) ->
            ('e -> bool) ->
              ('g -> bool) ->
                ('c * ('e * 'g) -> bool) ->
                  'a -> ('b -> bool) -> ('c * ('e * 'g) -> 'b -> 'b) -> 'b -> 'b
end = struct

let rec ltsbm_filter_it
  it1 it2 it3 p_v1 p_e p_v2 p m1 =
    SetIteratorOperations.set_iterator_filter
      (fun (v, (e, va)) -> p_v2 va && p (v, (e, va)))
      (SetIteratorOperations.map_iterator_product
        (SetIteratorOperations.map_iterator_key_filter p_v1
          (Set_map_extend.map_to_set_iterator m1 it1))
        (fun m2 ->
          SetIteratorOperations.map_iterator_product
            (SetIteratorOperations.map_iterator_key_filter p_e
              (Set_map_extend.map_to_set_iterator m2 it2))
            it3));;

end;; (*struct LTSByMap*)

module RBTMapImpl : sig
  val g_sng_rm_basic_ops : 'a Orderings.linorder -> 'a -> 'b -> ('a, 'b) RBT.rbt
  val iteratei_map_op_list_it_rm_ops :
    'a Orderings.linorder ->
      ('a, 'b) RBT.rbt -> ('c -> bool) -> ('a * 'b -> 'c -> 'c) -> 'c -> 'c
end = struct

let rec g_sng_rm_basic_ops _A k v = RBT.insert _A k v (RBT.empty _A);;

let rec iteratei_map_op_list_it_rm_ops _A
  s = RBT_add.rm_iterateoi (RBT.impl_of _A s);;

end;; (*struct RBTMapImpl*)

module RBTSetImpl : sig
  val ins_rm_basic_ops :
    'a Orderings.linorder -> 'a -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt
  val memb_rm_basic_ops :
    'a Orderings.linorder -> 'a -> ('a, unit) RBT.rbt -> bool
  val empty_rm_basic_ops : 'a Orderings.linorder -> unit -> ('a, unit) RBT.rbt
  val ins_dj_rm_basic_ops :
    'a Orderings.linorder -> 'a -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt
  val iteratei_set_op_list_it_rs_ops :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val g_sng_dflt_basic_oops_rm_basic_ops :
    'a Orderings.linorder -> 'a -> ('a, unit) RBT.rbt
  val g_diff_dflt_basic_oops_rm_basic_ops :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt
  val g_inter_dflt_basic_oops_rm_basic_ops :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt
  val g_union_dflt_basic_oops_rm_basic_ops :
    'a Orderings.linorder ->
      ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt
  val g_subset_dflt_basic_oops_rm_basic_ops :
    'a Orderings.linorder -> ('a, unit) RBT.rbt -> ('a, unit) RBT.rbt -> bool
  val g_isEmpty_dflt_basic_oops_rm_basic_ops :
    'a Orderings.linorder -> ('a, unit) RBT.rbt -> bool
  val g_to_list_dflt_basic_oops_rm_basic_ops :
    'a Orderings.linorder -> ('a, unit) RBT.rbt -> 'a list
end = struct

let rec ins_rm_basic_ops _A x s = RBT.insert _A x () s;;

let rec memb_rm_basic_ops _A x s = not (Option.is_none (RBT.lookup _A s x));;

let rec empty_rm_basic_ops _A = (fun _ -> RBT.empty _A);;

let rec delete_rm_basic_ops _A x s = RBT.delete _A x s;;

let rec ins_dj_rm_basic_ops _A x s = RBT.insert _A x () s;;

let rec iteratei_set_op_list_it_rs_ops _A
  s = (fun c f ->
        RBT_add.rm_iterateoi (RBT.impl_of _A s) c
          (Fun.comp f Product_Type.fst));;

let rec g_sng_dflt_basic_oops_rm_basic_ops _A
  x = ins_rm_basic_ops _A x (empty_rm_basic_ops _A ());;

let rec iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops _A
  s = (fun c f ->
        RBT_add.rm_iterateoi (RBT.impl_of _A s) c
          (Fun.comp f Product_Type.fst));;

let rec g_ball_dflt_basic_oops_rm_basic_ops _A
  s p = iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops _A s (fun c -> c)
          (fun x _ -> p x) true;;

let rec g_diff_dflt_basic_oops_rm_basic_ops _A
  s1 s2 =
    iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops _A s2 (fun _ -> true)
      (delete_rm_basic_ops _A) s1;;

let rec g_inter_dflt_basic_oops_rm_basic_ops _A
  s1 s2 =
    iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops _A s1 (fun _ -> true)
      (fun x s ->
        (if memb_rm_basic_ops _A x s2 then ins_dj_rm_basic_ops _A x s else s))
      (empty_rm_basic_ops _A ());;

let rec g_union_dflt_basic_oops_rm_basic_ops _A
  s1 s2 =
    iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops _A s1 (fun _ -> true)
      (ins_rm_basic_ops _A) s2;;

let rec g_subset_dflt_basic_oops_rm_basic_ops _A
  s1 s2 =
    g_ball_dflt_basic_oops_rm_basic_ops _A s1
      (fun x -> memb_rm_basic_ops _A x s2);;

let rec g_isEmpty_dflt_basic_oops_rm_basic_ops _A
  s = iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops _A s (fun c -> c)
        (fun _ _ -> false) true;;

let rec g_to_list_dflt_basic_oops_rm_basic_ops _A
  s = iteratei_bset_op_list_it_dflt_basic_oops_rm_basic_ops _A s (fun _ -> true)
        (fun a b -> a :: b) [];;

end;; (*struct RBTSetImpl*)

module RBT_LTSImpl : sig
  val rs_lts_add :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      'a -> 'b -> 'a -> ('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt ->
                          ('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt
  val rs_lts_empty :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      ('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt
  val rs_lts_image :
    'a Orderings.linorder -> 'b Orderings.linorder -> 'c Orderings.linorder ->
      'd Orderings.linorder ->
      ('a * ('b * 'a) -> 'c * ('d * 'c)) ->
        ('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt ->
          ('c, ('d, ('c, unit) RBT.rbt) RBT.rbt) RBT.rbt
  val rs_lts_succ_it :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      ('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt ->
        'a -> 'c -> ('d -> bool) -> ('b * 'a -> 'd -> 'd) -> 'd -> 'd
  val rs_lts_connect_it :
    'a Orderings.linorder -> 'b Orderings.linorder -> 'c Orderings.linorder ->
      ('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt ->
        ('a, unit) RBT.rbt ->
          ('c, unit) RBT.rbt ->
            'a -> ('d -> bool) -> ('b * 'c -> 'd -> 'd) -> 'd -> 'd
  val rs_lts_succ_label_it :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      ('a, ('b, ('a, unit) RBT.rbt) RBT.rbt) RBT.rbt ->
        'a -> ('c -> bool) -> ('b * 'a -> 'c -> 'c) -> 'c -> 'c
end = struct

let rec rs_lts_add _A _B
  = (fun v w va l ->
      (match RBT.lookup _A l v
        with None ->
          RBT.insert _A v
            (RBTMapImpl.g_sng_rm_basic_ops _B w
              (RBTSetImpl.g_sng_dflt_basic_oops_rm_basic_ops _A va))
            l
        | Some m2 ->
          (match RBT.lookup _B m2 w
            with None ->
              RBT.insert _A v
                (RBT.insert _B w
                  (RBTSetImpl.g_sng_dflt_basic_oops_rm_basic_ops _A va) m2)
                l
            | Some s3 ->
              RBT.insert _A v
                (RBT.insert _B w (RBTSetImpl.ins_rm_basic_ops _A va s3) m2)
                l)));;

let rec rs_lts_empty _A _B = RBT.empty _A;;

let rec rs_lts_filter_it _A _B _C
  = LTSByMap.ltsbm_filter_it (RBTMapImpl.iteratei_map_op_list_it_rm_ops _A)
      (RBTMapImpl.iteratei_map_op_list_it_rm_ops _B)
      (RBTSetImpl.iteratei_set_op_list_it_rs_ops _C);;

let rec rs_lts_image_filter _A _B _C _D
  = LTSGA.ltsga_image_filter (rs_lts_empty _C _D) (rs_lts_add _C _D)
      (rs_lts_filter_it _A _B _A);;

let rec rs_lts_image _A _B _C _D
  = LTSGA.ltsga_image (rs_lts_image_filter _A _B _C _D);;

let rec rs_lts_succ_it _A _B
  = (fun m1 v _ ->
      (match RBT.lookup _A m1 v
        with None -> SetIteratorOperations.set_iterator_emp
        | Some m2 ->
          SetIteratorOperations.map_iterator_product
            (RBTMapImpl.iteratei_map_op_list_it_rm_ops _B m2)
            (RBTSetImpl.iteratei_set_op_list_it_rs_ops _A)));;

let rec rs_lts_connect_it _A _B _C
  = (fun m1 sa si v ->
      (match RBT.lookup _A m1 v with None -> (fun _ _ sigma_0 -> sigma_0)
        | Some m2 ->
          SetIteratorOperations.map_iterator_product
            (SetIteratorOperations.set_iterator_image_filter
              (fun a ->
                (if not (RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops _A
                          (RBTSetImpl.g_inter_dflt_basic_oops_rm_basic_ops _A
                            (Product_Type.snd a) sa))
                  then Some a else None))
              (RBTMapImpl.iteratei_map_op_list_it_rm_ops _B m2))
            (fun _ -> RBTSetImpl.iteratei_set_op_list_it_rs_ops _C si)));;

let rec rs_lts_succ_label_it _A _B
  = (fun m1 v ->
      (match RBT.lookup _A m1 v
        with None -> SetIteratorOperations.set_iterator_emp
        | Some m2 ->
          SetIteratorOperations.map_iterator_product
            (RBTMapImpl.iteratei_map_op_list_it_rm_ops _B m2)
            (RBTSetImpl.iteratei_set_op_list_it_rs_ops _A)));;

end;; (*struct RBT_LTSImpl*)

module Product_Lexorder : sig
  val linorder_prod :
    'a Orderings.linorder -> 'b Orderings.linorder ->
      ('a * 'b) Orderings.linorder
end = struct

let rec less_eq_prod _A _B
  (x1, y1) (x2, y2) =
    Orderings.less _A x1 x2 ||
      Orderings.less_eq _A x1 x2 && Orderings.less_eq _B y1 y2;;

let rec less_prod _A _B
  (x1, y1) (x2, y2) =
    Orderings.less _A x1 x2 ||
      Orderings.less_eq _A x1 x2 && Orderings.less _B y1 y2;;

let rec ord_prod _A _B =
  ({Orderings.less_eq = less_eq_prod _A _B; Orderings.less = less_prod _A _B} :
    ('a * 'b) Orderings.ord);;

let rec preorder_prod _A _B =
  ({Orderings.ord_preorder =
      (ord_prod _A.Orderings.ord_preorder _B.Orderings.ord_preorder)}
    : ('a * 'b) Orderings.preorder);;

let rec order_prod _A _B =
  ({Orderings.preorder_order =
      (preorder_prod _A.Orderings.preorder_order _B.Orderings.preorder_order)}
    : ('a * 'b) Orderings.order);;

let rec linorder_prod _A _B =
  ({Orderings.order_linorder =
      (order_prod _A.Orderings.order_linorder _B.Orderings.order_linorder)}
    : ('a * 'b) Orderings.linorder);;

end;; (*struct Product_Lexorder*)

module While_Combinator : sig
  val whilea : ('a -> bool) -> ('a -> 'a) -> 'a -> 'a
end = struct

let rec whilea b c s = (if b s then whilea b c (c s) else s);;

end;; (*struct While_Combinator*)

module NFAByLTS_Interval : sig
  val product_iterator :
    ('a -> ('b -> bool) -> (('c * 'c) * 'a -> 'b -> 'b) -> 'b -> 'b) ->
      ('d ->
        'c * 'c -> ('b -> bool) -> (('c * 'c) * 'd -> 'b -> 'b) -> 'b -> 'b) ->
        'a * 'd ->
          ('b -> bool) ->
            ((('c * 'c) * ('c * 'c)) * ('a * 'd) -> 'b -> 'b) -> 'b -> 'b
  val tri_union_iterator :
    ('a -> ('b -> bool) -> (('c * 'c) * 'a -> 'b -> 'b) -> 'b -> 'b) ->
      ('a -> ('b -> bool) -> (('c * 'c) * 'a -> 'b -> 'b) -> 'b -> 'b) ->
        ('a -> ('b -> bool) -> (('c * 'c) * 'a -> 'b -> 'b) -> 'b -> 'b) ->
          'a -> ('b -> bool) -> (('c * 'c) * 'a -> 'b -> 'b) -> 'b -> 'b
  val nfa_transp : 'a * ('b * ('a * 'a)) -> 'b
  val nfa_initialp : 'a * ('b * ('a * 'a)) -> 'a
  val nfa_acceptingp : 'a * ('b * ('a * 'a)) -> 'a
  val rename_states_impl :
    (('a -> 'b) -> 'c -> 'd) ->
      (('a * ('e * 'a) -> 'b * ('e * 'b)) -> 'f -> 'g) ->
        'c * ('f * ('c * 'c)) -> ('a -> 'b) -> 'd * ('g * ('d * 'd))
end = struct

let rec product_iterator
  it_1 it_2 =
    (fun (q1, q2) ->
      SetIteratorOperations.set_iterator_image
        (fun (a, b) ->
          (let (a1, q1a) = a in (fun (a2, q2a) -> ((a1, a2), (q1a, q2a)))) b)
        (SetIteratorOperations.set_iterator_product (it_1 q1)
          (fun aq -> it_2 q2 (Product_Type.fst aq))));;

let rec tri_union_iterator
  it_1 it_2 it_3 =
    (fun q ->
      SetIteratorOperations.set_iterator_union (it_1 q)
        (SetIteratorOperations.set_iterator_union (it_2 q) (it_3 q)));;

let rec nfa_transp a = Product_Type.fst (Product_Type.snd a);;

let rec nfa_initialp
  a = Product_Type.fst (Product_Type.snd (Product_Type.snd a));;

let rec nfa_acceptingp
  a = Product_Type.snd (Product_Type.snd (Product_Type.snd a));;

let rec rename_states_gen_impl
  im im2 (q, (d, (i, f))) =
    (fun fa ->
      (im fa q,
        (im2 (fun qaq ->
               (fa (Product_Type.fst qaq),
                 (Product_Type.fst (Product_Type.snd qaq),
                   fa (Product_Type.snd (Product_Type.snd qaq)))))
           d,
          (im fa i, im fa f))));;

let rec rename_states_impl im im2 = rename_states_gen_impl im im2;;

end;; (*struct NFAByLTS_Interval*)

module Forward_Analysis_Impl  = struct

let rec lookup_aux _A v rc = lookup_aux _A v rc;;

let rec rs_gen_S_from_list _A
  l = Lista.foldl (fun s a -> RBTSetImpl.ins_rm_basic_ops _A a s)
        (RBTSetImpl.empty_rm_basic_ops _A ()) l;;

let rec rs_forward_analysis (_A1, _A2) _B _C
  rm = (fun b si rc rma ->
         While_Combinator.whilea
           (fun p ->
             not (RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops _B
                   (Product_Type.fst p)))
           (fun x ->
             (let xa =
                RBTSetImpl.iteratei_set_op_list_it_rs_ops _B
                  (Product_Type.fst x) (fun _ -> true)
                  (fun xa sigma ->
                    (let xb =
                       RBTSetImpl.iteratei_set_op_list_it_rs_ops
                         (Product_Lexorder.linorder_prod _B _B)
                         (Option.the (lookup_aux _B xa rc)) (fun _ -> true)
                         (fun xb sigmaa ->
                           RBTSetImpl.ins_rm_basic_ops _B (Product_Type.fst xb)
                             (RBTSetImpl.ins_rm_basic_ops _B
                               (Product_Type.snd xb) sigmaa))
                         (RBTSetImpl.empty_rm_basic_ops _B ())
                       in
                      (if RBTSetImpl.g_subset_dflt_basic_oops_rm_basic_ops _B xb
                            (Product_Type.snd (Product_Type.snd x))
                        then RBTSetImpl.ins_rm_basic_ops _B xa sigma
                        else sigma)))
                  (RBTSetImpl.empty_rm_basic_ops _B ())
                in
              let xb =
                RBTSetImpl.iteratei_set_op_list_it_rs_ops _B xa (fun _ -> true)
                  (fun xb sigma ->
                    (let xc =
                       RBTSetImpl.iteratei_set_op_list_it_rs_ops
                         (Product_Lexorder.linorder_prod _B _B)
                         (Option.the (lookup_aux _B xb rc)) (fun _ -> true)
                         (fun xc sigmaa ->
                           (let p =
                              Lista.foldl
                                (fun p q ->
                                  ((RBT.insert
                                      (Product_Lexorder.linorder_prod _A2 _A2)
                                      (Fun.id q)
                                      (NFA_set.states_enumerate _A1
(Product_Type.snd (Product_Type.fst p)))
                                      (Product_Type.fst (Product_Type.fst p)),
                                     Arith.suc
                                       (Product_Type.snd (Product_Type.fst p))),
                                    RBTSetImpl.ins_dj_rm_basic_ops _A2
                                      (NFA_set.states_enumerate _A1
(Product_Type.snd (Product_Type.fst p)))
                                      (Product_Type.snd p)))
                                ((RBT.empty
                                    (Product_Lexorder.linorder_prod _A2 _A2),
                                   Arith.zero_nat),
                                  RBTSetImpl.empty_rm_basic_ops _A2 ())
                                (Lista.product
                                  (RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                                    _A2 (Product_Type.fst
  (Product_Type.snd (Product_Type.snd sigmaa))))
                                  (RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                                    _A2 (Product_Type.fst
  (Product_Type.snd
    (Product_Type.snd
      (let nA1 =
         NFAByLTS_Interval.rename_states_impl
           (fun f s ->
             RBTSetImpl.iteratei_set_op_list_it_rs_ops _A2 s (fun _ -> true)
               (fun ba ->
                 RBTSetImpl.ins_rm_basic_ops
                   (Product_Lexorder.linorder_prod _A2 _A2) (f ba))
               (RBTSetImpl.empty_rm_basic_ops
                 (Product_Lexorder.linorder_prod _A2 _A2) ()))
           (RBT_LTSImpl.rs_lts_image _A2 (Product_Lexorder.linorder_prod _C _C)
             (Product_Lexorder.linorder_prod _A2 _A2)
             (Product_Lexorder.linorder_prod _C _C))
           (Option.the (RBT.lookup _B sigma (Product_Type.fst xc)))
           (fun a -> (rm, a))
         in
       let aA2 =
         NFAByLTS_Interval.rename_states_impl
           (fun f s ->
             RBTSetImpl.iteratei_set_op_list_it_rs_ops _A2 s (fun _ -> true)
               (fun ba ->
                 RBTSetImpl.ins_rm_basic_ops
                   (Product_Lexorder.linorder_prod _A2 _A2) (f ba))
               (RBTSetImpl.empty_rm_basic_ops
                 (Product_Lexorder.linorder_prod _A2 _A2) ()))
           (RBT_LTSImpl.rs_lts_image _A2 (Product_Lexorder.linorder_prod _C _C)
             (Product_Lexorder.linorder_prod _A2 _A2)
             (Product_Lexorder.linorder_prod _C _C))
           (Option.the (RBT.lookup _B sigma (Product_Type.snd xc)))
           (fun a -> (b, a))
         in
       let p =
         Lista.foldl
           (fun p q ->
             ((RBT.insert (Product_Lexorder.linorder_prod _A2 _A2) (Fun.id q)
                 (NFA_set.states_enumerate _A1
                   (Product_Type.snd (Product_Type.fst p)))
                 (Product_Type.fst (Product_Type.fst p)),
                Arith.suc (Product_Type.snd (Product_Type.fst p))),
               RBTSetImpl.ins_dj_rm_basic_ops _A2
                 (NFA_set.states_enumerate _A1
                   (Product_Type.snd (Product_Type.fst p)))
                 (Product_Type.snd p)))
           ((RBT.empty (Product_Lexorder.linorder_prod _A2 _A2),
              Arith.zero_nat),
             RBTSetImpl.empty_rm_basic_ops _A2 ())
           (if not (RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops
                     (Product_Lexorder.linorder_prod _A2 _A2)
                     (RBTSetImpl.g_inter_dflt_basic_oops_rm_basic_ops
                       (Product_Lexorder.linorder_prod _A2 _A2)
                       (NFAByLTS_Interval.nfa_initialp nA1)
                       (NFAByLTS_Interval.nfa_acceptingp nA1)))
             then RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                    (Product_Lexorder.linorder_prod _A2 _A2)
                    (NFAByLTS_Interval.nfa_initialp nA1) @
                    RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                      (Product_Lexorder.linorder_prod _A2 _A2)
                      (NFAByLTS_Interval.nfa_initialp aA2)
             else RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                    (Product_Lexorder.linorder_prod _A2 _A2)
                    (NFAByLTS_Interval.nfa_initialp nA1))
         in
       let pa =
         Workset.worklist (fun _ -> true)
           (fun pa q ->
             (let r =
                Option.the
                  (RBT.lookup (Product_Lexorder.linorder_prod _A2 _A2)
                    (Product_Type.fst (Product_Type.fst pa)) (Fun.id q))
                in
               (if RBTSetImpl.memb_rm_basic_ops _A2 r
                     (Product_Type.fst (Product_Type.snd pa))
                 then (pa, [])
                 else (let paa =
                         NFAByLTS_Interval.tri_union_iterator
                           (RBT_LTSImpl.rs_lts_succ_label_it
                             (Product_Lexorder.linorder_prod _A2 _A2)
                             (Product_Lexorder.linorder_prod _C _C)
                             (NFAByLTS_Interval.nfa_transp nA1))
                           (RBT_LTSImpl.rs_lts_succ_label_it
                             (Product_Lexorder.linorder_prod _A2 _A2)
                             (Product_Lexorder.linorder_prod _C _C)
                             (NFAByLTS_Interval.nfa_transp aA2))
                           (RBT_LTSImpl.rs_lts_connect_it
                             (Product_Lexorder.linorder_prod _A2 _A2)
                             (Product_Lexorder.linorder_prod _C _C)
                             (Product_Lexorder.linorder_prod _A2 _A2)
                             (NFAByLTS_Interval.nfa_transp nA1)
                             (NFAByLTS_Interval.nfa_acceptingp nA1)
                             (NFAByLTS_Interval.nfa_initialp aA2))
                           q (fun _ -> true)
                           (fun pb paa ->
                             (if Interval.nempI
                                   _C.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
                                   (Product_Type.fst pb)
                               then (let r_opt =
                                       RBT.lookup
 (Product_Lexorder.linorder_prod _A2 _A2)
 (Product_Type.fst (Product_Type.fst paa)) (Fun.id (Product_Type.snd pb))
                                       in
                                     let pba =
                                       (if Option.is_none r_opt
 then (let ra =
         NFA_set.states_enumerate _A1 (Product_Type.snd (Product_Type.fst paa))
         in
        ((RBT.insert (Product_Lexorder.linorder_prod _A2 _A2)
            (Fun.id (Product_Type.snd pb)) ra
            (Product_Type.fst (Product_Type.fst paa)),
           Arith.suc (Product_Type.snd (Product_Type.fst paa))),
          ra))
 else (Product_Type.fst paa, Option.the r_opt))
                                       in
                                      (Product_Type.fst pba,
(RBT_LTSImpl.rs_lts_add _A2 (Product_Lexorder.linorder_prod _C _C) r
   (Product_Type.fst pb) (Product_Type.snd pba)
   (Product_Type.fst (Product_Type.snd paa)),
  Product_Type.snd pb :: Product_Type.snd (Product_Type.snd paa))))
                               else paa))
                           (Product_Type.fst pa,
                             (Product_Type.fst
                                (Product_Type.snd (Product_Type.snd pa)),
                               []))
                         in
                        ((Product_Type.fst paa,
                           (RBTSetImpl.ins_dj_rm_basic_ops _A2 r
                              (Product_Type.fst (Product_Type.snd pa)),
                             (Product_Type.fst (Product_Type.snd paa),
                               (Product_Type.fst
                                  (Product_Type.snd
                                    (Product_Type.snd (Product_Type.snd pa))),
                                 (if RBTSetImpl.memb_rm_basic_ops
                                       (Product_Lexorder.linorder_prod _A2 _A2)
                                       q (NFAByLTS_Interval.nfa_acceptingp aA2)
                                   then RBTSetImpl.ins_dj_rm_basic_ops _A2 r
  (Product_Type.snd (Product_Type.snd (Product_Type.snd (Product_Type.snd pa))))
                                   else Product_Type.snd
  (Product_Type.snd (Product_Type.snd (Product_Type.snd pa)))))))),
                          Product_Type.snd (Product_Type.snd paa))))))
           ((Product_Type.fst p,
              (RBTSetImpl.empty_rm_basic_ops _A2 (),
                (RBT_LTSImpl.rs_lts_empty _A2
                   (Product_Lexorder.linorder_prod _C _C),
                  (Product_Type.snd p, RBTSetImpl.empty_rm_basic_ops _A2 ())))),
             (if not (RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops
                       (Product_Lexorder.linorder_prod _A2 _A2)
                       (RBTSetImpl.g_inter_dflt_basic_oops_rm_basic_ops
                         (Product_Lexorder.linorder_prod _A2 _A2)
                         (NFAByLTS_Interval.nfa_initialp nA1)
                         (NFAByLTS_Interval.nfa_acceptingp nA1)))
               then RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                      (Product_Lexorder.linorder_prod _A2 _A2)
                      (NFAByLTS_Interval.nfa_initialp nA1) @
                      RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                        (Product_Lexorder.linorder_prod _A2 _A2)
                        (NFAByLTS_Interval.nfa_initialp aA2)
               else RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                      (Product_Lexorder.linorder_prod _A2 _A2)
                      (NFAByLTS_Interval.nfa_initialp nA1)))
         in
        Product_Type.snd (Product_Type.fst pa)))))))
                              in
                            let pa =
                              Workset.worklist (fun _ -> true)
                                (fun pa q ->
                                  (let r =
                                     Option.the
                                       (RBT.lookup
 (Product_Lexorder.linorder_prod _A2 _A2)
 (Product_Type.fst (Product_Type.fst pa)) (Fun.id q))
                                     in
                                    (if RBTSetImpl.memb_rm_basic_ops _A2 r
  (Product_Type.fst (Product_Type.snd pa))
                                      then (pa, [])
                                      else (let paa =
      NFAByLTS_Interval.product_iterator
        (RBT_LTSImpl.rs_lts_succ_label_it _A2
          (Product_Lexorder.linorder_prod _C _C)
          (Product_Type.fst (Product_Type.snd sigmaa)))
        (RBT_LTSImpl.rs_lts_succ_it _A2 (Product_Lexorder.linorder_prod _C _C)
          (Product_Type.fst
            (Product_Type.snd
              (let nA1 =
                 NFAByLTS_Interval.rename_states_impl
                   (fun f s ->
                     RBTSetImpl.iteratei_set_op_list_it_rs_ops _A2 s
                       (fun _ -> true)
                       (fun ba ->
                         RBTSetImpl.ins_rm_basic_ops
                           (Product_Lexorder.linorder_prod _A2 _A2) (f ba))
                       (RBTSetImpl.empty_rm_basic_ops
                         (Product_Lexorder.linorder_prod _A2 _A2) ()))
                   (RBT_LTSImpl.rs_lts_image _A2
                     (Product_Lexorder.linorder_prod _C _C)
                     (Product_Lexorder.linorder_prod _A2 _A2)
                     (Product_Lexorder.linorder_prod _C _C))
                   (Option.the (RBT.lookup _B sigma (Product_Type.fst xc)))
                   (fun a -> (rm, a))
                 in
               let aA2 =
                 NFAByLTS_Interval.rename_states_impl
                   (fun f s ->
                     RBTSetImpl.iteratei_set_op_list_it_rs_ops _A2 s
                       (fun _ -> true)
                       (fun ba ->
                         RBTSetImpl.ins_rm_basic_ops
                           (Product_Lexorder.linorder_prod _A2 _A2) (f ba))
                       (RBTSetImpl.empty_rm_basic_ops
                         (Product_Lexorder.linorder_prod _A2 _A2) ()))
                   (RBT_LTSImpl.rs_lts_image _A2
                     (Product_Lexorder.linorder_prod _C _C)
                     (Product_Lexorder.linorder_prod _A2 _A2)
                     (Product_Lexorder.linorder_prod _C _C))
                   (Option.the (RBT.lookup _B sigma (Product_Type.snd xc)))
                   (fun a -> (b, a))
                 in
               let pb =
                 Lista.foldl
                   (fun pb qa ->
                     ((RBT.insert (Product_Lexorder.linorder_prod _A2 _A2)
                         (Fun.id qa)
                         (NFA_set.states_enumerate _A1
                           (Product_Type.snd (Product_Type.fst pb)))
                         (Product_Type.fst (Product_Type.fst pb)),
                        Arith.suc (Product_Type.snd (Product_Type.fst pb))),
                       RBTSetImpl.ins_dj_rm_basic_ops _A2
                         (NFA_set.states_enumerate _A1
                           (Product_Type.snd (Product_Type.fst pb)))
                         (Product_Type.snd pb)))
                   ((RBT.empty (Product_Lexorder.linorder_prod _A2 _A2),
                      Arith.zero_nat),
                     RBTSetImpl.empty_rm_basic_ops _A2 ())
                   (if not (RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops
                             (Product_Lexorder.linorder_prod _A2 _A2)
                             (RBTSetImpl.g_inter_dflt_basic_oops_rm_basic_ops
                               (Product_Lexorder.linorder_prod _A2 _A2)
                               (NFAByLTS_Interval.nfa_initialp nA1)
                               (NFAByLTS_Interval.nfa_acceptingp nA1)))
                     then RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                            (Product_Lexorder.linorder_prod _A2 _A2)
                            (NFAByLTS_Interval.nfa_initialp nA1) @
                            RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                              (Product_Lexorder.linorder_prod _A2 _A2)
                              (NFAByLTS_Interval.nfa_initialp aA2)
                     else RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                            (Product_Lexorder.linorder_prod _A2 _A2)
                            (NFAByLTS_Interval.nfa_initialp nA1))
                 in
               let pc =
                 Workset.worklist (fun _ -> true)
                   (fun pc qa ->
                     (let ra =
                        Option.the
                          (RBT.lookup (Product_Lexorder.linorder_prod _A2 _A2)
                            (Product_Type.fst (Product_Type.fst pc))
                            (Fun.id qa))
                        in
                       (if RBTSetImpl.memb_rm_basic_ops _A2 ra
                             (Product_Type.fst (Product_Type.snd pc))
                         then (pc, [])
                         else (let paa =
                                 NFAByLTS_Interval.tri_union_iterator
                                   (RBT_LTSImpl.rs_lts_succ_label_it
                                     (Product_Lexorder.linorder_prod _A2 _A2)
                                     (Product_Lexorder.linorder_prod _C _C)
                                     (NFAByLTS_Interval.nfa_transp nA1))
                                   (RBT_LTSImpl.rs_lts_succ_label_it
                                     (Product_Lexorder.linorder_prod _A2 _A2)
                                     (Product_Lexorder.linorder_prod _C _C)
                                     (NFAByLTS_Interval.nfa_transp aA2))
                                   (RBT_LTSImpl.rs_lts_connect_it
                                     (Product_Lexorder.linorder_prod _A2 _A2)
                                     (Product_Lexorder.linorder_prod _C _C)
                                     (Product_Lexorder.linorder_prod _A2 _A2)
                                     (NFAByLTS_Interval.nfa_transp nA1)
                                     (NFAByLTS_Interval.nfa_acceptingp nA1)
                                     (NFAByLTS_Interval.nfa_initialp aA2))
                                   qa (fun _ -> true)
                                   (fun pd paa ->
                                     (if Interval.nempI
   _C.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
   (Product_Type.fst pd)
                                       then (let r_opt =
       RBT.lookup (Product_Lexorder.linorder_prod _A2 _A2)
         (Product_Type.fst (Product_Type.fst paa))
         (Fun.id (Product_Type.snd pd))
       in
     let pba =
       (if Option.is_none r_opt
         then (let rb =
                 NFA_set.states_enumerate _A1
                   (Product_Type.snd (Product_Type.fst paa))
                 in
                ((RBT.insert (Product_Lexorder.linorder_prod _A2 _A2)
                    (Fun.id (Product_Type.snd pd)) rb
                    (Product_Type.fst (Product_Type.fst paa)),
                   Arith.suc (Product_Type.snd (Product_Type.fst paa))),
                  rb))
         else (Product_Type.fst paa, Option.the r_opt))
       in
      (Product_Type.fst pba,
        (RBT_LTSImpl.rs_lts_add _A2 (Product_Lexorder.linorder_prod _C _C) ra
           (Product_Type.fst pd) (Product_Type.snd pba)
           (Product_Type.fst (Product_Type.snd paa)),
          Product_Type.snd pd :: Product_Type.snd (Product_Type.snd paa))))
                                       else paa))
                                   (Product_Type.fst pc,
                                     (Product_Type.fst
(Product_Type.snd (Product_Type.snd pc)),
                                       []))
                                 in
                                ((Product_Type.fst paa,
                                   (RBTSetImpl.ins_dj_rm_basic_ops _A2 ra
                                      (Product_Type.fst (Product_Type.snd pc)),
                                     (Product_Type.fst (Product_Type.snd paa),
                                       (Product_Type.fst
  (Product_Type.snd (Product_Type.snd (Product_Type.snd pc))),
 (if RBTSetImpl.memb_rm_basic_ops (Product_Lexorder.linorder_prod _A2 _A2) qa
       (NFAByLTS_Interval.nfa_acceptingp aA2)
   then RBTSetImpl.ins_dj_rm_basic_ops _A2 ra
          (Product_Type.snd
            (Product_Type.snd (Product_Type.snd (Product_Type.snd pc))))
   else Product_Type.snd
          (Product_Type.snd (Product_Type.snd (Product_Type.snd pc)))))))),
                                  Product_Type.snd (Product_Type.snd paa))))))
                   ((Product_Type.fst pb,
                      (RBTSetImpl.empty_rm_basic_ops _A2 (),
                        (RBT_LTSImpl.rs_lts_empty _A2
                           (Product_Lexorder.linorder_prod _C _C),
                          (Product_Type.snd pb,
                            RBTSetImpl.empty_rm_basic_ops _A2 ())))),
                     (if not (RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops
                               (Product_Lexorder.linorder_prod _A2 _A2)
                               (RBTSetImpl.g_inter_dflt_basic_oops_rm_basic_ops
                                 (Product_Lexorder.linorder_prod _A2 _A2)
                                 (NFAByLTS_Interval.nfa_initialp nA1)
                                 (NFAByLTS_Interval.nfa_acceptingp nA1)))
                       then RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                              (Product_Lexorder.linorder_prod _A2 _A2)
                              (NFAByLTS_Interval.nfa_initialp nA1) @
                              RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                                (Product_Lexorder.linorder_prod _A2 _A2)
                                (NFAByLTS_Interval.nfa_initialp aA2)
                       else RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                              (Product_Lexorder.linorder_prod _A2 _A2)
                              (NFAByLTS_Interval.nfa_initialp nA1)))
                 in
                Product_Type.snd (Product_Type.fst pc)))))
        q (fun _ -> true)
        (fun pb paa ->
          (if Interval.nempI
                _C.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
                (Interval.intersectI
                  _C.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
                  _C.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
                  (Product_Type.fst (Product_Type.fst pb))
                  (Product_Type.snd (Product_Type.fst pb)))
            then (let r_opt =
                    RBT.lookup (Product_Lexorder.linorder_prod _A2 _A2)
                      (Product_Type.fst (Product_Type.fst paa))
                      (Fun.id (Product_Type.snd pb))
                    in
                  let pba =
                    (if Option.is_none r_opt
                      then (let ra =
                              NFA_set.states_enumerate _A1
                                (Product_Type.snd (Product_Type.fst paa))
                              in
                             ((RBT.insert
                                 (Product_Lexorder.linorder_prod _A2 _A2)
                                 (Fun.id (Product_Type.snd pb)) ra
                                 (Product_Type.fst (Product_Type.fst paa)),
                                Arith.suc
                                  (Product_Type.snd (Product_Type.fst paa))),
                               ra))
                      else (Product_Type.fst paa, Option.the r_opt))
                    in
                   (Product_Type.fst pba,
                     (RBT_LTSImpl.rs_lts_add _A2
                        (Product_Lexorder.linorder_prod _C _C) r
                        (Interval.intersectI
                          _C.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
                          _C.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
                          (Product_Type.fst (Product_Type.fst pb))
                          (Product_Type.snd (Product_Type.fst pb)))
                        (Product_Type.snd pba)
                        (Product_Type.fst (Product_Type.snd paa)),
                       Product_Type.snd pb ::
                         Product_Type.snd (Product_Type.snd paa))))
            else paa))
        (Product_Type.fst pa,
          (Product_Type.fst (Product_Type.snd (Product_Type.snd pa)), []))
      in
     ((Product_Type.fst paa,
        (RBTSetImpl.ins_dj_rm_basic_ops _A2 r
           (Product_Type.fst (Product_Type.snd pa)),
          (Product_Type.fst (Product_Type.snd paa),
            (Product_Type.fst
               (Product_Type.snd (Product_Type.snd (Product_Type.snd pa))),
              (if RBTSetImpl.memb_rm_basic_ops _A2 (Product_Type.fst q)
                    (Product_Type.snd
                      (Product_Type.snd (Product_Type.snd sigmaa))) &&
                    RBTSetImpl.memb_rm_basic_ops _A2 (Product_Type.snd q)
                      (Product_Type.snd
                        (Product_Type.snd
                          (Product_Type.snd
                            (let nA1 =
                               NFAByLTS_Interval.rename_states_impl
                                 (fun f s ->
                                   RBTSetImpl.iteratei_set_op_list_it_rs_ops _A2
                                     s (fun _ -> true)
                                     (fun ba ->
                                       RBTSetImpl.ins_rm_basic_ops
 (Product_Lexorder.linorder_prod _A2 _A2) (f ba))
                                     (RBTSetImpl.empty_rm_basic_ops
                                       (Product_Lexorder.linorder_prod _A2 _A2)
                                       ()))
                                 (RBT_LTSImpl.rs_lts_image _A2
                                   (Product_Lexorder.linorder_prod _C _C)
                                   (Product_Lexorder.linorder_prod _A2 _A2)
                                   (Product_Lexorder.linorder_prod _C _C))
                                 (Option.the
                                   (RBT.lookup _B sigma (Product_Type.fst xc)))
                                 (fun a -> (rm, a))
                               in
                             let aA2 =
                               NFAByLTS_Interval.rename_states_impl
                                 (fun f s ->
                                   RBTSetImpl.iteratei_set_op_list_it_rs_ops _A2
                                     s (fun _ -> true)
                                     (fun ba ->
                                       RBTSetImpl.ins_rm_basic_ops
 (Product_Lexorder.linorder_prod _A2 _A2) (f ba))
                                     (RBTSetImpl.empty_rm_basic_ops
                                       (Product_Lexorder.linorder_prod _A2 _A2)
                                       ()))
                                 (RBT_LTSImpl.rs_lts_image _A2
                                   (Product_Lexorder.linorder_prod _C _C)
                                   (Product_Lexorder.linorder_prod _A2 _A2)
                                   (Product_Lexorder.linorder_prod _C _C))
                                 (Option.the
                                   (RBT.lookup _B sigma (Product_Type.snd xc)))
                                 (fun a -> (b, a))
                               in
                             let pb =
                               Lista.foldl
                                 (fun pb qa ->
                                   ((RBT.insert
                                       (Product_Lexorder.linorder_prod _A2 _A2)
                                       (Fun.id qa)
                                       (NFA_set.states_enumerate _A1
 (Product_Type.snd (Product_Type.fst pb)))
                                       (Product_Type.fst (Product_Type.fst pb)),
                                      Arith.suc
(Product_Type.snd (Product_Type.fst pb))),
                                     RBTSetImpl.ins_dj_rm_basic_ops _A2
                                       (NFA_set.states_enumerate _A1
 (Product_Type.snd (Product_Type.fst pb)))
                                       (Product_Type.snd pb)))
                                 ((RBT.empty
                                     (Product_Lexorder.linorder_prod _A2 _A2),
                                    Arith.zero_nat),
                                   RBTSetImpl.empty_rm_basic_ops _A2 ())
                                 (if not (RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops
   (Product_Lexorder.linorder_prod _A2 _A2)
   (RBTSetImpl.g_inter_dflt_basic_oops_rm_basic_ops
     (Product_Lexorder.linorder_prod _A2 _A2)
     (NFAByLTS_Interval.nfa_initialp nA1)
     (NFAByLTS_Interval.nfa_acceptingp nA1)))
                                   then RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
  (Product_Lexorder.linorder_prod _A2 _A2)
  (NFAByLTS_Interval.nfa_initialp nA1) @
  RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
    (Product_Lexorder.linorder_prod _A2 _A2)
    (NFAByLTS_Interval.nfa_initialp aA2)
                                   else RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
  (Product_Lexorder.linorder_prod _A2 _A2) (NFAByLTS_Interval.nfa_initialp nA1))
                               in
                             let pc =
                               Workset.worklist (fun _ -> true)
                                 (fun pc qa ->
                                   (let ra =
                                      Option.the
(RBT.lookup (Product_Lexorder.linorder_prod _A2 _A2)
  (Product_Type.fst (Product_Type.fst pc)) (Fun.id qa))
                                      in
                                     (if RBTSetImpl.memb_rm_basic_ops _A2 ra
   (Product_Type.fst (Product_Type.snd pc))
                                       then (pc, [])
                                       else (let pab =
       NFAByLTS_Interval.tri_union_iterator
         (RBT_LTSImpl.rs_lts_succ_label_it
           (Product_Lexorder.linorder_prod _A2 _A2)
           (Product_Lexorder.linorder_prod _C _C)
           (NFAByLTS_Interval.nfa_transp nA1))
         (RBT_LTSImpl.rs_lts_succ_label_it
           (Product_Lexorder.linorder_prod _A2 _A2)
           (Product_Lexorder.linorder_prod _C _C)
           (NFAByLTS_Interval.nfa_transp aA2))
         (RBT_LTSImpl.rs_lts_connect_it (Product_Lexorder.linorder_prod _A2 _A2)
           (Product_Lexorder.linorder_prod _C _C)
           (Product_Lexorder.linorder_prod _A2 _A2)
           (NFAByLTS_Interval.nfa_transp nA1)
           (NFAByLTS_Interval.nfa_acceptingp nA1)
           (NFAByLTS_Interval.nfa_initialp aA2))
         qa (fun _ -> true)
         (fun pd pab ->
           (if Interval.nempI
                 _C.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
                 (Product_Type.fst pd)
             then (let r_opt =
                     RBT.lookup (Product_Lexorder.linorder_prod _A2 _A2)
                       (Product_Type.fst (Product_Type.fst pab))
                       (Fun.id (Product_Type.snd pd))
                     in
                   let pba =
                     (if Option.is_none r_opt
                       then (let rb =
                               NFA_set.states_enumerate _A1
                                 (Product_Type.snd (Product_Type.fst pab))
                               in
                              ((RBT.insert
                                  (Product_Lexorder.linorder_prod _A2 _A2)
                                  (Fun.id (Product_Type.snd pd)) rb
                                  (Product_Type.fst (Product_Type.fst pab)),
                                 Arith.suc
                                   (Product_Type.snd (Product_Type.fst pab))),
                                rb))
                       else (Product_Type.fst pab, Option.the r_opt))
                     in
                    (Product_Type.fst pba,
                      (RBT_LTSImpl.rs_lts_add _A2
                         (Product_Lexorder.linorder_prod _C _C) ra
                         (Product_Type.fst pd) (Product_Type.snd pba)
                         (Product_Type.fst (Product_Type.snd pab)),
                        Product_Type.snd pd ::
                          Product_Type.snd (Product_Type.snd pab))))
             else pab))
         (Product_Type.fst pc,
           (Product_Type.fst (Product_Type.snd (Product_Type.snd pc)), []))
       in
      ((Product_Type.fst pab,
         (RBTSetImpl.ins_dj_rm_basic_ops _A2 ra
            (Product_Type.fst (Product_Type.snd pc)),
           (Product_Type.fst (Product_Type.snd pab),
             (Product_Type.fst
                (Product_Type.snd (Product_Type.snd (Product_Type.snd pc))),
               (if RBTSetImpl.memb_rm_basic_ops
                     (Product_Lexorder.linorder_prod _A2 _A2) qa
                     (NFAByLTS_Interval.nfa_acceptingp aA2)
                 then RBTSetImpl.ins_dj_rm_basic_ops _A2 ra
                        (Product_Type.snd
                          (Product_Type.snd
                            (Product_Type.snd (Product_Type.snd pc))))
                 else Product_Type.snd
                        (Product_Type.snd
                          (Product_Type.snd (Product_Type.snd pc)))))))),
        Product_Type.snd (Product_Type.snd pab))))))
                                 ((Product_Type.fst pb,
                                    (RBTSetImpl.empty_rm_basic_ops _A2 (),
                                      (RBT_LTSImpl.rs_lts_empty _A2
 (Product_Lexorder.linorder_prod _C _C),
(Product_Type.snd pb, RBTSetImpl.empty_rm_basic_ops _A2 ())))),
                                   (if not
 (RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops
   (Product_Lexorder.linorder_prod _A2 _A2)
   (RBTSetImpl.g_inter_dflt_basic_oops_rm_basic_ops
     (Product_Lexorder.linorder_prod _A2 _A2)
     (NFAByLTS_Interval.nfa_initialp nA1)
     (NFAByLTS_Interval.nfa_acceptingp nA1)))
                                     then RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
    (Product_Lexorder.linorder_prod _A2 _A2)
    (NFAByLTS_Interval.nfa_initialp nA1) @
    RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
      (Product_Lexorder.linorder_prod _A2 _A2)
      (NFAByLTS_Interval.nfa_initialp aA2)
                                     else RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
    (Product_Lexorder.linorder_prod _A2 _A2)
    (NFAByLTS_Interval.nfa_initialp nA1)))
                               in
                              Product_Type.snd (Product_Type.fst pc)))))
                then RBTSetImpl.ins_dj_rm_basic_ops _A2 r
                       (Product_Type.snd
                         (Product_Type.snd
                           (Product_Type.snd (Product_Type.snd pa))))
                else Product_Type.snd
                       (Product_Type.snd
                         (Product_Type.snd (Product_Type.snd pa)))))))),
       Product_Type.snd (Product_Type.snd paa))))))
                                ((Product_Type.fst p,
                                   (RBTSetImpl.empty_rm_basic_ops _A2 (),
                                     (RBT_LTSImpl.rs_lts_empty _A2
(Product_Lexorder.linorder_prod _C _C),
                                       (Product_Type.snd p,
 RBTSetImpl.empty_rm_basic_ops _A2 ())))),
                                  Lista.product
                                    (RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                                      _A2 (Product_Type.fst
    (Product_Type.snd (Product_Type.snd sigmaa))))
                                    (RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                                      _A2 (Product_Type.fst
    (Product_Type.snd
      (Product_Type.snd
        (let nA1 =
           NFAByLTS_Interval.rename_states_impl
             (fun f s ->
               RBTSetImpl.iteratei_set_op_list_it_rs_ops _A2 s (fun _ -> true)
                 (fun ba ->
                   RBTSetImpl.ins_rm_basic_ops
                     (Product_Lexorder.linorder_prod _A2 _A2) (f ba))
                 (RBTSetImpl.empty_rm_basic_ops
                   (Product_Lexorder.linorder_prod _A2 _A2) ()))
             (RBT_LTSImpl.rs_lts_image _A2
               (Product_Lexorder.linorder_prod _C _C)
               (Product_Lexorder.linorder_prod _A2 _A2)
               (Product_Lexorder.linorder_prod _C _C))
             (Option.the (RBT.lookup _B sigma (Product_Type.fst xc)))
             (fun a -> (rm, a))
           in
         let aA2 =
           NFAByLTS_Interval.rename_states_impl
             (fun f s ->
               RBTSetImpl.iteratei_set_op_list_it_rs_ops _A2 s (fun _ -> true)
                 (fun ba ->
                   RBTSetImpl.ins_rm_basic_ops
                     (Product_Lexorder.linorder_prod _A2 _A2) (f ba))
                 (RBTSetImpl.empty_rm_basic_ops
                   (Product_Lexorder.linorder_prod _A2 _A2) ()))
             (RBT_LTSImpl.rs_lts_image _A2
               (Product_Lexorder.linorder_prod _C _C)
               (Product_Lexorder.linorder_prod _A2 _A2)
               (Product_Lexorder.linorder_prod _C _C))
             (Option.the (RBT.lookup _B sigma (Product_Type.snd xc)))
             (fun a -> (b, a))
           in
         let pa =
           Lista.foldl
             (fun pa q ->
               ((RBT.insert (Product_Lexorder.linorder_prod _A2 _A2) (Fun.id q)
                   (NFA_set.states_enumerate _A1
                     (Product_Type.snd (Product_Type.fst pa)))
                   (Product_Type.fst (Product_Type.fst pa)),
                  Arith.suc (Product_Type.snd (Product_Type.fst pa))),
                 RBTSetImpl.ins_dj_rm_basic_ops _A2
                   (NFA_set.states_enumerate _A1
                     (Product_Type.snd (Product_Type.fst pa)))
                   (Product_Type.snd pa)))
             ((RBT.empty (Product_Lexorder.linorder_prod _A2 _A2),
                Arith.zero_nat),
               RBTSetImpl.empty_rm_basic_ops _A2 ())
             (if not (RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops
                       (Product_Lexorder.linorder_prod _A2 _A2)
                       (RBTSetImpl.g_inter_dflt_basic_oops_rm_basic_ops
                         (Product_Lexorder.linorder_prod _A2 _A2)
                         (NFAByLTS_Interval.nfa_initialp nA1)
                         (NFAByLTS_Interval.nfa_acceptingp nA1)))
               then RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                      (Product_Lexorder.linorder_prod _A2 _A2)
                      (NFAByLTS_Interval.nfa_initialp nA1) @
                      RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                        (Product_Lexorder.linorder_prod _A2 _A2)
                        (NFAByLTS_Interval.nfa_initialp aA2)
               else RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                      (Product_Lexorder.linorder_prod _A2 _A2)
                      (NFAByLTS_Interval.nfa_initialp nA1))
           in
         let pb =
           Workset.worklist (fun _ -> true)
             (fun pb q ->
               (let r =
                  Option.the
                    (RBT.lookup (Product_Lexorder.linorder_prod _A2 _A2)
                      (Product_Type.fst (Product_Type.fst pb)) (Fun.id q))
                  in
                 (if RBTSetImpl.memb_rm_basic_ops _A2 r
                       (Product_Type.fst (Product_Type.snd pb))
                   then (pb, [])
                   else (let paa =
                           NFAByLTS_Interval.tri_union_iterator
                             (RBT_LTSImpl.rs_lts_succ_label_it
                               (Product_Lexorder.linorder_prod _A2 _A2)
                               (Product_Lexorder.linorder_prod _C _C)
                               (NFAByLTS_Interval.nfa_transp nA1))
                             (RBT_LTSImpl.rs_lts_succ_label_it
                               (Product_Lexorder.linorder_prod _A2 _A2)
                               (Product_Lexorder.linorder_prod _C _C)
                               (NFAByLTS_Interval.nfa_transp aA2))
                             (RBT_LTSImpl.rs_lts_connect_it
                               (Product_Lexorder.linorder_prod _A2 _A2)
                               (Product_Lexorder.linorder_prod _C _C)
                               (Product_Lexorder.linorder_prod _A2 _A2)
                               (NFAByLTS_Interval.nfa_transp nA1)
                               (NFAByLTS_Interval.nfa_acceptingp nA1)
                               (NFAByLTS_Interval.nfa_initialp aA2))
                             q (fun _ -> true)
                             (fun pc paa ->
                               (if Interval.nempI
                                     _C.Orderings.order_linorder.Orderings.preorder_order.Orderings.ord_preorder
                                     (Product_Type.fst pc)
                                 then (let r_opt =
 RBT.lookup (Product_Lexorder.linorder_prod _A2 _A2)
   (Product_Type.fst (Product_Type.fst paa)) (Fun.id (Product_Type.snd pc))
 in
                                       let pba =
 (if Option.is_none r_opt
   then (let ra =
           NFA_set.states_enumerate _A1
             (Product_Type.snd (Product_Type.fst paa))
           in
          ((RBT.insert (Product_Lexorder.linorder_prod _A2 _A2)
              (Fun.id (Product_Type.snd pc)) ra
              (Product_Type.fst (Product_Type.fst paa)),
             Arith.suc (Product_Type.snd (Product_Type.fst paa))),
            ra))
   else (Product_Type.fst paa, Option.the r_opt))
 in
(Product_Type.fst pba,
  (RBT_LTSImpl.rs_lts_add _A2 (Product_Lexorder.linorder_prod _C _C) r
     (Product_Type.fst pc) (Product_Type.snd pba)
     (Product_Type.fst (Product_Type.snd paa)),
    Product_Type.snd pc :: Product_Type.snd (Product_Type.snd paa))))
                                 else paa))
                             (Product_Type.fst pb,
                               (Product_Type.fst
                                  (Product_Type.snd (Product_Type.snd pb)),
                                 []))
                           in
                          ((Product_Type.fst paa,
                             (RBTSetImpl.ins_dj_rm_basic_ops _A2 r
                                (Product_Type.fst (Product_Type.snd pb)),
                               (Product_Type.fst (Product_Type.snd paa),
                                 (Product_Type.fst
                                    (Product_Type.snd
                                      (Product_Type.snd (Product_Type.snd pb))),
                                   (if RBTSetImpl.memb_rm_basic_ops
 (Product_Lexorder.linorder_prod _A2 _A2) q
 (NFAByLTS_Interval.nfa_acceptingp aA2)
                                     then RBTSetImpl.ins_dj_rm_basic_ops _A2 r
    (Product_Type.snd
      (Product_Type.snd (Product_Type.snd (Product_Type.snd pb))))
                                     else Product_Type.snd
    (Product_Type.snd (Product_Type.snd (Product_Type.snd pb)))))))),
                            Product_Type.snd (Product_Type.snd paa))))))
             ((Product_Type.fst pa,
                (RBTSetImpl.empty_rm_basic_ops _A2 (),
                  (RBT_LTSImpl.rs_lts_empty _A2
                     (Product_Lexorder.linorder_prod _C _C),
                    (Product_Type.snd pa,
                      RBTSetImpl.empty_rm_basic_ops _A2 ())))),
               (if not (RBTSetImpl.g_isEmpty_dflt_basic_oops_rm_basic_ops
                         (Product_Lexorder.linorder_prod _A2 _A2)
                         (RBTSetImpl.g_inter_dflt_basic_oops_rm_basic_ops
                           (Product_Lexorder.linorder_prod _A2 _A2)
                           (NFAByLTS_Interval.nfa_initialp nA1)
                           (NFAByLTS_Interval.nfa_acceptingp nA1)))
                 then RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                        (Product_Lexorder.linorder_prod _A2 _A2)
                        (NFAByLTS_Interval.nfa_initialp nA1) @
                        RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                          (Product_Lexorder.linorder_prod _A2 _A2)
                          (NFAByLTS_Interval.nfa_initialp aA2)
                 else RBTSetImpl.g_to_list_dflt_basic_oops_rm_basic_ops
                        (Product_Lexorder.linorder_prod _A2 _A2)
                        (NFAByLTS_Interval.nfa_initialp nA1)))
           in
          Product_Type.snd (Product_Type.fst pb)))))))
                              in
                             Product_Type.snd (Product_Type.fst pa)))
                         (Option.the (RBT.lookup _B sigma xb))
                       in
                      RBT.insert _B xb xc sigma))
                  (Product_Type.fst (Product_Type.snd x))
                in
               (RBTSetImpl.g_diff_dflt_basic_oops_rm_basic_ops _B
                  (Product_Type.fst x) xa,
                 (xb, RBTSetImpl.g_union_dflt_basic_oops_rm_basic_ops _B
                        (Product_Type.snd (Product_Type.snd x)) xa))))
           (si, (rma, RBTSetImpl.empty_rm_basic_ops _B ())));;

let rec rs_gen_rc_from_list _A
  l = Lista.foldl
        (fun _ a ->
          RBT.insert _A (Product_Type.fst a) (Product_Type.snd a)
            (RBT.empty _A))
        l;;

let rec rs_gen_rm_from_list _A (_B1, _B2) _C
  l = Lista.foldl
        (fun _ a ->
          RBT.insert _A (Product_Type.fst a) (Product_Type.snd a)
            (RBT.empty _A))
        l;;

end;; (*struct Forward_Analysis_Impl*)
