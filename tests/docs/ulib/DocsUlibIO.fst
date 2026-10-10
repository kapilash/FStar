module DocsUlibIO

(* Examples from the documentation of FStar.Printf, FStar.All, FStar.IO,
   FStar.Dyn, FStar.IFC and FStar.Error *)

let greeting : string = FStar.Printf.sprintf "%s has %d items" "cart" 3

let _ = assert_norm (greeting == "cart has 3 items")

let safe_div (x y: int) : FStar.All.ML int =
  FStar.All.try_with
    (fun () -> if y = 0 then FStar.All.failwith "division by zero" else x / y)
    (fun _ -> 0)

let counter_demo () : FStar.All.ML int =
  let r = FStar.All.alloc 0 in
  FStar.All.(r := !r + 1);
  FStar.All.(!r)

let hello () : FStar.All.ML unit =
  FStar.IO.print_string (FStar.Printf.sprintf "%ul\n" 42ul)

let packed = FStar.Dyn.mkdyn #int 42

let unpacked () : Dv int = FStar.Dyn.undyn #int packed

let bool_sl : FStar.IFC.sl u#0 =
  FStar.Ghost.hide (FStar.IFC.SemiLattice #bool true (fun x y -> x || y))

let secret : FStar.IFC.lattice_element bool_sl = FStar.Ghost.hide true

let incr (x: FStar.IFC.protected secret int) : FStar.IFC.protected secret int =
  FStar.IFC.map x (fun y -> y + 1)

let safe_head (l: list int) : FStar.Error.optResult string int =
  match l with
  | [] -> FStar.Error.Error "empty list"
  | x :: _ -> FStar.Error.correct x
