open Assert
open Hellocaml

(* These tests are provided by you -- they will NOT be graded *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)


(*Test Cases for 4-4*)
(* Test 1: Const *)
let test1 = interpret [] e1  (* Expected: 6L *)


(* Test 2: Multiple variables *)
let test2 = interpret ctxt2 e3  (* Expected: -63L *)

(* Test 3: Duplicate *)
let ctxt3 = [("x", 5L); ("x", 2L)]  (* Context with duplicate bindings *)
let test3 = interpret ctxt3 e2  (* Expected: 6L *)

(* Test 4: Nested*)
let e4 = Mult(Add(Var "x", Var "y"), Const 3L)
let test4 = interpret ctxt2 e4  (* Expected: 27L *)

(* Test 5: Double Negation *)
let e5 = Neg(Neg(Const 5L))
let test5 = interpret [] e5  (* Expected: -5L *)

(* TEST CASES FOR 4-5*)

(* Test 1: Adding zero *)
let t1 = Add(Const 0L, Var "x")
let test6 = optimize t1  (* Expected: Var "x" *)
(* Test 2: Multiplying a variable with zero *)

let t2 = Mult(Var "x", Const 0L)
let test7 = optimize t2  (* Expected: Const 0L *)

(* Test 3: Multiplying a variable with one *)
let t3 = Mult(Var "x", Const 1L)
let test8 = optimize t3  (* Expected: Var "x" *)

(* Test 4: Negation of negation *)
let t4 = Neg(Neg(Var "x"))
let test9 = optimize t4  (* Expected: Var "x" *)

(* Test 5: Negation of a constant *)
let t5 = Neg(Const 5L)
let test10 = optimize t5  (* Expected: Const (-5L) *)
(* Test 6: Combination *)
let t6 = Add(Const 3L, Mult(Const 0L, Var "x"))  (* 3 + (0 * x) *)
let test11 = optimize t6  (* Expected: Const 3L *)

(* Test 7: Nested expression with multiple operations *)
let t7= Add(Mult(Const 1L, Var "x"), Add(Const 0L, Mult(Var "y", Const 1L)))
let test12 = optimize t7  (* Expected: Add(Var "x", Var "y") *)

(* Test 8: More complex case with negation and multiplication *)
let t8 = Mult(Neg(Const 2L), Neg(Const 3L))  (* (-2) * (-3) *)
let test13 = optimize t8  (* Expected: Const 6L *)






let provided_tests : suite = [
  Test ("Student-Provided Tests For Problem 1-3", [
    ("case1", assert_eqf (fun () -> 42) prob3_ans );
    ("case2", assert_eqf (fun () -> 25) (prob3_case2 17) );
    ("case3", assert_eqf (fun () -> prob3_case3) 64);
  ]);

  Test ("Student-Provided Tests For Problem 4-4", [
    ("interpret1", assert_eqf (fun () -> test1) (6L));
    ("interpret2", assert_eqf (fun () -> test2) (-63L));
    ("interpret3", assert_eqf (fun () -> test3) (6L));
    ("interpret4", assert_eqf (fun () -> test4) (27L));
    ("interpret5", assert_eqf (fun () -> test5) (5L));

  ]); 

  Test ("Student-Provided Tests For Problem 4-5", [
    ("optimize1", assert_eqf (fun () -> test6) (Var "x"));
    ("optimize2", assert_eqf (fun () -> test7) (Const 0L));
    ("optimize3", assert_eqf (fun () -> test8) (Var "x"));
    ("optimize4", assert_eqf (fun () -> test9) (Var "x"));
    ("optimize5", assert_eqf (fun () -> test10) (Const (-5L)));
    ("optimize6", assert_eqf (fun () -> test11) (Const 3L));
    ("optimize7", assert_eqf (fun () -> test12) (Add(Var "x", Var "y")));
    ("optimize8", assert_eqf (fun () -> test13) (Const 6L));
    ("optimize9", assert_eqf (fun () -> optimize (Neg (Add(Var "x", Var "y")))) (Neg (Add(Var "x", Var "y"))));
    ("optimize10", assert_eqf (fun () -> optimize (Neg (Mult(Const 0L, Var "y")))) (Const 0L));
    ("optimize11", assert_eqf (fun () -> optimize (Neg (Neg (Mult(Const 2L, Const 3L))))) (Const 6L));
    ("optimize12", assert_eqf (fun () -> optimize (Add ((Var "x"), (Neg (Var "x"))))) (Const 0L));
    ("optimize13", assert_eqf (fun () -> optimize (Add((Add ((Var "x"), (Neg (Var "x")))), (Const 1L)))) (Const 1L));
    ("optimize14", assert_eqf (fun () -> optimize (Mult((Add (Const 1L, Const 3L)), (Const (-1L))))) (Const (-4L)));
    ("optimize15", assert_eqf (fun () -> optimize (Add(Neg (Var "x"), Neg (Var "y")))) (Neg(Add((Var "x", Var "y")))));
    ("optimize16", assert_eqf (fun () -> optimize (Mult(Neg (Var "x"), Neg (Var "y")))) (Mult(Var "x", Var "y")));



  ]); 
  (* cxt 1 maps "x" to 3L *)
  (* cxt 2 maps "x" to 2L, "y" to 7L *)
  Test ("Student-Provided Tests For Problem 5", [
    ("compile1", assert_eqf (fun () -> compile e1) p1); (* "2 * 3" *)
    ("equal1", assert_eqf (fun () -> interpret ctxt1 e1) (run ctxt1 p1));
    ("compile2", assert_eqf (fun () -> compile e2) [IPushV "x"; IPushC 1L; IAdd]); (* "x + 1" *)
    ("equal1", assert_eqf (fun () -> interpret ctxt1 e2) (run ctxt1 [IPushV "x"; IPushC 1L; IAdd]));
    ("compile3", assert_eqf (fun () -> compile e3) 
      [IPushV "y"; IPushV "x"; IPushC 1L; IAdd; IPushV "x"; IPushC 1L; IAdd; INeg; IMul; IMul]); (* "y * ((x+1) * -(x+1))" *)
    ("equal3", assert_eqf (fun () -> interpret ctxt2 e3) (run ctxt2 [IPushV "y"; IPushV "x"; IPushC 1L; IAdd; IPushV "x"; IPushC 1L; IAdd; INeg; IMul; IMul]));
    ("compile4", assert_eqf (fun () -> compile (Neg(Add(Const 1L, Const 2L)))) [IPushC 1L; IPushC 2L; IAdd; INeg]); (* "-(1 + 2)" *)
    ("equal4", assert_eqf (fun () -> interpret ctxt2 (Neg(Add(Const 1L, Const 2L)))) (run ctxt2 [IPushC 1L; IPushC 2L; IAdd;INeg]));
    ("compile4", assert_eqf (fun () -> compile (Mult((Add((Const 1L), (Const 2L))), (Add((Var "x"), (Const 2L)))))) [IPushC 1L; IPushC 2L; IAdd; IPushV "x"; IPushC 2L; IAdd; IMul]); (* "(1 + 2) * (x + 2)" *)
    ("equal4", assert_eqf (fun () -> interpret ctxt2 (Mult((Add((Const 1L), (Const 2L))), (Add((Var "x"), (Const 2L)))))) (run ctxt2 [IPushC 1L; IPushC 2L; IAdd; IPushV "x"; IPushC 2L; IAdd; IMul]));

 
  ]); 
  
] 



