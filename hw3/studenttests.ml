open Assert
open X86
open Ll
open Backend

(* These tests are provided by you -- they will not be graded  *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let begin_block = {insns = [("%1",Alloca Void)]; term = ("end",Br "test")}
let lbl_block : (lbl * block) list = [("labl1",{insns = [("%2",Alloca Void)]; term = ("end",Br "test")} )]
let result_layout2 :layout= [("%0", Ind3 (Lit (-8L), Rbp));
                            ("%1", Ind3 (Lit (-16L), Rbp))]
let result_layout3 :layout= [("%0", Ind3 (Lit (-8L), Rbp));
                            ("%1", Ind3 (Lit (-16L), Rbp));
                            ("%2", Ind3 (Lit (-24L), Rbp))]

let stack_tests =
  [("stack1", assert_eqf (fun () -> stack_layout ["%0"] ({insns = []; term = ("", Br "begin")}, []) ) [("%0", Ind3 (Lit (-8L), Rbp))]);
   ("stack2", assert_eqf (fun () -> stack_layout ["%0"] (begin_block, []) ) result_layout2);
   ("stack3", assert_eqf (fun () -> stack_layout ["%0"] (begin_block, lbl_block) ) result_layout3);]
let provided_tests : suite = [
  GradedTest("Task1 tests", 5, stack_tests)
]
