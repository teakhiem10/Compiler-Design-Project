open Assert
open Ast

(* These tests are provided by you -- they will be graded manually *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let provided_tests : suite = 
  let ty_A = TRef (RStruct "A") in 
  let ty_B = TRef (RStruct "B") in 
  let str_A = [{fieldName="x"; ftyp=TInt}] in 
  let str_B = List.append str_A [{fieldName="y"; ftyp=TBool}] in 
  let ab_ctxt = List.fold_left (fun c -> fun (id, fields) -> Tctxt.add_struct c id fields) Tctxt.empty [("A", str_A); ("B", str_B)] in [
  GradedTest ("student typecheck_exp tests", 10, [
    "CNull", assert_eq (Typechecker.typecheck_exp Tctxt.empty (no_loc (CNull RString))) (TNullRef RString);
    "CInt", assert_eq (Typechecker.typecheck_exp Tctxt.empty (no_loc (CInt 0L))) (TInt);
    "CBool", assert_eq (Typechecker.typecheck_exp Tctxt.empty (no_loc (CBool false))) (TBool);
    "CStr", assert_eq (Typechecker.typecheck_exp Tctxt.empty (no_loc (CStr "abc"))) (TRef RString);
    "Id_success", assert_eq (Typechecker.typecheck_exp (Tctxt.add_global Tctxt.empty "x" TInt) (no_loc (Id "x"))) (TInt);
    "Id_fail", assert_eq (try (let _ = Typechecker.typecheck_exp Tctxt.empty (no_loc (Id "x")) in 0) with _ -> 1) 1;
    "CArr_simple", assert_eq (Typechecker.typecheck_exp (Tctxt.empty) (no_loc (CArr (TInt, [no_loc (CInt 1L); no_loc (CInt 2L)])))) (TRef (RArray TInt));
    "CArr_inheritance", assert_eq (Typechecker.typecheck_exp (ab_ctxt) (no_loc (CArr (ty_A, [no_loc (CStruct ("A", [("x", no_loc (CInt 1L))])); no_loc (CStruct ("A", [("x", no_loc (CInt 1L))]))])))) (TRef (RArray ty_A));
    "CArr_inheritance_fail", assert_eq (try (let _ = Typechecker.typecheck_exp (ab_ctxt) (no_loc (CArr (ty_B, [no_loc (CStruct ("A", [("x", no_loc (CInt 1L))])); no_loc (CStruct ("A", [("x", no_loc (CInt 1L))]))]))) in 0) with _ -> 1) 1;
  ]);
] 
