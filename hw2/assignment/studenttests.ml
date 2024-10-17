open Assert
open X86
open Simulator
open Xor_test
open Add_test
open Sub_test
open Shift_test
open Invalid_test
open Kek

(* You can use this file for additional test cases to help your *)
(* implementation.                                              *)


let provided_tests : suite = [
  Test ("Debug", [
  ]);
  (*Test ("all_the_xor", xor_tests);
  Test ("all_the_add", add_tests);
  Test ("all_the_sub", sub_tests);
  Test ("all_the_shift", shift_tests);
  Test ("all_the_invalid", invalid_tests);
  Test ("all_the_kek", kek_tests);*)
] 
