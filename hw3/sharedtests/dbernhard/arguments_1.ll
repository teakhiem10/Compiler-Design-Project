
@gint = global i64 10

define i64 @sum(i64 %x1, i64 %x2, i64 %x3, i64 %x4, i64 %x5, i64 %x6, i64 %x7, i64 %x8, i64 %x9, i64 %x10) {
  %1 = add i64 %x1, %x2
  %2 = add i64 %1, %x3
  %3 = add i64 %2, %x4
  %4 = add i64 %3, %x5
  %5 = add i64 %4, %x6
  %6 = add i64 %5, %x7
  %7 = add i64 %6, %x8
  %8 = add i64 %7, %x9
  %9 = add i64 %8, %x10
  ret i64 %9
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = load i64, i64* @gint
  %2 = call i64 @sum(i64 %1,i64 %1,i64 %1,i64 %1,i64 %1,i64 %1,i64 %1,i64 %1,i64 %1,i64 %1)
  
  ret i64 %2
}
