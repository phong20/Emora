@message = private constant [17 x i8] c"Hello from LLVM!\00"

declare i32 @puts(ptr)

define i32 @main() {
entry:
  call i32 @puts(ptr @message)
  ret i32 0
}