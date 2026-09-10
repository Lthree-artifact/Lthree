import LeanMLIR.Dialects.LLVM

namespace LeanMLIR.Tests

private def widthParamConstant (w : Nat) :=
  [llvm(w)| {
    ^bb0():
      %0 = llvm.mlir.constant(w : _) : _
      llvm.return %0
  }]

private def widthParamConstant8 :=
  [llvm| {
    ^bb0():
      %0 = llvm.mlir.constant(8 : i8) : i8
      llvm.return %0 : i8
  }]

private def widthParamConstant13 :=
  [llvm| {
    ^bb0():
      %0 = llvm.mlir.constant(13 : i13) : i13
      llvm.return %0 : i13
  }]

example : widthParamConstant 8 = widthParamConstant8 := by
  rfl

example : widthParamConstant 13 = widthParamConstant13 := by
  rfl

/--
info: builtin.module {
  ^bb0():
    %0 = "llvm.mlir.constant"(){value = 8 : i8} : () -> (i8)
    "llvm.return"(%0) : (i8) -> ()
}
-/
#guard_msgs in
#eval Com.printModule (widthParamConstant 8)

end LeanMLIR.Tests
