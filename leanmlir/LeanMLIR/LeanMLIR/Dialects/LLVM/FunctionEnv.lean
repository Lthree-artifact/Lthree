import LeanMLIR.Dialects.LLVM.FunctionEnvCore
import LeanMLIR.Dialects.LLVM.CalleeAttribute

namespace InstCombine

open LLVM

namespace LLVMMemory

/--
Evaluate a named function via compile-time instance resolution.
`name` should be a literal at call sites (the normal `llvm.call @foo` case).
-/
def denoteFueled
    (fuel : Nat) (name : String)
    {argTys : List LLVM.Ty} {retTy : LLVM.Ty}
    [LLVMCallee σ name argTys retTy]
    (args : HVector TySemVal argTys) (s : σ)
    : ImmediateUBOr (TySemVal retTy × σ) :=
  match fuel with
  | 0 => .value (.poison, s)
  | fuel + 1 =>
      let fd := LLVMCallee.funcDef (σ := σ) (name := name) (argTys := argTys) (retTy := retTy)
      if hArg : argTys = fd.argTys then
        if hRet : fd.retTy = retTy then
          let args' : HVector TySemVal fd.argTys := by
            simpa [hArg] using args
          match fd.denote fuel args' s with
          | .none => .none
          | .some (v, s') =>
              let v' : TySemVal retTy := by
                simpa [hRet] using v
              .value (v', s')
        else
          .value (.poison, s)
      else
        .value (.poison, s)

/--
Backward-compatible runtime lookup semantics using an explicit `FunctionEnv`.
Missing/mismatched calls and fuel exhaustion yield poison.
-/
def denoteFueledInEnv
    (fuel : Nat) (env : FunctionEnv σ) (name : String)
    {argTys : List LLVM.Ty} {retTy : LLVM.Ty}
    (args : HVector TySemVal argTys) (s : σ)
    : ImmediateUBOr (TySemVal retTy × σ) :=
  match fuel with
  | 0 => .value (.poison, s)
  | fuel + 1 =>
      match env[name]? with
      | none => .value (.poison, s)
      | some fd =>
          if hArg : argTys = fd.argTys then
            if hRet : fd.retTy = retTy then
              let args' : HVector TySemVal fd.argTys := by
                simpa [hArg] using args
              match fd.denote fuel args' s with
              | .none => .none
              | .some (v, s') =>
                  let v' : TySemVal retTy := by
                    simpa [hRet] using v
                  .value (v', s')
            else
              .value (.poison, s)
          else
            .value (.poison, s)

end LLVMMemory

end InstCombine
