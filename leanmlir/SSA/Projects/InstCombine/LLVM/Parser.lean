import LeanMLIR.MLIRSyntax.Parser
import LeanMLIR.Dialects.LLVM.Syntax
import Init.Data.Repr

open InstCombine
def parseComFromFile (fileName : String) :
    IO (Option (Σ (Γ' : Ctxt (MetaLLVM 0).Ty) (eff : EffectKind) (ty : List (MetaLLVM 0).Ty),
      Com (MetaLLVM 0) Γ' eff ty)) :=
  Com.parseFromFile (MetaLLVM 0) fileName
