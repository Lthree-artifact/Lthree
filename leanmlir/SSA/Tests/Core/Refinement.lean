import LeanMLIR.Framework.Refinement
import LeanMLIR.Dialects.LLVM.Basic
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.Tactic

open InstCombine

set_option pp.instances false

variable {w : Nat} (x y : LLVM.m ⟦LLVM.Ty.bitvec w⟧)

-- `simp_denote` simplifies refinement of LLVM dialect bitvectors to refinement
-- of their denotation `LLVM.IntW _`.
example
    (h : @HRefinement.IsRefinedBy
        (ImmediateUBOr (LLVM.IntWUB w))
        (ImmediateUBOr (LLVM.IntWUB w))
        _ x y) :
    x ⊑ y := by
  simpa only [simp_denote] using h

-- `simp_llvm` composes with `simp_denote` on LLVM refinement goals.
example {w : Nat} (x y : LLVM.m ⟦LLVM.Ty.bitvec w⟧)
    (h : @HRefinement.IsRefinedBy
        (ImmediateUBOr (LLVM.IntWUB w))
        (ImmediateUBOr (LLVM.IntWUB w))
        _ x y) :
    x ⊑ y := by
  simpa only [simp_denote, simp_llvm] using h

-- `simp_denote` should still simplify in the presence of *concrete* effects.
example {w : Nat}
    (x : EffectKind.pure.toMonad LLVM.m ⟦LLVM.Ty.bitvec w⟧)
    (y : EffectKind.impure.toMonad LLVM.m ⟦LLVM.Ty.bitvec w⟧)
    (h : @HRefinement.IsRefinedBy
        (ImmediateUBOr (LLVM.IntWUB w))
        (ImmediateUBOr (LLVM.IntWUB w))
        _ (pure x) y) :
    x ⊑ y := by
  simpa only [simp_denote, simp_llvm] using h

-- and for plain bitvectors (without monads)
example {w : Nat} (x y : ⟦LLVM.Ty.bitvec w⟧)
    (h : @HRefinement.IsRefinedBy
        (ImmediateUBOr (LLVM.IntW w))
        (ImmediateUBOr (LLVM.IntW w))
        _ x y) :
    x ⊑ y := by
  simpa only [simp_denote, simp_llvm] using h
