import SSA.Projects.InstCombine.MemoryRefinement
import SSA.Projects.InstCombine.Tactic
import SSA.Projects.InstCombine.Tactic.SimpMemory

/--
Common simplification pass for memory-sensitive InstCombine refinement goals.
This packages the repeated memory-specific refinement rewrites on top of
`simp_peephole`.
-/
macro "simp_memory_peephole" : tactic =>
  `(tactic|(
      first
      | rw [funext_iff (α := Ctxt.Valuation _)]
      | change ∀ (_ : Ctxt.Valuation _), _
      | skip

      simp only [DialectHRefinement.IsRefinedBy, InstCombine.instRefinement]
      simp (config := { failIfUnchanged := false }) only
        [Expr.denote_castPureToEff, simp_denote, simp_memory]
      simp (config := { failIfUnchanged := false }) [simp_denote, simp_memory, LLVM.const?, Ctxt.Var.zero_eq_last]
    ))

/-- Unfold low-level memory store helpers at the current goal. -/
macro "simp_memory_store" : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) [simp_memory_store_defs])

/-- Unfold low-level memory allocation helpers at the current goal. -/
macro "simp_memory_alloca" : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) [simp_memory_alloca_defs])

/-- Unfold low-level GEP arithmetic helpers at the current goal. -/
macro "simp_memory_gep" : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) [simp_memory_gep_defs])
