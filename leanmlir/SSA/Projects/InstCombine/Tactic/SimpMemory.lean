import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

/-- Simp-set for memory-specific InstCombine executable semantics. -/
register_simp_attr simp_memory

/-- Simp-set for unfolding low-level memory store helpers. -/
register_simp_attr simp_memory_store_defs

/-- Simp-set for unfolding low-level memory allocation helpers. -/
register_simp_attr simp_memory_alloca_defs

/-- Simp-set for unfolding low-level GEP arithmetic helpers. -/
register_simp_attr simp_memory_gep_defs
