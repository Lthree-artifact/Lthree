-- import SSA.Projects.InstCombine.Refinement
-- import SSA.Projects.InstCombine.Tactic
-- import SSA.Projects.InstCombine.TacticAuto
-- import SSA.Projects.InstCombine.AliveStatements
-- import LeanMLIR.Dialects.LLVM.Syntax
-- import SSA.Projects.InstCombine.ForLean

-- -- open MLIR AST
-- -- open InstCombine (LLVM)

-- -- /--
-- -- 验证 transformations 的步骤:
-- -- 1. 定义 Source 程序 (`src`)
-- -- 2. 定义 Target 程序 (`tgt`)
-- -- 3. 声明定理 `src ⊑ tgt` (Refinement)
-- -- 4. 使用 `simp_peephole` 简化目标
-- -- 5. 使用 `bv_decide` (或其他位向量求解策略) 完成证明
-- -- -/

-- -- -- Source: x + x
-- -- def add_self_src (w : Nat) :=
-- -- [llvm(w)| {
-- -- ^bb0(%x : _):
-- --   %0 = llvm.add %x, %x
-- --   llvm.return %0
-- -- }]

-- -- -- Target: x << 1
-- -- def add_self_tgt (w : Nat) :=
-- -- [llvm(w)| {
-- -- ^bb0(%x : _):
-- --   %0 = llvm.mlir.constant(1)
-- --   %1 = llvm.shl %x, %0
-- --   llvm.return %1
-- -- }]

-- def add_self_src :=
-- [llvm(8)| {
-- ^bb0(%x : i8):
--   %0 = llvm.add %x, %x : i8
--   llvm.return %0 : i8
-- }]

-- def add_self_tgt :=
-- [llvm(8)| {
-- ^bb0(%x : i8):
--   %0 = llvm.mlir.constant(1 : i8) : i8
--   %1 = llvm.shl %x, %0 : i8
--   llvm.return %1 : i8
-- }]

-- theorem add_self_correct : add_self_src ⊑ add_self_tgt := by
--   unfold add_self_src add_self_tgt
--   simp_alive_peephole
--   simp_alive_undef
--   simp_alive_ops
--   simp_alive_case_bash
--   simp_alive_split
--   all_goals bv_auto

-- -- theorem add_self_correct (w : Nat) : add_self_src w ⊑ add_self_tgt w := by
-- --   unfold add_self_src add_self_tgt
-- --   simp_peephole
-- --   apply bv_AddSub_1156



-- -- 另一个示例: (x ^ y) ^ y -> x
-- def xor_cancel_src (w : Nat) :=
-- [llvm(w)| {
-- ^bb0(%x : _, %y : _):
--   %0 = llvm.xor %x, %y
--   %1 = llvm.xor %0, %y
--   llvm.return %1
-- }]

-- def xor_cancel_tgt (w : Nat) :=
-- [llvm(w)| {
-- ^bb0(%x : _, %y : _):
--   llvm.return %x
-- }]

-- -- theorem xor_cancel_correct (w : Nat) : xor_cancel_src w ⊑ xor_cancel_tgt w := by
-- --   unfold xor_cancel_src xor_cancel_tgt
-- --   simp_peephole
-- --   simp_alive_undef
-- --   -- 3. 将 LLVM 操作简化为 BitVec 操作
-- --   simp_alive_ops

-- --   simp_alive_case_bash
-- --   -- x ^ y ^ y = x using associativity and nilpotence
-- --   simp [BitVec.xor_assoc, BitVec.xor_comm, BitVec.xor_self, BitVec.xor_zero]


-- -- 源程序 (Source): (x - x) ^ y
-- def sub_xor_src (w : Nat) :=
-- [llvm(w)| {
-- ^bb0(%x : _, %y : _):
--   %0 = llvm.sub %x, %x   -- 计算 x - x (结果应为 0)
--   %1 = llvm.xor %0, %y   -- 计算 0 ^ y (结果应为 y)
--   llvm.return %1
-- }]

-- -- 目标程序 (Target): 直接返回 y
-- def sub_xor_tgt (w : Nat) :=
-- [llvm(w)| {
-- ^bb0(%x : _, %y : _):
--   llvm.return %y
-- }]

-- theorem sub_xor_correct (w : Nat) : sub_xor_src w ⊑ sub_xor_tgt w := by
--   -- 1. 展开定义
--   unfold sub_xor_src sub_xor_tgt

--   -- 2. 使用论文提到的策略简化 SSA 结构
--   simp_peephole at *

--   -- 3. 将 LLVM 操作转化为 BitVec 操作 (OpDenote)
--   simp_alive_ops
--   simp_alive_undef
--   simp_alive_case_bash
--   simp_alive_split

--   -- 4. 关键修复：引入变量到上下文中
--   -- 这一步将 "%x" 这种 IR 概念转化为 "x : BitVec w" 这种数学概念
--   intros

--   -- 5. 使用位向量决策程序求解
--   -- 论文中提到使用的是 alive_auto，但在现代版本通常对应 bv_decide
--   bv_decide


-- -- 1. 定义 Source: (x - x) ^ y
-- -- 逻辑：x - x = 0, 0 ^ y = y
-- def sub_xor_src (w : Nat) :=
-- [llvm(w)| {
-- ^bb0(%x : _, %y : _):
--   %0 = llvm.sub %x, %x
--   %1 = llvm.xor %0, %y
--   llvm.return %1
-- }]

-- -- 2. 定义 Target: y
-- def sub_xor_tgt (w : Nat) :=
-- [llvm(w)| {
-- ^bb0(%x : _, %y : _):
--   llvm.return %y
-- }]



-- theorem sub_xor_correct (w : Nat) : sub_xor_src w ⊑ sub_xor_tgt w := by
--   -- unfold sub_xor_src sub_xor_tgt
--   -- simp_alive_peephole
--   -- simp_alive_undef
--   -- simp_alive_ops
--   -- simp_alive_case_bash
--   -- simp_alive_split
--   -- all_goals bv_auto
--   -- simp_peephole at *
--   -- simp_alive_ops
--   -- simp_alive_undef
--   -- simp_alive_case_bash
--   -- simp_alive_split
--   -- intros
--   -- bv_decide
--   -- unfold sub_xor_src sub_xor_tgt
--   -- simp_alive_peephole
--   -- alive_auto


--   induction t with
--   | leaf =>
--       simp [mirror]
--   | node lft v rgt ih_l ih_r =>
--       simp [mirror, ih_l, ih_r]
