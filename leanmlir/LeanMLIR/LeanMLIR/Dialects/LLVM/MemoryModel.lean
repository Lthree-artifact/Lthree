import LeanMLIR.Dialects.LLVM.FunctionEnv

namespace InstCombine

open LLVM

namespace LLVMMemory

structure Block where
  sizeBytes : Nat
  bytes : BitVec (8 * sizeBytes)
  initialized : BitVec (8 * sizeBytes)
  deriving Repr

instance : Inhabited Block := ⟨{ sizeBytes := 0, bytes := 0#0, initialized := 0#0 }⟩

/-- Memory model state for LLVM memory-aware execution. -/
structure State where
  nextBlockId : Nat := 0
  blocks : Std.HashMap Nat Block := {}
  deriving Inhabited, Repr

abbrev M := StateT State ImmediateUBOr
abbrev ExecM := ReaderT (FunctionEnv State) M

def throwUB : M α :=
  StateT.lift ImmediateUBOr.immediateUB

def throwUBIf (p : Prop) [Decidable p] : M Unit :=
  if p then throwUB else pure ()

def getIntWOrUB (x : LLVM.IntW w) : M (BitVec w) :=
  match x with
  | .poison => throwUB
  | .value v => pure v

def getIntWUBOrUB (x : LLVM.IntWUB w) : M (BitVec w) :=
  match x with
  | .none => throwUB
  | .some v => getIntWOrUB v

def bytesForWidth (w : Nat) : Nat :=
  max 1 ((w + 7) / 8)

/--
Normalize an index to the pointer-index width (64 in this model), matching the
LangRef rule that GEP indices are sign-extended or truncated to that width.
-/
def gepNormalizeIdx (idx : LLVM.IntWUB w) : LLVM.IntWUB 64 := do
  let idx' ← idx
  pure <| LLVM.sext 64 idx'

/-- Compute the byte offset contributed by a single GEP index. -/
def gepOffset (elemW : Nat) (idx : LLVM.IntWUB w) : LLVM.IntWUB 64 := do
  let idx64 ← gepNormalizeIdx idx
  pure <| LLVM.mul idx64 (LLVM.SemVal.value (BitVec.ofNat 64 (bytesForWidth elemW))) {}

/-- Typed GEP: base pointer plus scaled byte offset. -/
def gep (elemW : Nat) (ptr : PtrValUB) (idx : LLVM.IntWUB w) : PtrValUB := do
  let base ← ptr
  match base with
  | .poison => pure .poison
  | .value v =>
      let off ← gepOffset elemW idx
      match off with
      | .poison => pure .poison
      | .value delta =>
          pure (.value { blockId := v.blockId, offset := v.offset + delta })

def alloca (w : Nat) : M PtrValUB := do
  let s ← get
  let id := s.nextBlockId
  let nb := bytesForWidth w
  set { s with
    nextBlockId := id + 1
    blocks := s.blocks.insert id {
      sizeBytes := nb
      bytes := 0#(8 * nb)
      initialized := 0#(8 * nb)
    }
  }
  pure (.some (.value { blockId := id, offset := 0#64 }))

def getPtrOrUB (p : PtrValUB) : M Ptr :=
  match p with
  | .none => throwUB
  | .some .poison => throwUB
  | .some (.value v) => pure v

def load (ptr : PtrValUB) (w : Nat) : M (LLVM.IntWUB w) := do
  let p ← getPtrOrUB ptr
  let s ← get
  let some b := s.blocks[p.blockId]? | throwUB
  let offsetBytes := p.offset.toNat
  if _h : offsetBytes + bytesForWidth w ≤ b.sizeBytes then
    let startBit := 8 * offsetBytes
    let initSlice := b.initialized.extractLsb' startBit w
    if initSlice = BitVec.allOnes w then
      pure (LLVM.IntWUB.value (b.bytes.extractLsb' startBit w))
    else
      pure (LLVM.IntWUB.poison : LLVM.IntWUB w)
  else
    throwUB

def store (ptr : PtrValUB) (x : LLVM.IntWUB w) : M Unit := do
  let p ← getPtrOrUB ptr
  let v ← getIntWUBOrUB x
  let s ← get
  let some b := s.blocks[p.blockId]? | throwUB
  let offsetBytes := p.offset.toNat
  if _h : offsetBytes + bytesForWidth w ≤ b.sizeBytes then
    let startBit := 8 * offsetBytes
    let vExt : BitVec (8 * b.sizeBytes) :=
      (v.zeroExtend (8 * b.sizeBytes)) <<< startBit
    let mask : BitVec (8 * b.sizeBytes) :=
      ~~~((BitVec.allOnes w).zeroExtend (8 * b.sizeBytes) <<< startBit)
    let bytes' := (b.bytes &&& mask) ||| vExt
    let initUpdate : BitVec (8 * b.sizeBytes) :=
      (BitVec.allOnes w).zeroExtend (8 * b.sizeBytes) <<< startBit
    let initialized' := b.initialized ||| initUpdate
    let b' : Block := { sizeBytes := b.sizeBytes, bytes := bytes', initialized := initialized' }
    set { s with blocks := s.blocks.insert p.blockId b' }
  else
    throwUB

/-- Memory-model dialect layer over `LLVM` with the same op/type language. -/
def LLVMM : Dialect where
  Op := LLVM.Op
  Ty := LLVM.Ty
  m := ExecM

instance : DecidableEq LLVMM.Op := by unfold LLVMM; infer_instance
instance : DecidableEq LLVMM.Ty := by unfold LLVMM; infer_instance

instance : Monad LLVMM.m := by unfold LLVMM ExecM; infer_instance
instance : LawfulMonad LLVMM.m := by unfold LLVMM ExecM; infer_instance

/-- Lift a state-only memory computation into the environment-aware execution monad. -/
def liftState (x : M α) : ExecM α := fun _ => x

@[simp] theorem liftState_run (x : M α) (env : FunctionEnv State) :
    ReaderT.run (liftState x) env = x := rfl

@[simp] theorem liftState_apply (x : M α) (env : FunctionEnv State) :
    liftState x env = x := rfl

instance : DialectSignature LLVMM where
  signature op := DialectSignature.signature (d := LLVM) op

instance : TyDenote LLVMM.Ty := by
  unfold LLVMM
  infer_instance

@[simp]
def Op.denoteVec (o : LLVMM.Op) (args : HVector TyDenote.toType (DialectSignature.sig o)) :
    ((DialectSignature.effectKind o).toMonad LLVMM.m
      (HVector TyDenote.toType <| DialectSignature.returnTypes o)) :=
  match o with
  | .load (.concrete n) => do
      let p : PtrValUB := args.getN 0 (by simp [DialectSignature.sig, signature])
      let x ← liftState (load p n)
      pure [x]ₕ
  | .load (.mvar idx) => nomatch idx
  | .store (.concrete n) => do
      let p : PtrValUB := args.getN 0 (by simp [DialectSignature.sig, signature])
      let x : LLVM.IntWUB n := args.getN 1 (by simp [DialectSignature.sig, signature])
      let _ ← liftState (store p x)
      pure []ₕ
  | .store (.mvar idx) => nomatch idx
  | .alloca (.concrete n) => do
      let p ← liftState (alloca n)
      pure [p]ₕ
  | .alloca (.mvar idx) => nomatch idx
  | .call retTy fnName argTys =>
      fun env => do
        let s ← get
        let semArgs ← StateT.lift (toSemValVecOrUB args)
        let (v, s') ← StateT.lift
          (denoteFueledInEnv defaultFuel env fnName semArgs s)
        set s'
        let v' : TyDenote.toType (β := LLVM.Ty) retTy := fromSemVal (ty := retTy) v
        pure [v']ₕ
  | .assume_ => do
      let cU := args.getN 0 (by simp [DialectSignature.sig, signature])
      let c : LLVM.IntW 1 ← liftState <| StateT.lift (by simpa [DialectSignature.sig, signature] using cU)
      let _ ← liftState <| StateT.lift (_root_.LLVM.assume_ c)
      pure ([]ₕ)
  | .unary w op' =>
      [InstCombine.Op.denote (.unary w op') args]ₕ
  | .binary w op' =>
      [InstCombine.Op.denote (.binary w op') args]ₕ
  | MOp.getelementptr elemW idxW =>
      match elemW, idxW with
      | .concrete elemW, .concrete idxW =>
          let p : PtrValUB := args.getN 0 (by simp [DialectSignature.sig, signature])
          let idx : LLVM.IntWUB idxW := args.getN 1 (by simp [DialectSignature.sig, signature])
          [gep elemW p idx]ₕ
      | .mvar idx, _ =>
          nomatch idx
      | _, .mvar idx =>
          nomatch idx
  | .isPowerOf2 w =>
      [InstCombine.Op.denote (.isPowerOf2 w) args]ₕ
  | .select w =>
      [InstCombine.Op.denote (.select w) args]ₕ
  | .icmp c w =>
      [InstCombine.Op.denote (.icmp c w) args]ₕ
  | .const w val =>
      [InstCombine.Op.denote (.const w val) args]ₕ
  | .constParam w idx =>
      nomatch idx

instance : DialectDenote LLVMM := ⟨
  fun o args _ => Op.denoteVec o args
⟩

def toMemoryMorphism : DialectMorphism LLVM LLVMM where
  mapOp := fun o => o
  mapTy := fun t => t
  preserves_signature := by
    intro op
    have hctxtId : ∀ Γ : Ctxt LLVM.Ty, Ctxt.map id Γ = Γ := by
      intro Γ
      simpa using (Ctxt.map_id (Γ := Γ))
    have hregId : ∀ rs : RegionSignature LLVM.Ty, (id <$> rs) = rs := by
      intro rs
      induction rs with
      | nil =>
          rfl
      | cons a rs ih =>
          rcases a with ⟨Γ, tys⟩
          simpa [Functor.map, RegionSignature.map, hctxtId Γ] using ih
    have hid : ∀ s : Signature LLVM.Ty, (id <$> s) = s := by
      intro s
      cases s with
      | mkEffectful sig regSig returnTypes effectKind =>
          change Signature.mkEffectful (id <$> sig) (id <$> regSig)
            (id <$> returnTypes) effectKind
            = Signature.mkEffectful sig regSig returnTypes effectKind
          simp [hregId regSig]
    simpa using (hid (DialectSignature.signature (d := LLVM) op)).symm

@[simp] theorem toMemoryMorphism_mapOp (o : LLVM.Op) :
    toMemoryMorphism.mapOp o = o := rfl

@[simp] theorem toMemoryMorphism_mapTy (t : LLVM.Ty) :
    toMemoryMorphism.mapTy t = t := rfl

@[simp] theorem Expr_changeDialect_toMemoryMorphism_op
    {Γ : Ctxt LLVM.Ty} {eff : EffectKind} {ty : List LLVM.Ty}
    (e : Expr LLVM Γ eff ty) :
    (Expr.changeDialect toMemoryMorphism e).op = e.op := by
  cases e with
  | mk op ty_eq eff_le args regArgs =>
      cases ty_eq
      simp [Expr.changeDialect, toMemoryMorphism]

@[simp] theorem gep_lift2_add_zero_right (elemW idxW : Nat) (p : PtrValUB) :
    gep elemW p (LLVM.IntWUB.value (0#idxW)) = p := by
  cases p with
  | none =>
      simp [gep, gepOffset, gepNormalizeIdx, LLVM.sext, LLVM.sext?]
  | some v =>
      cases v with
      | poison =>
          simp [gep, gepOffset, gepNormalizeIdx, LLVM.sext, LLVM.sext?, LLVM.mul, LLVM.mul?]
      | value a =>
          have hz : BitVec.signExtend 64 (0#idxW) = (0#64) := by
            apply BitVec.eq_of_toNat_eq
            simp [BitVec.toNat_signExtend]
          simp [gep, gepOffset, gepNormalizeIdx, LLVM.sext, LLVM.sext?, LLVM.mul, LLVM.mul?, hz]

/--
Continuation-level fusion for `getelementptr p, 0` followed by `store/load`.
This is stronger than a bare pointer equality because it rewrites the whole
store/load continuation in one step.
-/
@[simp] theorem gep_zero_store_load_fusion
    (elemW idxW : Nat) (p : PtrValUB) (x : LLVM.IntWUB w)
    (k : LLVM.IntWUB w → M α) :
    (do
      let q := gep elemW p (LLVM.IntWUB.value (0#idxW))
      let _ ← store q x
      let y ← load q w
      k y)
    =
    (do
      let _ ← store p x
      let y ← load p w
      k y) := by
  have hzero :
      gep elemW p (some (LLVM.SemVal.value (0#idxW))) = p := by
    simpa using gep_lift2_add_zero_right (elemW := elemW) (idxW := idxW) (p := p)
  simp [hzero]

/-- Simplify `StateT` binds whose left side is immediate UB. -/
@[simp] theorem lift_immediateUB_bind
    (f : α → M β) :
    (StateT.lift (m := ImmediateUBOr) (σ := State) ImmediateUBOr.immediateUB >>= f) =
      (StateT.lift (m := ImmediateUBOr) (σ := State) ImmediateUBOr.immediateUB : M β) := by
  funext s
  rfl

@[simp] theorem bind_apply (x : M α) (f : α → M β) (s : State) :
    (x >>= f) s = Option.bind (x s) (fun p => f p.1 p.2) := rfl

@[simp] theorem pure_apply (a : α) (s : State) :
    (pure a : M α) s = some (a, s) := rfl

@[simp] theorem get_apply (s : State) :
    (get : M State) s = some (s, s) := rfl

@[simp] theorem set_apply (s' s : State) :
    (set s' : M Unit) s = some ((), s') := rfl

@[simp] theorem lift_apply (x : ImmediateUBOr α) (s : State) :
    (StateT.lift (σ := State) (m := ImmediateUBOr) x : M α) s =
      Option.bind x (fun a => some (a, s)) := rfl

/-- Storing a concrete value and loading from the same pointer yields that value. -/
theorem store_load_roundtrip
    (ptr : PtrValUB) (v : BitVec w)
    (k : LLVM.IntWUB w → M α) :
    (do
      let _ ← store ptr (LLVM.IntWUB.value v)
      let x ← load ptr w
      k x)
    =
    (do
      let _ ← store ptr (LLVM.IntWUB.value v)
      k (LLVM.IntWUB.value v)) := by
  funext s
  cases ptr with
  | none =>
      simp [store, load, getPtrOrUB, getIntWUBOrUB, getIntWOrUB, throwUB,
        ImmediateUBOr.immediateUB]
  | some pv =>
      cases pv with
      | poison =>
          simp [store, load, getPtrOrUB, getIntWUBOrUB, getIntWOrUB, throwUB,
            ImmediateUBOr.immediateUB]
      | value p =>
          cases hblk : s.blocks[p.blockId]? with
          | none =>
              simp [store, load, getPtrOrUB, getIntWUBOrUB, getIntWOrUB, throwUB,
                ImmediateUBOr.immediateUB, hblk]
          | some b =>
              by_cases hbound : p.offset.toNat + bytesForWidth w ≤ b.sizeBytes
              · have hwbits : w ≤ 8 * bytesForWidth w := by
                  unfold bytesForWidth
                  omega
                have hfit : 8 * p.offset.toNat + w ≤ 8 * b.sizeBytes := by
                  omega
                have hslice_v :
                    (((v.zeroExtend (8 * b.sizeBytes)) <<< (8 * p.offset.toNat)).extractLsb'
                      (8 * p.offset.toNat) w) = v := by
                  apply BitVec.eq_of_getLsbD_eq
                  intro i
                  by_cases hi : i < w
                  · have hiN : i < 8 * b.sizeBytes := by omega
                    have hstart : 8 * p.offset.toNat + i < 8 * b.sizeBytes := by omega
                    simp [BitVec.getLsbD_extractLsb', hi, BitVec.getLsbD_shiftLeft, hstart,
                      show ¬8 * p.offset.toNat + i < 8 * p.offset.toNat by omega,
                      BitVec.getLsbD_setWidth, hiN]
                  · have hiw : w ≤ i := Nat.le_of_not_lt hi
                    simp [BitVec.getLsbD_extractLsb', hi, BitVec.getLsbD_of_ge, hiw]
                have hslice_ones :
                    ((((BitVec.allOnes w).zeroExtend (8 * b.sizeBytes)) <<< (8 * p.offset.toNat)).extractLsb'
                      (8 * p.offset.toNat) w) = BitVec.allOnes w := by
                  apply BitVec.eq_of_getLsbD_eq
                  intro i
                  by_cases hi : i < w
                  · have hiN : i < 8 * b.sizeBytes := by omega
                    have hstart : 8 * p.offset.toNat + i < 8 * b.sizeBytes := by omega
                    simp [BitVec.getLsbD_extractLsb', hi, BitVec.getLsbD_shiftLeft, hstart,
                      show ¬8 * p.offset.toNat + i < 8 * p.offset.toNat by omega,
                      BitVec.getLsbD_setWidth, hiN]
                  · have hiw : w ≤ i := Nat.le_of_not_lt hi
                    simp [BitVec.getLsbD_extractLsb', hi, BitVec.getLsbD_of_ge, hiw]
                have hslice_mask_zero :
                    ((~~~(((BitVec.allOnes w).zeroExtend (8 * b.sizeBytes)) <<< (8 * p.offset.toNat))).extractLsb'
                      (8 * p.offset.toNat) w) = (0#w) := by
                  apply BitVec.eq_of_getLsbD_eq
                  intro i
                  by_cases hi : i < w
                  · have hiN : i < 8 * b.sizeBytes := by omega
                    have hstart : 8 * p.offset.toNat + i < 8 * b.sizeBytes := by omega
                    simp [BitVec.getLsbD_extractLsb', hi, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
                      hstart, show ¬8 * p.offset.toNat + i < 8 * p.offset.toNat by omega,
                      BitVec.getLsbD_setWidth, hiN]
                  · have hiw : w ≤ i := Nat.le_of_not_lt hi
                    simp [BitVec.getLsbD_extractLsb', hi, BitVec.getLsbD_of_ge, hiw]
                simp [store, load, getPtrOrUB, getIntWUBOrUB, getIntWOrUB, hblk, hbound,
                  throwUB, BitVec.extractLsb'_or, BitVec.extractLsb'_and,
                  ImmediateUBOr.immediateUB,
                  hslice_v, hslice_ones, hslice_mask_zero]
              · simp [store, load, getPtrOrUB, getIntWUBOrUB, getIntWOrUB, throwUB, hblk, hbound,
                  ImmediateUBOr.immediateUB]

@[simp] theorem LLVM_regSig_nil (op : LLVM.Op) :
    DialectSignature.regSig op = [] := by
  cases op <;> rfl

/-- Evaluate an `Expr LLVM` directly in the executable memory monad. -/
def Expr.denoteWithMemory (e : Expr LLVM Γ eff ty) (V : Γ.Valuation) :
    eff.toMonad LLVMM.m (e.outContext.Valuation) :=
  match e with
  | ⟨op, ty_eq, heff, args, regArgs⟩ => do
      let argsDenote := args.map V
      let regDenote :
          HVector (fun t : Ctxt LLVM.Ty × List LLVM.Ty =>
            t.1.Valuation → EffectKind.impure.toMonad LLVMM.m (HVector TyDenote.toType t.2))
          (DialectSignature.regSig op) := by
            simpa [LLVM_regSig_nil op] using
              (HVector.nil :
                HVector
                  (fun t : Ctxt LLVM.Ty × List LLVM.Ty =>
                    t.1.Valuation → EffectKind.impure.toMonad LLVMM.m (HVector TyDenote.toType t.2))
                  [])
      let val ← EffectKind.liftEffect heff <| DialectDenote.denote (d := LLVMM) op argsDenote regDenote
      pure ((val ++ V).cast (by
        convert (rfl :
          ((DialectSignature.returnTypes op : Ctxt LLVM.Ty) ++ Γ)
            = ((DialectSignature.returnTypes op : Ctxt LLVM.Ty) ++ Γ)) using 1
        simp [Expr.outContext, ty_eq]))

private structure MemoryRuntimeCFGBlock (Γ : Ctxt LLVM.Ty) (retTys : List LLVM.Ty) where
  args : Ctxt LLVM.Ty
  body : CFGBody LLVM (args ++ Γ) .impure retTys

/--
Look up a basic block by name.

STRUCTURAL RECURSION (deliberate): see the note on
`CFGBody.denoteWithMemoryFuelCore` below.  `CFGBlocks` is likewise an inductive
family whose `EffectKind` index is degenerate — every constructor produces
`.impure` — so writing the index as the variable `eff` lets Lean compile this
structurally instead of falling back to `WellFounded.fix`, which the kernel
cannot iota-reduce.  Block lookup sits directly under the fuel loop, so leaving
it well-founded would keep concrete CFG evaluation stuck even once the body
interpreter reduces.
-/
def CFGBlocks.findMemoryBlock? {Γ : Ctxt LLVM.Ty} {eff : EffectKind}
    {retTys : List LLVM.Ty}
    (name : String) : CFGBlocks LLVM Γ eff retTys →
    Option (MemoryRuntimeCFGBlock Γ retTys)
  | .nil => none
  | .cons (.mk blockName args body) blocks =>
      if blockName == name then
        some ⟨args, body⟩
      else
        findMemoryBlock? name blocks
  termination_by structural bs => bs

def CFGTerm.denoteWithMemoryFuelCore {Γcur : Ctxt LLVM.Ty} {retTys : List LLVM.Ty}
    (jump : {Γnext : Ctxt LLVM.Ty} →
      Γnext.Valuation → CFGTarget LLVM Γnext → ExecM (HVector TyDenote.toType retTys))
    (V : Γcur.Valuation) :
    CFGTerm LLVM Γcur retTys → ExecM (HVector TyDenote.toType retTys)
  | .ret vs => pure (vs.map V)
  | .br target => jump V target
  | .condBr (condTy := condTy) cond trueTarget falseTarget =>
      if h : condTy = LLVM.Ty.bitvec 1 then
        let condVal : TyDenote.toType (LLVM.Ty.bitvec 1) := h ▸ V cond
        let condUB : LLVM.IntWUB 1 := condVal
        match condUB with
        | .none => fun _ => throwUB
        | .some .poison => fun _ => throwUB
        | .some (.value c) =>
            if c == 1#1 then
              jump V trueTarget
            else
              jump V falseTarget
      else
        fun _ => throwUB

/--
Interpret the body of one CFG basic block.

STRUCTURAL RECURSION (deliberate): the `EffectKind` index is written as the
variable `eff` rather than the literal `.impure`, and the recursion is pinned
with `termination_by structural`.  Both constructors of `CFGBody` produce
`.impure`, so the index is degenerate and generalising it changes nothing about
which terms are accepted — but Lean's structural-recursion check rejects an
inductive family whose indices are not variables ("its type CFGBody is an
inductive family and indices are not variables"), and would otherwise fall back
to well-founded recursion.  A well-founded compilation goes through
`WellFounded.fix` on an opaque accessibility proof, which the KERNEL cannot
iota-reduce: `decide`/`rfl` then get stuck on any concrete CFG evaluation and
every consumer has to unfold this interpreter with `simp` and its equation
lemmas instead.  Compiled structurally, concrete evaluation reduces in the
kernel.
-/
def CFGBody.denoteWithMemoryFuelCore {Γcur : Ctxt LLVM.Ty} {eff : EffectKind}
    {retTys : List LLVM.Ty}
    (jump : {Γnext : Ctxt LLVM.Ty} →
      Γnext.Valuation → CFGTarget LLVM Γnext → ExecM (HVector TyDenote.toType retTys)) :
    CFGBody LLVM Γcur eff retTys → Γcur.Valuation →
    ExecM (HVector TyDenote.toType retTys)
  | .terminator term, V => CFGTerm.denoteWithMemoryFuelCore jump V term
  | .var e body, V => do
      let V' ← Expr.denoteWithMemory e V
      CFGBody.denoteWithMemoryFuelCore jump body V'
  termination_by structural b => b

def CFGTarget.denoteWithMemoryFuel {Γ Γcur : Ctxt LLVM.Ty} {retTys : List LLVM.Ty}
    (fuel : Nat) (blocks : CFGBlocks LLVM Γ .impure retTys)
    (baseV : Γ.Valuation) (V : Γcur.Valuation) (target : CFGTarget LLVM Γcur) :
    ExecM (HVector TyDenote.toType retTys) :=
  match fuel with
  | 0 => fun _ => throwUB
  | fuel + 1 =>
      match CFGBlocks.findMemoryBlock? target.name blocks with
      | none => fun _ => throwUB
      | some ⟨args, body⟩ =>
          if h : target.argTys = args.toList then
            let argVals : HVector TyDenote.toType args.toList :=
              h ▸ target.args.map V
            let blockV : (args ++ Γ).Valuation :=
              Ctxt.Valuation.cast (by cases args; rfl) (argVals ++ baseV)
            CFGBody.denoteWithMemoryFuelCore
              (fun V target => CFGTarget.denoteWithMemoryFuel fuel blocks baseV V target)
              body blockV
          else
            fun _ => throwUB

def CFGTerm.denoteWithMemoryFuel {Γ Γcur : Ctxt LLVM.Ty} {retTys : List LLVM.Ty}
    (fuel : Nat) (blocks : CFGBlocks LLVM Γ .impure retTys)
    (baseV : Γ.Valuation) (V : Γcur.Valuation) :
    CFGTerm LLVM Γcur retTys → ExecM (HVector TyDenote.toType retTys) :=
  CFGTerm.denoteWithMemoryFuelCore
    (fun V target => CFGTarget.denoteWithMemoryFuel fuel blocks baseV V target) V

def CFGBody.denoteWithMemoryFuel {Γ Γcur : Ctxt LLVM.Ty} {retTys : List LLVM.Ty}
    (fuel : Nat) (blocks : CFGBlocks LLVM Γ .impure retTys)
    (baseV : Γ.Valuation) :
    CFGBody LLVM Γcur .impure retTys → Γcur.Valuation →
    ExecM (HVector TyDenote.toType retTys) :=
  CFGBody.denoteWithMemoryFuelCore
    (fun V target => CFGTarget.denoteWithMemoryFuel fuel blocks baseV V target)

/-- Evaluate a regular `Com LLVM` under the memory-aware `LLVMM` semantics. -/
def Com.denoteWithMemoryCore : Com LLVM Γ eff ty → (Γ.Valuation → eff.toMonad LLVMM.m (HVector TyDenote.toType ty))
  | .rets vs => fun V => pure (vs.map V)
  | .var e body => fun V => Expr.denoteWithMemory e V >>= Com.denoteWithMemoryCore body
  | .cfg _ _ fallback => Com.denoteWithMemoryCore fallback

/--
Evaluate an impure command with a fuel-bounded CFG interpreter.
For `.cfg`, execution starts at the CFG entry block and ignores the fallback.
For non-CFG commands, this agrees with `denoteWithMemoryIn` and ignores fuel.
-/
def Com.denoteWithMemoryFuelIn (env : FunctionEnv State) (fuel : Nat)
    (com : Com LLVM Γ .impure ty) (V : Γ.Valuation)
    (s : State := default) :
    ImmediateUBOr (HVector TyDenote.toType ty × State) :=
  match com with
  | .cfg entry blocks _fallback =>
      let target : CFGTarget LLVM Γ := { name := entry, argTys := [], args := .nil }
      ((CFGTarget.denoteWithMemoryFuel fuel blocks V V target).run env).run s
  | _ =>
      ((Com.denoteWithMemoryCore com V).run env).run s

/-- Evaluate an impure `Com LLVM` under the memory-aware `LLVMM` semantics. -/
def Com.denoteWithMemoryIn (env : FunctionEnv State)
    (com : Com LLVM Γ .impure ty) (V : Γ.Valuation)
    (s : State := default) :
    ImmediateUBOr (HVector TyDenote.toType ty × State) :=
  ((Com.denoteWithMemoryCore com V).run env).run s

@[simp] theorem Com.denoteWithMemoryIn_eq (env : FunctionEnv State)
    (com : Com LLVM Γ .impure ty) (V : Γ.Valuation) (s : State := default) :
    InstCombine.LLVMMemory.Com.denoteWithMemoryIn env com V s
    = ((InstCombine.LLVMMemory.Com.denoteWithMemoryCore com V).run env).run s := by
  rfl

@[simp] theorem Com.denoteWithMemoryFuelIn_eq (env : FunctionEnv State) (fuel : Nat)
    (com : Com LLVM Γ .impure ty) (V : Γ.Valuation) (s : State := default) :
    InstCombine.LLVMMemory.Com.denoteWithMemoryFuelIn env fuel com V s
    =
      match com with
      | .cfg entry blocks _fallback =>
          let target : CFGTarget LLVM Γ := { name := entry, argTys := [], args := .nil }
          ((InstCombine.LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel blocks V V target).run env).run s
      | _ =>
          ((InstCombine.LLVMMemory.Com.denoteWithMemoryCore com V).run env).run s := by
  rfl

/--
Default function-environment selector for memory-aware impure LLVM commands.
Refinement lemmas can override this instance locally to make `llvm.call` resolve
project-specific callees without changing theorem statements.
-/
class DefaultFunctionEnvFor (Γ : Ctxt LLVM.Ty) (ty : List LLVM.Ty) where
  env : FunctionEnv State

/-- Backward-compatible default: no registered functions. -/
instance (priority := 100) instDefaultFunctionEnvFor
    (Γ : Ctxt LLVM.Ty) (ty : List LLVM.Ty) :
    DefaultFunctionEnvFor Γ ty where
  env := ({} : FunctionEnv State)

/-- Resolve the default function environment for memory-aware execution. -/
def defaultFunctionEnv [inst : DefaultFunctionEnvFor Γ ty] : FunctionEnv State :=
  inst.env

@[simp] theorem defaultFunctionEnv_eq_env [inst : DefaultFunctionEnvFor Γ ty] :
    defaultFunctionEnv (Γ := Γ) (ty := ty) = inst.env := by
  rfl

@[simp] theorem defaultFunctionEnv_lookup [inst : DefaultFunctionEnvFor Γ ty] (name : String) :
    (defaultFunctionEnv (Γ := Γ) (ty := ty))[name]? = inst.env[name]? := by
  rfl

/--
Evaluate an impure command under the selected default function environment for
its `(Γ, ty)` index.
-/
def Com.denoteWithDefaultFunctionEnv [DefaultFunctionEnvFor Γ ty]
    (com : Com LLVM Γ .impure ty) (V : Γ.Valuation)
    (s : State := default) :
    ImmediateUBOr (HVector TyDenote.toType ty × State) :=
  Com.denoteWithMemoryIn (env := defaultFunctionEnv (Γ := Γ) (ty := ty)) com V s

def Com.denoteWithDefaultFunctionEnvFuel [DefaultFunctionEnvFor Γ ty]
    (fuel : Nat) (com : Com LLVM Γ .impure ty) (V : Γ.Valuation)
    (s : State := default) :
    ImmediateUBOr (HVector TyDenote.toType ty × State) :=
  Com.denoteWithMemoryFuelIn
    (env := defaultFunctionEnv (Γ := Γ) (ty := ty)) fuel com V s

@[simp] theorem Com.denoteWithDefaultFunctionEnv_eq [DefaultFunctionEnvFor Γ ty]
    (com : Com LLVM Γ .impure ty) (V : Γ.Valuation) (s : State := default) :
    InstCombine.LLVMMemory.Com.denoteWithDefaultFunctionEnv (Γ := Γ) (ty := ty) com V s
    = InstCombine.LLVMMemory.Com.denoteWithMemoryIn
        (InstCombine.LLVMMemory.defaultFunctionEnv (Γ := Γ) (ty := ty))
        com V s := by
  rfl

@[simp] theorem Com.denoteWithDefaultFunctionEnvFuel_eq [DefaultFunctionEnvFor Γ ty]
    (fuel : Nat) (com : Com LLVM Γ .impure ty) (V : Γ.Valuation) (s : State := default) :
    InstCombine.LLVMMemory.Com.denoteWithDefaultFunctionEnvFuel
        (Γ := Γ) (ty := ty) fuel com V s
    = InstCombine.LLVMMemory.Com.denoteWithMemoryFuelIn
        (InstCombine.LLVMMemory.defaultFunctionEnv (Γ := Γ) (ty := ty))
        fuel com V s := by
  rfl

/-- Evaluate an impure `Com LLVM` under memory-aware semantics with an empty function environment. -/
def Com.denoteWithMemory (com : Com LLVM Γ .impure ty) (V : Γ.Valuation)
    (s : State := default) :
    ImmediateUBOr (HVector TyDenote.toType ty × State) :=
  ((Com.denoteWithMemoryCore com V).run ({} : FunctionEnv State)).run s

/-- Evaluate an impure command with a fuel-bounded CFG interpreter and an empty function environment. -/
def Com.denoteWithMemoryFuel (fuel : Nat) (com : Com LLVM Γ .impure ty) (V : Γ.Valuation)
    (s : State := default) :
    ImmediateUBOr (HVector TyDenote.toType ty × State) :=
  Com.denoteWithMemoryFuelIn ({} : FunctionEnv State) fuel com V s

@[simp] theorem Com.denoteWithDefaultFunctionEnv_instDefault
    (com : Com LLVM Γ .impure ty) (V : Γ.Valuation) (s : State := default) :
    @InstCombine.LLVMMemory.Com.denoteWithDefaultFunctionEnv Γ ty
        (InstCombine.LLVMMemory.instDefaultFunctionEnvFor Γ ty)
        com V s
    = InstCombine.LLVMMemory.Com.denoteWithMemory com V s := by
  rfl

@[simp] theorem Com.denoteWithDefaultFunctionEnvFuel_instDefault
    (fuel : Nat) (com : Com LLVM Γ .impure ty) (V : Γ.Valuation) (s : State := default) :
    @InstCombine.LLVMMemory.Com.denoteWithDefaultFunctionEnvFuel Γ ty
        (InstCombine.LLVMMemory.instDefaultFunctionEnvFor Γ ty)
        fuel com V s
    = InstCombine.LLVMMemory.Com.denoteWithMemoryFuel fuel com V s := by
  rfl

@[simp] theorem Com.denoteWithMemoryIn_empty (com : Com LLVM Γ .impure ty)
    (V : Γ.Valuation) (s : State := default) :
    InstCombine.LLVMMemory.Com.denoteWithMemoryIn ({} : FunctionEnv State) com V s
    = InstCombine.LLVMMemory.Com.denoteWithMemory com V s := by
  rfl

@[simp] theorem Com.denoteWithMemoryFuelIn_empty (fuel : Nat) (com : Com LLVM Γ .impure ty)
    (V : Γ.Valuation) (s : State := default) :
    InstCombine.LLVMMemory.Com.denoteWithMemoryFuelIn ({} : FunctionEnv State) fuel com V s
    = InstCombine.LLVMMemory.Com.denoteWithMemoryFuel fuel com V s := by
  rfl

@[simp] theorem Com.denoteWithMemory_eq (com : Com LLVM Γ .impure ty)
    (V : Γ.Valuation) (s : State := default) :
    InstCombine.LLVMMemory.Com.denoteWithMemory com V s
    = ((InstCombine.LLVMMemory.Com.denoteWithMemoryCore com V).run ({} : FunctionEnv State)).run s := by
  rfl

@[simp] theorem Com.denoteWithMemoryFuel_eq (fuel : Nat) (com : Com LLVM Γ .impure ty)
    (V : Γ.Valuation) (s : State := default) :
    InstCombine.LLVMMemory.Com.denoteWithMemoryFuel fuel com V s
    = InstCombine.LLVMMemory.Com.denoteWithMemoryFuelIn
        ({} : FunctionEnv State) fuel com V s := by
  rfl

end LLVMMemory
end InstCombine
