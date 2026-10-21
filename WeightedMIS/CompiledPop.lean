module

public import WeightedMIS.CompiledJoin
public import WeightedMIS.PointerPopSafety
public import WeightedMIS.EfficientSearchCodeSearchHelpers

/-! # Compilation correctness of minimum extraction -/

@[expose] public section

namespace WeightedMIS.CompiledTrie

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine
open WeightedMIS.EfficientSearch.RegisterCode (popOutput)

theorem compile_emptyPop {p : ℕ} (code : Code p) (h : Heap) (regs : Registers) {tree : Ptr}
    (ht : regs 0 = .pointer tree) :
    Within code h regs emptyPop (popOutput tree none) h 9 := by
  simpa [emptyPop, popOutput, values, Atom.eval, ht] using
    Within.ret code h regs [.flag false, .null, .null, .register 0]

theorem compile_bucketTail {p : ℕ} (code : Code p) (h : Heap) (regs : Registers)
    {a tail : Ptr} {c : Cell} (ha : regs 4 = .pointer a) (ht : regs 5 = .pointer tail)
    (loaded : h[tail]? = some c) :
    Within code h regs bucketTailBody
      [.flag true, .pointer 0, .pointer a, .pointer (leafPointer tail h).value]
      (leafPointer tail h).heap 25 := by
  have alloc : ∀ rs : Registers, rs 4 = .pointer a → rs 5 = .pointer tail →
      Within code h rs (.allocate 10 (.bucket (.register 5))
        (.ret [.flag true, .null, .register 4, .register 10]))
        [.flag true, .pointer 0, .pointer a, .pointer h.length] (h ++ [.bucket tail]) 15 := by
    intro rs h4 h5
    apply Within.allocate (budget := 9) (c := .bucket tail)
    · simp [CellExpr.eval, Atom.eval, h5, Value.asPointer]
    · simpa [values, Atom.eval, h4] using
        Within.ret code (h ++ [.bucket tail]) (Function.update rs 10 (.pointer h.length))
          [.flag true, .null, .register 4, .register 10]
  unfold bucketTailBody
  apply Within.load (budget := 15) (pointer := tail) (c := c)
  · exact ht
  · exact loaded
  · have h4 : loadRegisters regs 7 8 9 c 4 = .pointer a := by
      simpa [loadRegisters] using ha
    have h5 : loadRegisters regs 7 8 9 c 5 = .pointer tail := by
      simpa [loadRegisters] using ht
    cases c with
    | nil =>
      apply Within.mono (a := 9)
      · simpa [leafPointer, Program.load, Program.pure, loaded, Cases.select, values, Atom.eval, h4] using
          Within.ret code h (loadRegisters regs 7 8 9 .nil) [.flag true, .null, .register 4, .null]
      · omega
    | bit b q => simpa [leafPointer, Program.load, Program.allocate, loaded, Cases.select] using alloc _ h4 h5
    | cons x q => simpa [leafPointer, Program.load, Program.allocate, loaded, Cases.select] using alloc _ h4 h5
    | fork x q => simpa [leafPointer, Program.load, Program.allocate, loaded, Cases.select] using alloc _ h4 h5
    | bucket q => simpa [leafPointer, Program.load, Program.allocate, loaded, Cases.select] using alloc _ h4 h5
    | pair x q => simpa [leafPointer, Program.load, Program.allocate, loaded, Cases.select] using alloc _ h4 h5

theorem compile_extendPop {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {left right : Atom} {sibling key a tree original : Ptr} (b : Bool)
    (hla : JoinAtom left) (hra : JoinAtom right)
    (hlv : left.eval regs = .pointer (if b then sibling else tree))
    (hrv : right.eval regs = .pointer (if b then tree else sibling))
    (hs : sibling < h.length) (ht : tree < h.length)
    (hk : regs 5 = .pointer key) (ha : regs 6 = .pointer a) :
    Within code h regs (finishPop b left right)
      (popOutput original (extendPop b sibling key a tree h).value)
      (extendPop b sibling key a tree h).heap 45 := by
  have hleft : (if b then sibling else tree) < h.length := by cases b <;> assumption
  have hright : (if b then tree else sibling) < h.length := by cases b <;> assumption
  have hl : h[if b then sibling else tree]? = some h[if b then sibling else tree] :=
    List.getElem?_eq_some_iff.mpr ⟨hleft, rfl⟩
  have hr : h[if b then tree else sibling]? = some h[if b then tree else sibling] :=
    List.getElem?_eq_some_iff.mpr ⟨hright, rfl⟩
  simpa [extendPop, Program.allocate, popOutput] using
    compile_finishPop b hla hra hlv hrv hl hr hk ha

/-- Minimum extraction is one fixed closed recursive procedure. Every branch
is selected by a heap tag or a returned Boolean. -/
theorem compile_pop {p : ℕ} {code : Code p} {self : Fin p}
    (hcode : code self = popBody self) {h : Heap} {tree : Ptr} {result : Run PopValue}
    (he : PopEval h tree result) (hh : Valid h) (regs : Registers)
    (ht : regs 0 = .pointer tree) :
    Within code h regs (popBody self) (popOutput tree result.value) result.heap
      (100 * result.trace.length) := by
  induction he generalizing regs with
  | @empty h tree root =>
    apply Within.mono (a := 19)
    · unfold popBody
      apply Within.load (budget := 9) (pointer := tree) (c := .nil)
      · exact ht
      · exact root
      · exact compile_emptyPop code h _ (by simpa [loadRegisters, decoded] using ht)
    · simp [readBefore, Program.load]
  | @emptyBucket h tree items root item =>
    apply Within.mono (a := 29)
    · unfold popBody
      apply Within.load (budget := 19) (pointer := tree) (c := .bucket items)
      · exact ht
      · exact root
      · apply Within.load (budget := 9) (pointer := items) (c := .nil)
        · simp [Atom.eval, loadRegisters, decoded]
        · exact item
        · exact compile_emptyPop code h _ (by simpa [loadRegisters, decoded] using ht)
    · simp [readTwoBefore, Program.load]
  | @bucket h tree items a tail root item =>
    have htail : tail < h.length := hh.2 _ _ item _ (by simp [Cell.references])
    have loaded : h[tail]? = some h[tail] := List.getElem?_eq_some_iff.mpr ⟨htail, rfl⟩
    apply Within.mono (a := 45)
    · unfold popBody
      apply Within.load (budget := 35) (pointer := tree) (c := .bucket items)
      · exact ht
      · exact root
      · apply Within.load (budget := 25) (pointer := items) (c := .cons a tail)
        · simp [Atom.eval, loadRegisters, decoded]
        · exact item
        · exact compile_bucketTail code h _ (by simp [loadRegisters, decoded])
            (by simp [loadRegisters, decoded]) loaded
    · simp only [withEvents, readTwoBefore, Program.load, List.length_cons,
        List.length_append, List.length_nil]
      omega
  | @left h tree left right key a left' lp root child found ih =>
    obtain ⟨hsafe, hvalue⟩ := child.safe hh
    have hnew := (hvalue _ _ _ found).2.2
    have hsib : right < lp.heap.length := lt_of_lt_of_le
      (hh.2 _ _ root _ (by simp [Cell.references])) hsafe.1.length_le
    have hc := ih hh (initialRegisters [.pointer left]) (by simp [initialRegisters])
    let rs := loadRegisters regs 1 2 3 (.fork left right)
    let rt := bindResults rs [4, 5, 6, 7] [.flag true, .pointer key, .pointer a, .pointer left']
    have hf := compile_extendPop (code := code) (h := lp.heap) (regs := rt)
      (left := .register 7) (right := .register 2) (sibling := right) (tree := left')
      (key := key) (a := a) (original := tree) false
      (by simp [JoinAtom]) (by simp [JoinAtom])
      (by simp [Atom.eval, rt, bindResults])
      (by simp [Atom.eval, rt, rs, bindResults, loadRegisters, decoded]) hsib hnew
      (by simp [rt, bindResults]) (by simp [rt, bindResults])
    have houter : Within code h regs (popBody self)
        (popOutput tree (extendPop false right key a left' lp.heap).value)
        (extendPop false right key a left' lp.heap).heap
        (10 + (3 + 100 * lp.trace.length + (3 + 45))) := by
      unfold popBody
      apply Within.load (budget := 3 + 100 * lp.trace.length + (3 + 45))
        (pointer := tree) (c := .fork left right)
      · exact ht
      · exact root
      · apply Within.call (calleeBudget := 100 * lp.trace.length) (restBudget := 3 + 45)
          (returned := [.flag true, .pointer key, .pointer a, .pointer left']) (mid := lp.heap)
        · simpa [hcode, values, Atom.eval, loadRegisters, decoded, found, popOutput] using hc
        · apply Within.branch (budget := 45) (b := true)
          · simp [Atom.eval, bindResults]
          · exact hf
    apply houter.mono
    simp only [withEvents, sequenceRuns, readBefore, Program.load, List.length_cons,
      List.length_append, List.length_nil]
    omega
  | @right h tree left right key a right' lp rp root leftChild noLeft rightChild found ihl ihr =>
    obtain ⟨hlsafe, _⟩ := leftChild.safe hh
    obtain ⟨hrsafe, hvalue⟩ := rightChild.safe hlsafe.2.1
    have hnew := (hvalue _ _ _ found).2.2
    have hsib : left < rp.heap.length := lt_of_lt_of_le
      (hh.2 _ _ root _ (by simp [Cell.references])) (hlsafe.1.trans hrsafe.1).length_le
    have hcl := ihl hh (initialRegisters [.pointer left]) (by simp [initialRegisters])
    have hcr := ihr hlsafe.2.1 (initialRegisters [.pointer right]) (by simp [initialRegisters])
    let rs := loadRegisters regs 1 2 3 (.fork left right)
    let rt := bindResults rs [4, 5, 6, 7] [.flag false, .pointer 0, .pointer 0, .pointer left]
    let ru := bindResults rt [4, 5, 6, 7] [.flag true, .pointer key, .pointer a, .pointer right']
    have hf := compile_extendPop (code := code) (h := rp.heap) (regs := ru)
      (left := .register 1) (right := .register 7) (sibling := left) (tree := right')
      (key := key) (a := a) (original := tree) true
      (by simp [JoinAtom]) (by simp [JoinAtom])
      (by simp [Atom.eval, ru, rt, rs, bindResults, loadRegisters, decoded])
      (by simp [Atom.eval, ru, bindResults]) hsib hnew
      (by simp [ru, bindResults]) (by simp [ru, bindResults])
    have houter : Within code h regs (popBody self)
        (popOutput tree (extendPop true left key a right' rp.heap).value)
        (extendPop true left key a right' rp.heap).heap
        (10 + (3 + 100 * lp.trace.length + (3 + (3 + 100 * rp.trace.length + (3 + 45))))) := by
      unfold popBody
      apply Within.load (budget := 3 + 100 * lp.trace.length + (3 + (3 + 100 * rp.trace.length + (3 + 45))))
        (pointer := tree) (c := .fork left right)
      · exact ht
      · exact root
      · apply Within.call (calleeBudget := 100 * lp.trace.length)
          (restBudget := 3 + (3 + 100 * rp.trace.length + (3 + 45)))
          (returned := [.flag false, .pointer 0, .pointer 0, .pointer left]) (mid := lp.heap)
        · simpa [hcode, values, Atom.eval, loadRegisters, decoded, noLeft, popOutput] using hcl
        · apply Within.branch (budget := 3 + 100 * rp.trace.length + (3 + 45)) (b := false)
          · simp [Atom.eval, bindResults]
          · apply Within.call (calleeBudget := 100 * rp.trace.length) (restBudget := 3 + 45)
              (returned := [.flag true, .pointer key, .pointer a, .pointer right']) (mid := rp.heap)
            · simpa [hcode, values, Atom.eval, bindResults, loadRegisters, decoded, found, popOutput] using hcr
            · apply Within.branch (budget := 45) (b := true)
              · simp [Atom.eval, bindResults]
              · exact hf
    apply houter.mono
    simp only [withEvents, sequenceRuns, readBefore, Program.load, List.length_cons,
      List.length_append, List.length_nil]
    omega
  | @noChildren h tree left right lp rp root leftChild noLeft rightChild noRight ihl ihr =>
    obtain ⟨hlsafe, _⟩ := leftChild.safe hh
    have hcl := ihl hh (initialRegisters [.pointer left]) (by simp [initialRegisters])
    have hcr := ihr hlsafe.2.1 (initialRegisters [.pointer right]) (by simp [initialRegisters])
    have houter : Within code h regs (popBody self) (popOutput tree none) rp.heap
        (10 + (3 + 100 * lp.trace.length + (3 + (3 + 100 * rp.trace.length + (3 + 9))))) := by
      unfold popBody
      apply Within.load (budget := 3 + 100 * lp.trace.length + (3 + (3 + 100 * rp.trace.length + (3 + 9))))
        (pointer := tree) (c := .fork left right)
      · exact ht
      · exact root
      · apply Within.call (calleeBudget := 100 * lp.trace.length)
          (restBudget := 3 + (3 + 100 * rp.trace.length + (3 + 9)))
          (returned := [.flag false, .pointer 0, .pointer 0, .pointer left]) (mid := lp.heap)
        · simpa [hcode, values, Atom.eval, loadRegisters, decoded, noLeft, popOutput] using hcl
        · apply Within.branch (budget := 3 + 100 * rp.trace.length + (3 + 9)) (b := false)
          · simp [Atom.eval, bindResults]
          · apply Within.call (calleeBudget := 100 * rp.trace.length) (restBudget := 3 + 9)
              (returned := [.flag false, .pointer 0, .pointer 0, .pointer right]) (mid := rp.heap)
            · simpa [hcode, values, Atom.eval, bindResults, loadRegisters, decoded, noRight, popOutput] using hcr
            · apply Within.branch (budget := 9) (b := false)
              · simp [Atom.eval, bindResults]
              · exact compile_emptyPop code rp.heap _ (by simpa [bindResults, loadRegisters, decoded] using ht)
    apply houter.mono
    simp only [withEvents, sequenceRuns, Program.pure, readBefore, Program.load,
      List.length_cons, List.length_append, List.length_nil]
    omega

end WeightedMIS.CompiledTrie
