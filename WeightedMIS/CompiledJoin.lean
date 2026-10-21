module

public import WeightedMIS.CompiledInsert

/-! # Compilation of the canonical join used by extraction -/

@[expose] public section

namespace WeightedMIS.CompiledTrie

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine

def JoinAtom : Atom → Prop
  | .register r => r ≠ 8 ∧ r ≠ 9 ∧ r ≠ 10
  | _ => True

theorem joinAtom_eval_load {a : Atom} (ha : JoinAtom a) (regs : Registers) (c : Cell) :
    a.eval (loadRegisters regs 8 9 10 c) = a.eval regs := by
  cases a with
  | register r =>
    obtain ⟨h8, h9, h10⟩ := ha
    simp [Atom.eval, loadRegisters, h8, h9, h10]
  | null => rfl
  | flag b => rfl

theorem compile_join_allocate {p : ℕ} {code : Code p} {h final : Heap} {regs : Registers}
    {left right : Atom} {l r : Ptr} {next : Command p} {outputs : List Value} {budget : ℕ}
    (hl : left.eval regs = .pointer l) (hr : right.eval regs = .pointer r)
    (cont : Within code (h ++ [.fork l r]) (Function.update regs 11 (.pointer h.length))
      next outputs final budget) :
    Within code h regs (.allocate 11 (.fork left right) next) outputs final (8 + budget) := by
  apply Within.allocate (budget := budget) (c := .fork l r)
  · simp [CellExpr.eval, hl, hr, Value.asPointer]
  · exact cont

/-- The continuation uses its key and payload in registers 5 and 6. The
canonical joined root is placed in register 11; all scratch accesses are
explicit commands in `joinBody`. -/
theorem compile_joinBody {p : ℕ} {code : Code p} {h final : Heap} {regs : Registers}
    {left right : Atom} {l r : Ptr} {lc rc : Cell} {next : Command p}
    {outputs : List Value} {budget : ℕ}
    (hla : JoinAtom left) (hra : JoinAtom right)
    (hlv : left.eval regs = .pointer l) (hrv : right.eval regs = .pointer r)
    (hl : h[l]? = some lc) (hr : h[r]? = some rc)
    (cont : ∀ rs : Registers, rs 5 = regs 5 → rs 6 = regs 6 →
      rs 11 = .pointer (joinPointer l r h).value →
      Within code (joinPointer l r h).heap rs next outputs final budget) :
    Within code h regs (joinBody left right next) outputs final (28 + budget) := by
  have alloc : ∀ (rs : Registers), rs 5 = regs 5 → rs 6 = regs 6 →
      left.eval rs = .pointer l → right.eval rs = .pointer r →
      ¬(h[l]? = some .nil ∧ h[r]? = some .nil) →
      Within code h rs (.allocate 11 (.fork left right) next) outputs final (8 + budget) := by
    intro rs h5 h6 hal har hn
    apply compile_join_allocate hal har
    have hcont := cont (Function.update rs 11 (.pointer h.length))
      (by simpa using h5) (by simpa using h6)
      (by simp [joinPointer, Program.load, Program.allocate, hn])
    simpa [joinPointer, Program.load, Program.allocate, hn] using hcont
  unfold joinBody
  apply Within.mono (a := 10 + (18 + budget))
  · apply Within.load (budget := 18 + budget) hlv hl
    let rs := loadRegisters regs 8 9 10 lc
    have h5 : rs 5 = regs 5 := by simp [rs, loadRegisters]
    have h6 : rs 6 = regs 6 := by simp [rs, loadRegisters]
    have hal : left.eval rs = .pointer l := (joinAtom_eval_load hla regs lc).trans hlv
    have har : right.eval rs = .pointer r := (joinAtom_eval_load hra regs lc).trans hrv
    cases lc with
    | nil =>
      apply Within.mono (a := 10 + (8 + budget)) <;> try omega
      apply Within.load (budget := 8 + budget) har hr
      let rt := loadRegisters rs 8 9 10 rc
      have ht5 : rt 5 = regs 5 := by simpa [rt, loadRegisters] using h5
      have ht6 : rt 6 = regs 6 := by simpa [rt, loadRegisters] using h6
      have htal : left.eval rt = .pointer l := (joinAtom_eval_load hla rs rc).trans hal
      have htar : right.eval rt = .pointer r := (joinAtom_eval_load hra rs rc).trans har
      cases rc with
      | nil =>
        apply Within.mono (a := 3 + budget)
        · apply Within.copy (budget := budget)
          have hn : h[l]? = some .nil ∧ h[r]? = some .nil := ⟨hl, hr⟩
          have hcont := cont (Function.update rt 11 (.pointer 0))
            (by simpa using ht5) (by simpa using ht6)
            (by simp [joinPointer, Program.load, Program.pure, hn])
          simpa [joinPointer, Program.load, Program.pure, hn, rt, Atom.eval] using hcont
        · omega
      | bit b q => exact alloc rt ht5 ht6 htal htar (by simp [hr])
      | cons a t => exact alloc rt ht5 ht6 htal htar (by simp [hr])
      | fork a b => exact alloc rt ht5 ht6 htal htar (by simp [hr])
      | bucket q => exact alloc rt ht5 ht6 htal htar (by simp [hr])
      | pair a b => exact alloc rt ht5 ht6 htal htar (by simp [hr])
    | bit b q => exact (alloc rs h5 h6 hal har (by simp [hl])).mono (by omega)
    | cons a t => exact (alloc rs h5 h6 hal har (by simp [hl])).mono (by omega)
    | fork a b => exact (alloc rs h5 h6 hal har (by simp [hl])).mono (by omega)
    | bucket q => exact (alloc rs h5 h6 hal har (by simp [hl])).mono (by omega)
    | pair a b => exact (alloc rs h5 h6 hal har (by simp [hl])).mono (by omega)
  · omega

theorem compile_finishPop {p : ℕ} {code : Code p} {h : Heap} {regs : Registers}
    {left right : Atom} {l r key a : Ptr} {lc rc : Cell} (b : Bool)
    (hla : JoinAtom left) (hra : JoinAtom right)
    (hlv : left.eval regs = .pointer l) (hrv : right.eval regs = .pointer r)
    (hl : h[l]? = some lc) (hr : h[r]? = some rc)
    (hk : regs 5 = .pointer key) (ha : regs 6 = .pointer a) :
    Within code h regs (finishPop b left right)
      [.flag true, .pointer (joinPointer l r h).heap.length, .pointer a,
        .pointer (joinPointer l r h).value]
      ((joinPointer l r h).heap ++ [.bit b key]) 45 := by
  unfold finishPop
  apply compile_joinBody (budget := 17) hla hra hlv hrv hl hr
  intro rs h5 h6 h11
  apply Within.allocate (budget := 9) (c := .bit b key)
  · simp [CellExpr.eval, Atom.eval, h5, hk, Value.asPointer, Value.asFlag]
  · simpa [values, Atom.eval, h6, ha, h11] using
      Within.ret code ((joinPointer l r h).heap ++ [.bit b key])
        (Function.update rs 14 (.pointer (joinPointer l r h).heap.length))
        [.flag true, .register 14, .register 6, .register 11]

end WeightedMIS.CompiledTrie
