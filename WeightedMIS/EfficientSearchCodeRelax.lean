module

public import WeightedMIS.EfficientSearchCodePush

/-! # Compilation of adjacency-list traversal -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.RegisterCode

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine

variable {p : ℕ} {code : Code p}

theorem relaxEval_value_some {h : Heap} {v path distance edges queue : Ptr}
    {result : Run (Option (Ptr × Bool))}
    (he : Pointer.RelaxEval h v path distance edges queue result) :
    ∃ q overflow, result.value = some (q, overflow) := by
  induction he with
  | nil => exact ⟨_, _, rfl⟩
  | cons cell edge value next ih =>
    obtain ⟨q, overflow, hv⟩ := ih
    simp [hv]

theorem relaxEval_compile {push self : Fin p} (hself : code self = relaxBody push self)
    (compilePush : ∀ {h : Heap} {vertex path distance arc queue : Ptr} {result : Run (Option (Ptr × Bool))},
      Pointer.PushEdgeEval h vertex path distance arc queue result →
      Within code h (initialRegisters [.pointer vertex, .pointer path, .pointer distance,
        .pointer arc, .pointer queue]) (code push)
        (queueOutput result.value) result.heap (100 * result.trace.length))
    {h : Heap} {vertex path distance edges queue : Ptr} {result : Run (Option (Ptr × Bool))}
    (he : Pointer.RelaxEval h vertex path distance edges queue result) :
    Within code h (initialRegisters [.pointer vertex, .pointer path, .pointer distance,
      .pointer edges, .pointer queue]) (code self)
      (queueOutput result.value) result.heap (100 * result.trace.length) := by
  induction he with
  | @nil h vertex path distance edges queue cell =>
    rw [hself]
    let regs := initialRegisters [.pointer vertex, .pointer path, .pointer distance,
      .pointer edges, .pointer queue]
    have hr : Within code h (loadRegisters regs 5 6 7 .nil) (.ret [r 4, .flag false])
        [.pointer queue, .flag false] h 5 := by
      simpa [regs, r, values, Atom.eval, initialRegisters, loadRegisters, decoded, Function.update_apply] using
        Within.ret code h (loadRegisters regs 5 6 7 .nil) [r 4, .flag false]
    have hl := Within.load (regs := regs) (address := r 3) (first := 5) (second := 6) (bit := 7)
      (branches := listCases (.ret [r 4, .flag false])
        (.call push [r 0, r 1, r 2, r 5, r 4] [8, 9]
          (.call self [r 0, r 1, r 2, r 6, r 8] [10, 11]
            (.branch (r 9) (.ret [r 10, .flag true]) (.ret [r 10, r 11])))))
      (by simp [regs, r, Atom.eval, initialRegisters]) cell
      (by simpa [listCases, Cases.select] using hr)
    exact hl.mono (by simp [Program.load])
  | @cons h vertex path distance edges queue arc tail nextQueue overflow step rest cell edge value next ih =>
    obtain ⟨out, lastOverflow, lastValue⟩ := relaxEval_value_some next
    let regs := initialRegisters [.pointer vertex, .pointer path, .pointer distance,
      .pointer edges, .pointer queue]
    let loaded := loadRegisters regs 5 6 7 (.cons arc tail)
    let pushed := bindResults loaded [8, 9] [.pointer nextQueue, .flag overflow]
    let finalRegs := bindResults pushed [10, 11] [.pointer out, .flag lastOverflow]
    have hb : Within code rest.heap finalRegs
        (.branch (r 9) (.ret [r 10, .flag true]) (.ret [r 10, r 11]))
        [.pointer out, .flag (overflow || lastOverflow)] rest.heap 8 := by
      apply Within.branch (budget := 5) (b := overflow)
        (by simp [finalRegs, pushed, r, Atom.eval, bindResults, Function.update_apply])
      cases overflow <;> simp only [Bool.false_or, Bool.true_or, Bool.false_eq_true, ↓reduceIte]
      · simpa [finalRegs, pushed, r, values, Atom.eval, bindResults, Function.update_apply] using
          Within.ret code rest.heap finalRegs [r 10, r 11]
      · simpa [finalRegs, pushed, r, values, Atom.eval, bindResults, Function.update_apply] using
          Within.ret code rest.heap finalRegs [r 10, .flag true]
    rw [lastValue] at ih
    have hrec := Within.call (regs := pushed) (procedure := self)
      (arguments := [r 0, r 1, r 2, r 6, r 8]) (results := [10, 11])
      (by simpa [pushed, loaded, regs, r, values, Atom.eval, initialRegisters, bindResults,
          loadRegisters, decoded, Function.update_apply, queueOutput] using ih) hb
    have hp := compilePush edge
    rw [value] at hp
    have hpush := Within.call (regs := loaded) (procedure := push)
      (arguments := [r 0, r 1, r 2, r 5, r 4]) (results := [8, 9])
      (by simpa [loaded, regs, r, values, Atom.eval, initialRegisters, loadRegisters, decoded,
          Function.update_apply, queueOutput] using hp) hrec
    have hl := Within.load (regs := regs) (address := r 3) (first := 5) (second := 6) (bit := 7)
      (branches := listCases (.ret [r 4, .flag false])
        (.call push [r 0, r 1, r 2, r 5, r 4] [8, 9]
          (.call self [r 0, r 1, r 2, r 6, r 8] [10, 11]
            (.branch (r 9) (.ret [r 10, .flag true]) (.ret [r 10, r 11])))))
      (by simp [regs, r, Atom.eval, initialRegisters]) cell
      (by simpa [listCases, Cases.select, loaded] using hpush)
    rw [hself]
    simp only [lastValue, Option.map_some, queueOutput]
    apply hl.mono
    simp only [List.length_cons, List.length_nil, List.length_append, Program.load]
    omega

end WeightedMIS.EfficientSearch.RegisterCode
