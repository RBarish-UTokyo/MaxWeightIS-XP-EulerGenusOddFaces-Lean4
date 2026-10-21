module

public import WeightedMIS.EfficientSearchCodeSearchHelpers

/-! # Compilation of the complete sparse search loop -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.RegisterCode

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine

variable {p : ℕ} {code : Code p}

theorem searchEval_output {h : Heap} {g q s : Ptr} {result : Run (Option Pointer.SearchRecord)}
    (he : Pointer.SearchEval h g q s result) :
    ∃ b outQueue outSettled, searchOutput result.value = [.flag b, .pointer outQueue, .pointer outSettled] := by
  induction he with
  | finished => exact ⟨false, _, _, rfl⟩
  | stale heapValid pop popValue read readValue lookup knownValue next ih => exact ih
  | overflow => exact ⟨true, _, _, rfl⟩
  | advance heapValid pop popValue read readValue lookup knownValue expand freshValue next ih => exact ih

theorem searchEval_compile {pop read lookupEmpty fresh self : Fin p}
    (hself : code self = searchBody pop read lookupEmpty fresh self)
    (compilePop : ∀ {h : Heap} {tree : Ptr} {result : Run PopValue}, PopEval h tree result → Valid h →
      Within code h (initialRegisters [.pointer tree]) (code pop)
        (popOutput tree result.value) result.heap (100 * result.trace.length))
    (compileRead : ∀ {h : Heap} {pointer : Ptr} {result : Run (Option (Ptr × Ptr))},
      Pointer.ReadPairEval h pointer result →
      Within code h (initialRegisters [.pointer pointer]) (code read)
        (pairOutput result.value) result.heap 15)
    (compileKnown : ∀ {h : Heap} {key tree : Ptr} {result : Run (Option Bool)},
      Pointer.LookupEmptyEval h key tree result →
      Within code h (initialRegisters [.pointer key, .pointer tree]) (code lookupEmpty)
        (flagOutput result.value) result.heap (100 * result.trace.length))
    (compileFresh : ∀ {h : Heap} {graph vertex path distance queue settled : Ptr}
        {result : Run (Option Pointer.FreshValue)},
      Pointer.FreshEval h graph vertex path distance queue settled result →
      Within code h (initialRegisters [.pointer graph, .pointer vertex, .pointer path,
        .pointer distance, .pointer queue, .pointer settled]) (code fresh)
        (freshOutput result.value) result.heap (100 * result.trace.length))
    {h : Heap} {graph queue settled : Ptr} {result : Run (Option Pointer.SearchRecord)}
    (he : Pointer.SearchEval h graph queue settled result) :
    Within code h (initialRegisters [.pointer graph, .pointer queue, .pointer settled]) (code self)
      (searchOutput result.value) result.heap (100 * result.trace.length) := by
  induction he with
  | @finished h graph queue settled popped heapValid popEval empty =>
    let regs := initialRegisters [.pointer graph, .pointer queue, .pointer settled]
    let finalRegs := bindResults regs [3, 4, 5, 6] [.flag false, .pointer 0, .pointer 0, .pointer queue]
    have hret : Within code popped.heap finalRegs (.ret [.flag false, r 1, r 2])
        [.flag false, .pointer queue, .pointer settled] popped.heap 7 := by
      simpa [finalRegs, regs, r, values, Atom.eval, initialRegisters, bindResults,
        Function.update_apply] using Within.ret code popped.heap finalRegs [.flag false, r 1, r 2]
    have hb := Within.branch (regs := finalRegs) (test := r 3) (b := false)
      (yes := foundSearchBody read lookupEmpty fresh self) (no := .ret [.flag false, r 1, r 2])
      (by simp [finalRegs, r, Atom.eval, bindResults]) (by simpa using hret)
    have hp := compilePop popEval heapValid
    rw [empty] at hp
    have hc := Within.call (regs := regs) (procedure := pop) (arguments := [r 1]) (results := [3, 4, 5, 6])
      (by simpa [regs, r, values, Atom.eval, initialRegisters, popOutput] using hp) hb
    rw [hself]
    apply hc.mono
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  | @stale h graph queue settled distance candidate tail vertex path popped record known rest
      heapValid popEval popValue readEval readValue knownEval knownValue next ih =>
    obtain ⟨status, outQueue, outSettled, hout⟩ := searchEval_output next
    rw [hout] at ih
    have ht := searchTail_compile (regs := knownRegs graph queue settled distance candidate tail vertex path false)
      (queueAtom := r 6) (settledAtom := r 2)
      (by simp [knownRegs, readRegs, popRegs, r, Atom.eval, initialRegisters, bindResults, Function.update_apply])
      (by simp [knownRegs, readRegs, popRegs, r, Atom.eval, initialRegisters, bindResults, Function.update_apply])
      (by simp [knownRegs, readRegs, popRegs, r, Atom.eval, initialRegisters, bindResults, Function.update_apply]) ih
    have hp := compilePop popEval heapValid
    have hr := compileRead readEval
    have hk := compileKnown knownEval
    rw [popValue] at hp
    rw [readValue] at hr
    rw [knownValue] at hk
    have hall := search_found_prefix (fresh := fresh)
      (by simpa [popOutput] using hp) (by simpa [pairOutput] using hr)
      (by simpa [flagOutput] using hk) (by simpa using ht)
    rw [hself]
    change Within _ _ _ _ (searchOutput rest.value) _ _
    rw [hout]
    apply hall.mono
    simp only [List.length_append, List.length_replicate]
    omega
  | @overflow h graph queue settled distance candidate tail vertex path newQueue newSettled
      popped record known expanded heapValid popEval popValue readEval readValue knownEval knownValue expand freshValue =>
    let regs := knownRegs graph queue settled distance candidate tail vertex path true
    let finalRegs := bindResults regs [10, 11, 12] [.pointer newQueue, .pointer newSettled, .flag true]
    have hret : Within code expanded.heap finalRegs (.ret [.flag true, r 10, r 11])
        [.flag true, .pointer newQueue, .pointer newSettled] expanded.heap 7 := by
      simpa [finalRegs, r, values, Atom.eval, bindResults, Function.update_apply] using
        Within.ret code expanded.heap finalRegs [.flag true, r 10, r 11]
    have hb := Within.branch (regs := finalRegs) (test := r 12) (b := true)
      (yes := .ret [.flag true, r 10, r 11]) (no := searchTail self (r 10) (r 11))
      (by simp [finalRegs, r, Atom.eval, bindResults]) (by simpa using hret)
    have hf := compileFresh expand
    rw [freshValue] at hf
    have hfc := Within.call (regs := regs) (procedure := fresh)
      (arguments := [r 0, r 7, r 8, r 4, r 6, r 2]) (results := [10, 11, 12])
      (by simpa [regs, knownRegs, readRegs, popRegs, r, values, Atom.eval, initialRegisters,
        bindResults, Function.update_apply, freshOutput] using hf) hb
    have hp := compilePop popEval heapValid
    have hr := compileRead readEval
    have hk := compileKnown knownEval
    rw [popValue] at hp
    rw [readValue] at hr
    rw [knownValue] at hk
    have hall := search_found_prefix
      (by simpa [popOutput] using hp) (by simpa [pairOutput] using hr)
      (by simpa [flagOutput] using hk) (by simpa [freshSearchBody, regs] using hfc)
    rw [hself]
    apply hall.mono
    simp only [List.length_append, List.length_replicate]
    omega
  | @advance h graph queue settled distance candidate tail vertex path newQueue newSettled
      popped record known expanded rest heapValid popEval popValue readEval readValue knownEval knownValue expand freshValue next ih =>
    obtain ⟨status, outQueue, outSettled, hout⟩ := searchEval_output next
    rw [hout] at ih
    let regs := knownRegs graph queue settled distance candidate tail vertex path true
    let finalRegs := bindResults regs [10, 11, 12] [.pointer newQueue, .pointer newSettled, .flag false]
    have ht := searchTail_compile (regs := finalRegs) (queueAtom := r 10) (settledAtom := r 11)
      (by simp [finalRegs, regs, knownRegs, readRegs, popRegs, r, Atom.eval, initialRegisters,
        bindResults, Function.update_apply])
      (by simp [finalRegs, r, Atom.eval, bindResults])
      (by simp [finalRegs, r, Atom.eval, bindResults]) ih
    have hb := Within.branch (regs := finalRegs) (test := r 12) (b := false)
      (yes := .ret [.flag true, r 10, r 11]) (no := searchTail self (r 10) (r 11))
      (by simp [finalRegs, r, Atom.eval, bindResults]) (by simpa using ht)
    have hf := compileFresh expand
    rw [freshValue] at hf
    have hfc := Within.call (regs := regs) (procedure := fresh)
      (arguments := [r 0, r 7, r 8, r 4, r 6, r 2]) (results := [10, 11, 12])
      (by simpa [regs, knownRegs, readRegs, popRegs, r, values, Atom.eval, initialRegisters,
        bindResults, Function.update_apply, freshOutput] using hf) hb
    have hp := compilePop popEval heapValid
    have hr := compileRead readEval
    have hk := compileKnown knownEval
    rw [popValue] at hp
    rw [readValue] at hr
    rw [knownValue] at hk
    have hall := search_found_prefix
      (by simpa [popOutput] using hp) (by simpa [pairOutput] using hr)
      (by simpa [flagOutput] using hk) (by simpa [freshSearchBody, regs] using hfc)
    rw [hself]
    change Within _ _ _ _ (searchOutput rest.value) _ _
    rw [hout]
    apply hall.mono
    simp only [List.length_append, List.length_replicate]
    omega

end WeightedMIS.EfficientSearch.RegisterCode
