module

public import WeightedMIS.RegisterMachineFacts

/-! # Allocated-register invariants for closed programs -/

@[expose] public section

namespace WeightedMIS.RegisterMachine

open WeightedMIS.PointerMemory

def Value.Bounded (bound : ℕ) (v : Value) : Prop := v.word.Bounded bound

def RegistersBound (bound : ℕ) (regs : Registers) : Prop := ∀ r, (regs r).Bounded bound

def ValuesBound (bound : ℕ) (vs : List Value) : Prop := ∀ v ∈ vs, v.Bounded bound

theorem Value.bounded_mono {a b : ℕ} {v : Value} (hv : v.Bounded a) (hab : a ≤ b) :
    v.Bounded b := by
  cases v with
  | pointer p => exact lt_of_lt_of_le hv hab
  | flag => trivial

theorem registersBound_mono {a b : ℕ} {regs : Registers} (hr : RegistersBound a regs) (hab : a ≤ b) :
    RegistersBound b regs := fun r => Value.bounded_mono (hr r) hab

theorem valuesBound_mono {a b : ℕ} {vs : List Value} (hv : ValuesBound a vs) (hab : a ≤ b) :
    ValuesBound b vs := fun v hm => Value.bounded_mono (hv v hm) hab

theorem null_allocated {h : Heap} (hh : Valid h) : 0 < h.length :=
  List.getElem?_eq_some_iff.mp hh.1 |>.1

theorem Atom.bounded {bound : ℕ} {regs : Registers} (hr : RegistersBound bound regs)
    (hzero : 0 < bound) (a : Atom) : (a.eval regs).Bounded bound := by
  cases a with
  | register r => exact hr r
  | null => exact hzero
  | flag => trivial

theorem values_bounded {bound : ℕ} {regs : Registers} (hr : RegistersBound bound regs)
    (hzero : 0 < bound) (args : List Atom) : ValuesBound bound (values regs args) := by
  intro v hv
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
  exact a.bounded hr hzero

theorem update_bounded {bound : ℕ} {regs : Registers} (hr : RegistersBound bound regs)
    (dst : Register) {v : Value} (hv : v.Bounded bound) :
    RegistersBound bound (Function.update regs dst v) := by
  intro r
  by_cases he : r = dst
  · subst r; simpa using hv
  · simpa [Function.update_of_ne he] using hr r

theorem initialRegisters_bounded {bound : ℕ} {args : List Value}
    (hzero : 0 < bound) (ha : ValuesBound bound args) :
    RegistersBound bound (initialRegisters args) := by
  intro r
  cases hv : args[r.val]? with
  | none => simpa [initialRegisters, hv, Value.Bounded, Value.word, Word.Bounded] using hzero
  | some v =>
    have hm := List.mem_of_getElem? hv
    simpa [initialRegisters, hv] using ha v hm

theorem bindResults_bounded {bound : ℕ} {regs : Registers} {rs : List Register} {vs : List Value}
    (hr : RegistersBound bound regs) (hv : ValuesBound bound vs) :
    RegistersBound bound (bindResults regs rs vs) := by
  induction rs generalizing regs vs with
  | nil => exact hr
  | cons r rs ih =>
    cases vs with
    | nil => exact hr
    | cons v vs =>
      exact ih (update_bounded hr r (hv v List.mem_cons_self))
        (fun a ha => hv a (List.mem_cons_of_mem v ha))

theorem Value.moves_bound {bound : ℕ} {v : Value} (hv : v.Bounded bound) :
    TraceBound v.moves bound := by
  cases v with
  | pointer p =>
    intro e he q hq
    simp only [Value.moves, List.mem_cons, List.not_mem_nil, or_false, or_self] at he
    subst e
    simp only [Event.references, List.mem_singleton] at hq
    exact hq ▸ hv
  | flag b =>
    intro e he q hq
    simp only [Value.moves, List.mem_cons, List.not_mem_nil, or_false, or_self] at he
    subst e
    simp [Event.references] at hq

theorem moves_bound {bound : ℕ} {vs : List Value} (hv : ValuesBound bound vs) :
    TraceBound (moves vs) bound := by
  induction vs with
  | nil => simp [moves, TraceBound]
  | cons v vs ih =>
    exact traceBound_append (Value.moves_bound (hv v List.mem_cons_self))
      (ih (fun a ha => hv a (List.mem_cons_of_mem v ha)))

theorem Value.pointer_bound {bound : ℕ} {v : Value} {p : Ptr}
    (hv : v.Bounded bound) (hp : v.asPointer = some p) : p < bound := by
  cases v <;> simp [Value.asPointer] at hp
  subst p
  exact hv

theorem CellExpr.fits {bound : ℕ} {regs : Registers} (hr : RegistersBound bound regs)
    (hzero : 0 < bound) {expr : CellExpr} {c : Cell} (he : expr.eval regs = some c) : c.Fits bound := by
  cases expr with
  | nil => simp [CellExpr.eval] at he; subst c; simp [Cell.Fits, Cell.references]
  | bit b t =>
    cases hb : b.eval regs <;> cases ht : t.eval regs <;>
      simp [CellExpr.eval, hb, ht, Value.asPointer, Value.asFlag] at he
    subst c
    intro q hq
    simp only [Cell.references, List.mem_singleton] at hq
    subst q
    exact Value.pointer_bound (t.bounded hr hzero) (by rw [ht]; rfl)
  | cons a t =>
    cases ha : a.eval regs <;> cases ht : t.eval regs <;>
      simp [CellExpr.eval, ha, ht, Value.asPointer, Value.asFlag] at he
    subst c
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Value.pointer_bound (a.bounded hr hzero) (by rw [ha]; rfl)
    · exact Value.pointer_bound (t.bounded hr hzero) (by rw [ht]; rfl)
  | fork a t =>
    cases ha : a.eval regs <;> cases ht : t.eval regs <;>
      simp [CellExpr.eval, ha, ht, Value.asPointer, Value.asFlag] at he
    subst c
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Value.pointer_bound (a.bounded hr hzero) (by rw [ha]; rfl)
    · exact Value.pointer_bound (t.bounded hr hzero) (by rw [ht]; rfl)
  | pair a t =>
    cases ha : a.eval regs <;> cases ht : t.eval regs <;>
      simp [CellExpr.eval, ha, ht, Value.asPointer, Value.asFlag] at he
    subst c
    intro q hq
    simp only [Cell.references, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact Value.pointer_bound (a.bounded hr hzero) (by rw [ha]; rfl)
    · exact Value.pointer_bound (t.bounded hr hzero) (by rw [ht]; rfl)
  | bucket a =>
    cases ha : a.eval regs <;> simp [CellExpr.eval, ha, Value.asPointer] at he
    subst c
    intro q hq
    simp only [Cell.references, List.mem_singleton] at hq
    subst q
    exact Value.pointer_bound (a.bounded hr hzero) (by rw [ha]; rfl)

theorem decoded_bounded {bound : ℕ} {c : Cell} (hzero : 0 < bound) (hc : c.Fits bound) :
    (decoded c).1.Bounded bound ∧ (decoded c).2.1.Bounded bound ∧ (decoded c).2.2.Bounded bound := by
  cases c <;> simp only [Cell.Fits, Cell.references, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_singleton] at hc
  all_goals simp only [decoded, Value.Bounded, Value.word, Word.Bounded]
  all_goals aesop

theorem loadRegisters_bounded {bound : ℕ} {regs : Registers} {c : Cell}
    (hr : RegistersBound bound regs) (hzero : 0 < bound) (hc : c.Fits bound)
    (first second bit : Register) : RegistersBound bound (loadRegisters regs first second bit c) := by
  have hd := decoded_bounded hzero hc
  exact update_bounded (update_bounded (update_bounded hr first hd.1) second hd.2.1) bit hd.2.2

theorem decodedMoves_bound {bound : ℕ} {c : Cell} (hzero : 0 < bound) (hc : c.Fits bound) :
    TraceBound (decodedMoves c) bound := by
  have hd := decoded_bounded hzero hc
  exact traceBound_append (traceBound_append (Value.moves_bound hd.1)
    (Value.moves_bound hd.2.1)) (Value.moves_bound hd.2.2)

theorem traceBound_control_cons {bound : ℕ} {events : List Event} (ht : TraceBound events bound) :
    TraceBound (.control :: events) bound := by
  intro e he p hp
  rcases List.mem_cons.mp he with rfl | he
  · simp [Event.references] at hp
  · exact ht e he p hp

@[simp] theorem savedRegisters_length (regs : Registers) : (savedRegisters regs).length = 16 := by
  simp [savedRegisters]

theorem savedRegisters_bounded {bound : ℕ} {regs : Registers} (hr : RegistersBound bound regs) :
    ∀ w ∈ savedRegisters regs, w.Bounded bound := by
  intro w hw
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hw
  exact hr r

end WeightedMIS.RegisterMachine
