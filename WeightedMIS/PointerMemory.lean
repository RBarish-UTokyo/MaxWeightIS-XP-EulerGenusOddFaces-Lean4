module

public import Mathlib
public import WeightedMIS.Statement

/-!
# An append-only, logarithmic-cost pointer RAM

Cells contain a fixed tag and at most two addresses.  Address zero is the
shared empty value.  `load` and `allocate` are the primitive RAM instructions;
all programs below record each executed instruction.  Their charge includes
the address bits and the bits of every transferred pointer field.  Functional
lists describe RAM states mathematically; their host-language indexing cost is
not asserted to be a machine implementation of random access.
-/

@[expose] public section

namespace WeightedMIS.PointerMemory

@[simp] theorem Cell.references_length_le (c : Cell) : c.references.length ≤ 2 := by
  cases c <;> simp [Cell.references]

def Extends (old new : Heap) : Prop := ∃ suffix, new = old ++ suffix

@[refl] theorem Extends.refl (h : Heap) : Extends h h := ⟨[], by simp⟩

theorem Extends.trans {a b c : Heap} (hab : Extends a b) (hbc : Extends b c) : Extends a c := by
  obtain ⟨xs, rfl⟩ := hab
  obtain ⟨ys, rfl⟩ := hbc
  exact ⟨xs ++ ys, by simp [List.append_assoc]⟩

theorem Extends.length_le {a b : Heap} (h : Extends a b) : a.length ≤ b.length := by
  obtain ⟨xs, rfl⟩ := h
  simp

theorem Extends.lookup {a b : Heap} (h : Extends a b) {p : Ptr} {c : Cell}
    (hp : a[p]? = some c) : b[p]? = some c := by
  obtain ⟨xs, rfl⟩ := h
  have hl : p < a.length := List.getElem?_eq_some_iff.mp hp |>.1
  rw [List.getElem?_append_left hl, hp]

/-- Every stored pointer addresses an allocated cell. Cycles are permitted;
representations of immutable values below impose the appropriate shape. -/
def Valid (h : Heap) : Prop :=
  h[0]? = some .nil ∧ ∀ (p : Ptr) (c : Cell), h[p]? = some c → ∀ q ∈ c.references, q < h.length

def Cell.Fits (c : Cell) (bound : ℕ) : Prop := ∀ q ∈ c.references, q < bound

@[simp] theorem Event.references_length_le (e : Event) : e.references.length ≤ 3 := by
  cases e with
  | load p c =>
    cases c with
    | none => simp [Event.references]
    | some c => have := c.references_length_le; simp only [Event.references, List.length_cons]; omega
  | allocate p c =>
    have := c.references_length_le
    simp only [Event.references, List.length_cons]
    omega
  | copyPointer p => simp [Event.references]
  | copyFlag b => simp [Event.references]
  | control => simp [Event.references]

def TraceBound (trace : List Event) (bound : ℕ) : Prop :=
  ∀ e ∈ trace, ∀ p ∈ e.references, p < bound

def bitCost (trace : List Event) : ℕ := (trace.map Event.bitCost).sum

theorem traceBound_mono {trace : List Event} {a b : ℕ}
    (h : TraceBound trace a) (hab : a ≤ b) : TraceBound trace b :=
  fun e he p hp => lt_of_lt_of_le (h e he p hp) hab

theorem traceBound_append {xs ys : List Event} {bound : ℕ}
    (hx : TraceBound xs bound) (hy : TraceBound ys bound) : TraceBound (xs ++ ys) bound := by
  intro e he p hp
  rcases List.mem_append.mp he with h | h
  · exact hx e h p hp
  · exact hy e h p hp

theorem sizes_sum_le (xs : List Ptr) (bound : ℕ)
    (h : ∀ p ∈ xs, p < bound) : (xs.map Nat.size).sum ≤ xs.length * bound.size := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
    have hp := Nat.size_le_size (Nat.le_of_lt (h p List.mem_cons_self))
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem event_bitCost_le (e : Event) (bound : ℕ)
    (h : ∀ p ∈ e.references, p < bound) : e.bitCost ≤ 4 + 3 * bound.size := by
  have hs := sizes_sum_le e.references bound h
  have hl := e.references_length_le
  unfold Event.bitCost
  nlinarith

theorem bitCost_le (trace : List Event) (bound : ℕ)
    (h : TraceBound trace bound) : bitCost trace ≤ trace.length * (4 + 3 * bound.size) := by
  induction trace with
  | nil => simp [bitCost]
  | cons e es ih =>
    have he := event_bitCost_le e bound (h e List.mem_cons_self)
    have ht := ih (fun f hf => h f (List.mem_cons_of_mem e hf))
    simp only [bitCost, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith

abbrev Program (α : Type*) := Heap → Run α

namespace Program

def pure (a : α) : Program α := fun h => ⟨a, h, []⟩

def bind (p : Program α) (f : α → Program β) : Program β := fun h =>
  let first := p h
  let second := f first.value first.heap
  ⟨second.value, second.heap, first.trace ++ second.trace⟩

instance : Monad Program where
  pure := pure
  bind := bind

def load (p : Ptr) : Program (Option Cell) := fun h =>
  ⟨h[p]?, h, [.load p h[p]?]⟩

def allocate (c : Cell) : Program Ptr := fun h =>
  ⟨h.length, h ++ [c], [.allocate h.length c]⟩

def control : Program Unit := fun h => ⟨(), h, [.control]⟩

end Program

/-- Every primitive and composition preserves old cells, charges allocations,
and bounds every referenced address by the final heap size. -/
def SafeRun (h : Heap) (r : Run α) : Prop :=
  Extends h r.heap ∧ Valid r.heap ∧ TraceBound r.trace r.heap.length ∧
    r.heap.length ≤ h.length + r.trace.length

theorem safe_pure (h : Heap) (hh : Valid h) (a : α) : SafeRun h (Program.pure a h) := by
  exact ⟨Extends.refl h, hh, by simp [TraceBound, Program.pure], by simp [Program.pure]⟩

theorem safe_control (h : Heap) (hh : Valid h) : SafeRun h (Program.control h) := by
  refine ⟨Extends.refl h, hh, ?_, ?_⟩
  · simp [TraceBound, Program.control, Event.references]
  · simp [Program.control]

theorem safe_load (h : Heap) (hh : Valid h) (p : Ptr) (hp : p < h.length) :
    SafeRun h (Program.load p h) := by
  refine ⟨Extends.refl h, hh, ?_, by simp [Program.load]⟩
  intro e he q hq
  simp only [Program.load, List.mem_singleton] at he
  subst e
  cases hc : h[p]? with
  | none =>
    simp only [hc, Event.references, List.mem_singleton] at hq
    exact hq ▸ hp
  | some c =>
    simp only [Event.references, hc, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hp
    · exact hh.2 p c hc q hq

theorem safe_allocate (h : Heap) (hh : Valid h) (c : Cell) (hc : c.Fits h.length) :
    SafeRun h (Program.allocate c h) := by
  dsimp only [SafeRun, Program.allocate]
  have hext : Extends h (h ++ [c]) := ⟨[c], rfl⟩
  refine ⟨hext, ⟨hext.lookup hh.1, ?_⟩, ?_, ?_⟩
  · intro p value hp q hq
    by_cases hlt : p < h.length
    · rw [List.getElem?_append_left hlt] at hp
      exact lt_of_lt_of_le (hh.2 p value hp q hq) hext.length_le
    · rw [List.getElem?_append_right (show h.length ≤ p from Nat.le_of_not_gt hlt)] at hp
      have hlen := List.getElem?_eq_some_iff.mp hp |>.1
      have hd : p - h.length = 0 := by simpa using Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlen)
      have hv : c = value := by simpa [hd] using hp
      subst value
      exact lt_of_lt_of_le (hc q hq) hext.length_le
  · intro e he p hp
    simp only [List.mem_singleton] at he
    subst e
    simp only [Event.references, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
    · have := hc p hp
      simpa using Nat.lt_succ_of_lt this
  · simp

theorem safe_bind (h : Heap) (p : Program α) (f : α → Program β)
    (hp : SafeRun h (p h)) (hf : SafeRun (p h).heap (f (p h).value (p h).heap)) :
    SafeRun h (Program.bind p f h) := by
  refine ⟨hp.1.trans hf.1, hf.2.1, ?_, ?_⟩
  · exact traceBound_append (traceBound_mono hp.2.2.1 hf.1.length_le) hf.2.2.1
  · have h1 := hp.2.2.2
    have h2 := hf.2.2.2
    simpa only [Program.bind, List.length_append, Nat.add_assoc] using le_trans h2 (Nat.add_le_add_right h1 _)

theorem safe_join {h : Heap} {first : Run α} {second : Run β}
    (hf : SafeRun h first) (hs : SafeRun first.heap second) :
    SafeRun h ⟨second.value, second.heap, first.trace ++ second.trace⟩ := by
  refine ⟨hf.1.trans hs.1, hs.2.1, ?_, ?_⟩
  · exact traceBound_append (traceBound_mono hf.2.2.1 hs.1.length_le) hs.2.2.1
  · have h1 := hf.2.2.2
    have h2 := hs.2.2.2
    simp only [List.length_append]
    omega

theorem safe_change_value {h : Heap} {r : Run α} (hr : SafeRun h r) (b : β) :
    SafeRun h ⟨b, r.heap, r.trace⟩ := hr

theorem safe_prefix {h : Heap} {r : Run α} (hr : SafeRun h r)
    (before : List Event) (hp : TraceBound before h.length) :
    SafeRun h ⟨r.value, r.heap, before ++ r.trace⟩ := by
  refine ⟨hr.1, hr.2.1, ?_, ?_⟩
  · exact traceBound_append (traceBound_mono hp hr.1.length_le) hr.2.2.1
  · have := hr.2.2.2
    simp only [List.length_append]
    omega

/-- This is the address-width bridge: at most one cell is allocated per event,
so no executed address needs more than log(input cells + executed events) bits. -/
theorem safe_bitCost_le {h : Heap} {r : Run α} (hr : SafeRun h r) :
    bitCost r.trace ≤ r.trace.length * (4 + 3 * (h.length + r.trace.length).size) := by
  apply le_trans (bitCost_le r.trace r.heap.length hr.2.2.1)
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left
    (Nat.mul_le_mul_left 3 (Nat.size_le_size hr.2.2.2)) 4)

end WeightedMIS.PointerMemory
