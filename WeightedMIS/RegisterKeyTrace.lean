module

public import WeightedMIS.FlagKeyFaces
public import WeightedMIS.RegisterFlagKeys
public import WeightedMIS.RegisterListCommon
public import WeightedMIS.RegisterComparator
public import WeightedMIS.ExpandedWords

/-!
# First-return traces of stored keys

A fixed step procedure maps a stored key to the stored key of its successor.
The loop compares the current key with the root using the compiled
comparator, stops at the first return, and otherwise prepends the current key
to the trace of its successor. It also returns the parity bit of the trace
length. The cycle procedure prepends the root to the trace of its successor.
The code has no fuel; the fuel of `returnTrace` appears only in the proof.
-/

@[expose] public section

namespace WeightedMIS.RegisterKeyTrace

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.FlagKeyFaces
open WeightedMIS.RegisterFlagKeys

variable {p : ℕ}

/-- The equality flag of the comparator decides equality of equal-width words. -/
theorem compare_eq_decide {n : ℕ} (a b : Bits n) :
    decide ((Bits.compare a b).1 = .eq) = decide (a = b) := by
  apply decide_eq_decide.mpr
  rw [(Bits.compare_correct a b).2.1]
  exact ⟨fun h => RibbonTable.value_injective h, fun h => h ▸ rfl⟩

/-- One allocated `cons` cell extends a stored word list by a stored word. -/
theorem alloc_wordCons {n : ℕ} {h : Heap} (hh : Valid h) {a tail : Ptr} {x : Bits n}
    {xs : List (Bits n)} (ha : BitsAt h a x) (ht : WordsAt h tail xs) :
    Extends h (h ++ [.cons a tail]) ∧ Valid (h ++ [.cons a tail]) ∧
      WordsAt (h ++ [.cons a tail]) h.length (x :: xs) :=
  RegisterListCommon.allocate_consRep (R := fun h p (w : Bits n) => BitsAt h p w)
    (fun he _ _ hb => hb.mono he) hh ha ha.allocated ht

/-- Return a pointer and the negation of a flag. -/
def negRet (ptr flag : Register) : Command p :=
  .branch (.register flag) (.ret [.register ptr, .flag false]) (.ret [.register ptr, .flag true])

theorem negRet_within (code : Code p) (h : Heap) {regs : Registers} {ptr flag : Register}
    {q : Ptr} {b : Bool} (hp : regs ptr = .pointer q) (hf : regs flag = .flag b) :
    Within code h regs (negRet ptr flag) [.pointer q, .flag (!b)] h 8 := by
  cases b
  · exact Within.branch (b := false) (by simp [Atom.eval, hf])
      (ret_values (by simp [values, Atom.eval, hp]) le_rfl)
  · exact Within.branch (b := true) (by simp [Atom.eval, hf])
      (ret_values (by simp [values, Atom.eval, hp]) le_rfl)

/-- Arguments 0 = root, 1 = current key, 2 = step data; results are the
trace up to the first return and the parity bit of its length. -/
def loopBody (self next cmp : Fin p) : Command p :=
  .call cmp [.register 1, .register 0] [3, 4]
    (.branch (.register 4) (.ret [.null, .flag false])
      (.call next [.register 1, .register 2] [5]
        (.call self [.register 0, .register 5, .register 2] [6, 7]
          (.allocate 8 (.cons (.register 1) (.register 6)) (negRet 8 7)))))

/-- Arguments 0 = root, 1 = step data; results are the cycle and its parity bit. -/
def cycleBody (loop next : Fin p) : Command p :=
  .call next [.register 0, .register 1] [2]
    (.call loop [.register 0, .register 2, .register 1] [3, 4]
      (.allocate 5 (.cons (.register 0) (.register 3)) (negRet 5 4)))

def loopBudget (n B k : ℕ) : ℕ := (36 * n + B + 61) * k + 40

def cycleBudget (n B k : ℕ) : ℕ := B + loopBudget n B k + 28

section Step

variable {γ : Type*} {n : ℕ} (code : Code p) (next : Fin p) (f : Bits n → Bits n)
  (Good : Bits n → Prop) (DataAt : Heap → Ptr → γ → Prop) (data : γ) (B : ℕ)

/-- Specification of a step procedure on good keys. -/
def StepSpec : Prop :=
  ∀ {h : Heap}, Valid h → ∀ {xp dp : Ptr} {x : Bits n}, Good x → BitsAt h xp x →
    DataAt h dp data → ∃ out q, Extends h out ∧ Valid out ∧ BitsAt out q (f x) ∧
      Within code h (initialRegisters [.pointer xp, .pointer dp]) (code next) [.pointer q] out B

end Step

variable {γ : Type*} {n : ℕ}

theorem loop_compiled (code : Code p) (self next cmp : Fin p)
    (hself : code self = loopBody self next cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (f : Bits n → Bits n) (Good : Bits n → Prop) (hgood : ∀ x, Good x → Good (f x))
    (DataAt : Heap → Ptr → γ → Prop)
    (dataMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr d, DataAt h ptr d → DataAt h' ptr d)
    (data : γ) (B : ℕ) (step : StepSpec code next f Good DataAt data B) (root : Bits n) :
    ∀ (k : ℕ) {h : Heap}, Valid h → ∀ {rp yp dp : Ptr} {y : Bits n},
      BitsAt h rp root → BitsAt h yp y → DataAt h dp data → Good y → Returns f root k y →
      ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (returnTrace f root k y) ∧
        Within code h (initialRegisters [.pointer rp, .pointer yp, .pointer dp]) (code self)
          [.pointer q, .flag (parity (returnTrace f root k y))] out (loopBudget n B k) := by
  intro k
  induction k with
  | zero => intro h _ _ _ _ _ _ _ _ _ hret; exact absurd hret.pos (by omega)
  | succ k ih =>
    intro h hh rp yp dp y hr hy hd hg hret
    have hc := RegisterComparator.compiled code cmp hcmp hy hr
    let regs := initialRegisters [Value.pointer rp, .pointer yp, .pointer dp]
    let r1 := bindResults regs [3, 4] (RegisterComparator.flags (Bits.compare y root).1)
    have hflag : r1 4 = .flag (decide (y = root)) := by
      simp [r1, bindResults, RegisterComparator.flags, compare_eq_decide]
    by_cases hyr : y = root
    · have hres : returnTrace f root (k + 1) y = [] := by simp [returnTrace, hyr]
      rw [hres]
      refine ⟨h, 0, .refl h, hh, RegisterListCommon.listRep_null hh, ?_⟩
      rw [hself]
      refine (call_of (by simp [values, Atom.eval, initialRegisters]) hc
        (Within.branch (b := true) (by simp only [Atom.eval]; exact hflag.trans (by simp [hyr]))
          (ret_values (by simp [values, Atom.eval, parity]) le_rfl))).mono ?_
      simp [loopBudget]
      nlinarith
    · obtain ⟨m1, q1, e1, v1, b1, w1⟩ := step hh hg hy hd
      obtain ⟨m2, q2, e2, v2, b2, w2⟩ := ih v1 (hr.mono e1) b1 (dataMono e1 _ _ hd) (hgood y hg)
        (hret.step hyr)
      obtain ⟨e3, v3, b3⟩ := alloc_wordCons v2 (hy.mono (e1.trans e2)) b2
      refine ⟨_, m2.length, e1.trans (e2.trans e3), v3, ?_, ?_⟩
      · simpa [returnTrace, hyr] using b3
      · have hres : returnTrace f root (k + 1) y = y :: returnTrace f root k (f y) := by
          simp [returnTrace, hyr]
        rw [hres, hself]
        let r2 := bindResults r1 [5] [.pointer q1]
        let r3 := bindResults r2 [6, 7] [.pointer q2, .flag (parity (returnTrace f root k (f y)))]
        have tail := Within.allocate (code := code) (h := m2) (regs := r3) (dst := 8)
          (expr := .cons (.register 1) (.register 6)) (c := .cons yp q2)
          (by simp [CellExpr.eval, Atom.eval, r3, r2, r1, regs, bindResults, initialRegisters, RegisterComparator.flags,
            Value.asPointer])
          (negRet_within code _ (ptr := 8) (flag := 7) (q := m2.length)
            (b := parity (returnTrace f root k (f y)))
            (by simp) (by simp [r3, bindResults]))
        refine (call_of (by simp [values, Atom.eval, regs, initialRegisters]) hc
          (Within.branch (b := false) (by simpa [Atom.eval, hyr] using hflag)
            (call_of (by simp [values, Atom.eval, regs, bindResults, initialRegisters, RegisterComparator.flags]) w1
              (call_of (by simp [values, Atom.eval, regs, bindResults, initialRegisters, RegisterComparator.flags]) w2
                tail)))).mono ?_
        simp [loopBudget, CellExpr.args]
        nlinarith

theorem cycle_compiled (code : Code p) (self loop next cmp : Fin p)
    (hself : code self = cycleBody loop next)
    (hloop : code loop = loopBody loop next cmp)
    (hcmp : code cmp = RegisterComparator.comparatorBody cmp)
    (f : Bits n → Bits n) (Good : Bits n → Prop) (hgood : ∀ x, Good x → Good (f x))
    (DataAt : Heap → Ptr → γ → Prop)
    (dataMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr d, DataAt h ptr d → DataAt h' ptr d)
    (data : γ) (B : ℕ) (step : StepSpec code next f Good DataAt data B) (k : ℕ)
    {h : Heap} (hh : Valid h) {xp dp : Ptr} {x : Bits n}
    (hx : BitsAt h xp x) (hd : DataAt h dp data) (hg : Good x) (hret : Returns f x k (f x)) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (returnCycle f k x) ∧
      Within code h (initialRegisters [.pointer xp, .pointer dp]) (code self)
        [.pointer q, .flag (parity (returnCycle f k x))] out (cycleBudget n B k) := by
  obtain ⟨m1, q1, e1, v1, b1, w1⟩ := step hh hg hx hd
  obtain ⟨m2, q2, e2, v2, b2, w2⟩ := loop_compiled code loop next cmp hloop hcmp f Good hgood
    DataAt dataMono data B step x k v1 (hx.mono e1) b1 (dataMono e1 _ _ hd) (hgood x hg) hret
  obtain ⟨e3, v3, b3⟩ := alloc_wordCons v2 (hx.mono (e1.trans e2)) b2
  refine ⟨_, m2.length, e1.trans (e2.trans e3), v3, b3, ?_⟩
  let regs := initialRegisters [Value.pointer xp, .pointer dp]
  let r1 := bindResults regs [2] [.pointer q1]
  let r2 := bindResults r1 [3, 4] [.pointer q2, .flag (parity (returnTrace f x k (f x)))]
  have tail := Within.allocate (code := code) (h := m2) (regs := r2) (dst := 5)
    (expr := .cons (.register 0) (.register 3)) (c := .cons xp q2)
    (by simp [CellExpr.eval, Atom.eval, r2, r1, regs, bindResults, initialRegisters,
      Value.asPointer])
    (negRet_within code _ (ptr := 5) (flag := 4) (q := m2.length)
      (b := parity (returnTrace f x k (f x)))
      (by simp) (by simp [r2, bindResults]))
  rw [hself]
  refine (call_of (by simp [values, Atom.eval, regs, initialRegisters]) w1
    (call_of (by simp [values, Atom.eval, regs, bindResults, initialRegisters]) w2
      tail)).mono ?_
  simp [cycleBudget, CellExpr.args]
  omega

end WeightedMIS.RegisterKeyTrace
