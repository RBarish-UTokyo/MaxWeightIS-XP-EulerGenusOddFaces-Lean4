module

public import WeightedMIS.RegisterKeyTrace
public import WeightedMIS.RegisterMembership
public import WeightedMIS.RegisterListFlatMap

/-!
# First-unseen enumeration of even key cycles

The scan reads a stored key order. A key already in the seen list is skipped.
For a fresh key the cycle procedure computes its first-return cycle and parity
bit; every cycle key followed by its mirror key is prepended to the seen list
by the flat-map combinator; and the cycle is emitted when its length is even.
The result refines `FlagKeyFaces.scanEven` for an arbitrary step procedure
whose successor returns to every root of the order within the fuel.
-/

@[expose] public section

namespace WeightedMIS.RegisterKeyFaceEnumeration

open WeightedMIS.PointerMemory WeightedMIS.RegisterMachine WeightedMIS.EfficientSearch
open WeightedMIS.EfficientSearch.Pointer WeightedMIS.ExpandedWords WeightedMIS.FlagKeyFaces
open WeightedMIS.RegisterFlagKeys WeightedMIS.RegisterKeyTrace WeightedMIS.RibbonTable

variable {p : ℕ}

/-- Arguments 0 = key, 1 = unused data, 2 = tail; prepends the key and its mirror. -/
def mirrorItemBody (along : Fin p) : Command p :=
  .call along [.register 0] [3]
    (.allocate 4 (.cons (.register 3) (.register 2))
      (.allocate 5 (.cons (.register 0) (.register 4)) (.ret [.register 5])))

/-- Arguments 0 = order, 1 = seen keys, 2 = step data; the result lists the
even cycles of fresh roots. -/
def scanBody (self member cycle mirrorAll : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .call member [.register 3, .register 1] [5]
      (.branch (.register 5)
        (.call self [.register 4, .register 1, .register 2] [6] (.ret [.register 6]))
        (.call cycle [.register 3, .register 2] [7, 8]
          (.call mirrorAll [.register 7, .register 2, .register 1] [9]
            (.call self [.register 4, .register 9, .register 2] [10]
              (.branch (.register 8) (.ret [.register 10])
                (.allocate 11 (.cons (.register 7) (.register 10)) (.ret [.register 11]))))))) }

/-- A list of stored key lists. -/
def CyclesAt {n : ℕ} (h : Heap) (ptr : Ptr) (cs : List (List (Bits n))) : Prop :=
  ListRep (fun h p c => WordsAt h p c) h ptr cs

theorem CyclesAt.mono {n : ℕ} {h h' : Heap} (he : Extends h h') {ptr : Ptr}
    {cs : List (List (Bits n))} (hc : CyclesAt h ptr cs) : CyclesAt h' ptr cs :=
  ListRep.mono he (fun _ _ hw => hw.mono he) hc

theorem mirrorItem_compiled (code : Code p) (self along : Fin p)
    (hself : code self = mirrorItemBody along) (halong : code along = alongBody)
    {W : ℕ} {h : Heap} (hh : Valid h) {xp dp acc : Ptr} {x : Bits (W + 2)}
    {tail : List (Bits (W + 2))} (hx : BitsAt h xp x) (ht : WordsAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q ([x, alongKey x] ++ tail) ∧
      Within code h (initialRegisters [.pointer xp, .pointer dp, .pointer acc]) (code self)
        [.pointer q] out 64 := by
  obtain ⟨m1, a, e1, v1, b1, w1⟩ := along_compiled code along halong hh hx
  obtain ⟨e2, v2, b2⟩ := alloc_wordCons v1 b1 (ht.mono e1)
  obtain ⟨e3, v3, b3⟩ := alloc_wordCons v2 ((hx.mono e1).mono e2) b2
  refine ⟨_, _, e1.trans (e2.trans e3), v3, b3, ?_⟩
  rw [hself]
  refine (call_of (by simp [values, Atom.eval, initialRegisters]) w1
    (Within.allocate (c := .cons a acc)
      (by simp [CellExpr.eval, Atom.eval, bindResults, initialRegisters, Value.asPointer])
      (Within.allocate (c := .cons xp m1.length)
        (by simp [CellExpr.eval, Atom.eval, bindResults, initialRegisters, Value.asPointer])
        (ret_values (by simp [values, Atom.eval]) le_rfl)))).mono ?_
  simp [CellExpr.args]

theorem mirrorAll_compiled (code : Code p) (self item along : Fin p)
    (hself : code self = RegisterListFlatMap.body self item)
    (hitem : code item = mirrorItemBody along) (halong : code along = alongBody)
    {W : ℕ} {h : Heap} (hh : Valid h) {cp dp acc : Ptr} {c tail : List (Bits (W + 2))}
    (hc : WordsAt h cp c) (ht : WordsAt h acc tail) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (mirrorBlock alongKey c ++ tail) ∧
      Within code h (initialRegisters [.pointer cp, .pointer dp, .pointer acc]) (code self)
        [.pointer q] out (91 * c.length + 13) := by
  obtain ⟨out, q, he, ho, hq, hw⟩ := RegisterListFlatMap.compiled code self item hself
    (fun h p (x : Bits (W + 2)) => BitsAt h p x) (fun _ _ (_ : Unit) => True)
    (fun h p l => WordsAt h p l) (fun he _ _ hb => hb.mono he) (fun _ _ _ _ => trivial)
    (fun _ x => [x, alongKey x]) 64
    (fun {_} hv {_ _ _} {_ _ _} hx _ ht =>
      mirrorItem_compiled code item along hitem halong hv hx ht)
    hh hc (data := ()) (dataPtr := dp) trivial ht
  exact ⟨out, q, he, ho, hq, hw.mono (by ring_nf; omega)⟩

/-- Stored membership decides list membership of fixed-width words. -/
theorem found_iff_mem {n : ℕ} (x : Bits n) (seen : List (Bits n)) :
    RegisterMembership.found x seen = decide (x ∈ seen) := by
  apply Bool.eq_iff_iff.mpr
  rw [RegisterMembership.found_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨k, hk, he⟩
    exact value_injective he ▸ hk
  · exact fun hx => ⟨x, hx, rfl⟩

theorem returnTrace_length_le {α : Type*} [DecidableEq α] (f : α → α) (root : α) :
    ∀ (k : ℕ) (y : α), (returnTrace f root k y).length ≤ k := by
  intro k
  induction k with
  | zero => intro y; simp [returnTrace]
  | succ k ih =>
    intro y
    simp only [returnTrace]
    split
    · simp
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (ih _)

theorem returnCycle_length_le {α : Type*} [DecidableEq α] (f : α → α) (k : ℕ) (x : α) :
    (returnCycle f k x).length ≤ k + 1 := by
  simp only [returnCycle, List.length_cons]
  exact Nat.succ_le_succ (returnTrace_length_le f x k (f x))

theorem mirrorBlock_length {α : Type*} (mirror : α → α) (c : List α) :
    (mirrorBlock mirror c).length = 2 * c.length := by
  induction c with
  | nil => rfl
  | cons x c ih =>
    simp only [mirrorBlock, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    rw [ih]
    ring

def scanBudget (n B k cap len : ℕ) : ℕ :=
  len * ((36 * n + 60) * cap + cycleBudget n B k + 91 * (k + 1) + 80) + 13

theorem scanBudget_succ (n B k cap len : ℕ) :
    scanBudget n B k cap (len + 1) = scanBudget n B k cap len +
      ((36 * n + 60) * cap + cycleBudget n B k + 91 * (k + 1) + 80) := by
  unfold scanBudget
  ring

/-- Procedure identifiers of the scan and its helpers. -/
structure Procedures (p : ℕ) where
  scan : Fin p
  member : Fin p
  cmp : Fin p
  cycle : Fin p
  loop : Fin p
  next : Fin p
  mirrorAll : Fin p
  mirrorItem : Fin p
  along : Fin p

/-- Code equations of the scan; the step procedure `next` is left open. -/
def Procedures.Matches (ids : Procedures p) (code : Code p) : Prop :=
  code ids.scan = scanBody ids.scan ids.member ids.cycle ids.mirrorAll ∧
  code ids.member = RegisterMembership.membershipBody ids.member ids.cmp ∧
  code ids.cmp = RegisterComparator.comparatorBody ids.cmp ∧
  code ids.cycle = cycleBody ids.loop ids.next ∧
  code ids.loop = loopBody ids.loop ids.next ids.cmp ∧
  code ids.mirrorAll = RegisterListFlatMap.body ids.mirrorAll ids.mirrorItem ∧
  code ids.mirrorItem = mirrorItemBody ids.along ∧
  code ids.along = alongBody

theorem scan_compiled {γ : Type*} {W : ℕ} (ids : Procedures p) (code : Code p)
    (hm : ids.Matches code)
    (f : Bits (W + 2) → Bits (W + 2)) (Good : Bits (W + 2) → Prop)
    (hgood : ∀ x, Good x → Good (f x))
    (DataAt : Heap → Ptr → γ → Prop)
    (dataMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr d, DataAt h ptr d → DataAt h' ptr d)
    (data : γ) (B : ℕ) (step : StepSpec code ids.next f Good DataAt data B) (k cap : ℕ) :
    ∀ (order : List (Bits (W + 2))) {h : Heap}, Valid h → ∀ {op sp dp : Ptr}
      {seen : List (Bits (W + 2))},
      WordsAt h op order → WordsAt h sp seen → DataAt h dp data →
      (∀ x ∈ order, Good x ∧ Returns f x k (f x)) →
      seen.length + 2 * (k + 1) * order.length ≤ cap →
      ∃ out q, Extends h out ∧ Valid out ∧
        CyclesAt out q (scanEven (returnCycle f k) alongKey seen order) ∧
        Within code h (initialRegisters [.pointer op, .pointer sp, .pointer dp]) (code ids.scan)
          [.pointer q] out (scanBudget (W + 2) B k cap order.length) := by
  obtain ⟨hscan, hmember, hcmp, hcycle, hloop, hmirror, hitem, halong⟩ := hm
  intro order
  induction order with
  | nil =>
    intro h hh op sp dp seen ho _ _ _ _
    have cell := WordsAt.nil_iff.mp ho
    refine ⟨h, 0, .refl h, hh, RegisterListCommon.listRep_null hh, ?_⟩
    rw [hscan]
    refine (Within.load (pointer := op) (c := .nil) (by simp [Atom.eval, initialRegisters]) cell
      (ret_values (by simp [values, Atom.eval]) le_rfl)).mono ?_
    simp [scanBudget]
  | cons x order ih =>
    intro h hh op sp dp seen ho hs hd hgood' hcap
    obtain ⟨xp, rest, cell, hx, hrest⟩ := WordsAt.cons_iff.mp ho
    have hxg := hgood' x List.mem_cons_self
    have hgood'' : ∀ y ∈ order, Good y ∧ Returns f y k (f y) :=
      fun y hy => hgood' y (List.mem_cons_of_mem x hy)
    have hmem := RegisterMembership.compiled code ids.member ids.cmp hmember hcmp hx hs
    rw [found_iff_mem] at hmem
    let regs := initialRegisters [Value.pointer op, .pointer sp, .pointer dp]
    let r1 := loadRegisters regs 3 4 15 (.cons xp rest)
    let r2 := bindResults r1 [5] [.flag (decide (x ∈ seen))]
    have hseenLe : seen.length ≤ cap := by
      simp only [List.length_cons] at hcap
      nlinarith
    have hmemB : RegisterMembership.budget (W + 2) seen.length ≤ (36 * (W + 2) + 60) * cap + 13 := by
      unfold RegisterMembership.budget
      have := Nat.mul_le_mul_left (36 * (W + 2) + 60) hseenLe
      omega
    have branchResult : ∃ out q, Extends h out ∧ Valid out ∧
        CyclesAt out q (scanEven (returnCycle f k) alongKey seen (x :: order)) ∧
        Within code h r2
          (.branch (.register 5)
            (.call ids.scan [.register 4, .register 1, .register 2] [6] (.ret [.register 6]))
            (.call ids.cycle [.register 3, .register 2] [7, 8]
              (.call ids.mirrorAll [.register 7, .register 2, .register 1] [9]
                (.call ids.scan [.register 4, .register 9, .register 2] [10]
                  (.branch (.register 8) (.ret [.register 10])
                    (.allocate 11 (.cons (.register 7) (.register 10)) (.ret [.register 11])))))))
          [.pointer q] out
          (scanBudget (W + 2) B k cap order.length + cycleBudget (W + 2) B k + 91 * (k + 1) + 51) := by
      by_cases hxs : x ∈ seen
      · obtain ⟨out, q, he, ho', hq, hw⟩ := ih hh hrest hs hd hgood''
          (by simp only [List.length_cons] at hcap; nlinarith)
        refine ⟨out, q, he, ho', by simpa [scanEven, hxs] using hq, ?_⟩
        refine (Within.branch (b := true) (by simp [Atom.eval, r2, bindResults, hxs])
          (call_of (by simp [values, Atom.eval, r2, r1, regs, bindResults, loadRegisters, decoded,
            initialRegisters]) hw (ret_values (by simp [values, Atom.eval, bindResults]) le_rfl))).mono ?_
        simp
        omega
      · obtain ⟨m1, cq, e1, v1, b1, w1⟩ := cycle_compiled code ids.cycle ids.loop ids.next ids.cmp
          hcycle hloop hcmp f Good hgood DataAt dataMono data B step k hh hx hd hxg.1 hxg.2
        obtain ⟨m2, sq, e2, v2, b2, w2⟩ := mirrorAll_compiled code ids.mirrorAll ids.mirrorItem
          ids.along hmirror hitem halong v1 (dp := dp) b1 (hs.mono e1)
        have hclen := returnCycle_length_le f k x
        obtain ⟨m3, rq, e3, v3, b3, w3⟩ := ih v2 (hrest.mono (e1.trans e2)) b2
          (dataMono (e1.trans e2) _ _ hd) hgood'' (by
            rw [List.length_append, mirrorBlock_length]
            simp only [List.length_cons] at hcap
            nlinarith)
        have hmirB : 91 * (returnCycle f k x).length + 13 ≤ 91 * (k + 1) + 13 := by omega
        let r3 := bindResults r2 [7, 8] [.pointer cq, .flag (parity (returnCycle f k x))]
        let r4 := bindResults r3 [9] [.pointer sq]
        let r5 := bindResults r4 [10] [.pointer rq]
        cases hpar : parity (returnCycle f k x)
        · -- even cycle: emitted
          have hcq : cq < m3.length := lt_of_lt_of_le b1.allocated (e2.trans e3).length_le
          obtain ⟨e4, v4, b4⟩ := RegisterListCommon.allocate_consRep
            (R := fun h p (c : List (Bits (W + 2))) => WordsAt h p c)
            (fun he _ _ hw => hw.mono he) v3 ((b1.mono e2).mono e3) hcq b3
          refine ⟨_, m3.length, e1.trans (e2.trans (e3.trans e4)), v4, ?_, ?_⟩
          · simpa [scanEven, hxs, hpar, CyclesAt] using b4
          refine (Within.branch (b := false) (by simp [Atom.eval, r2, bindResults, hxs])
            (call_of (by simp [values, Atom.eval, r2, r1, regs, bindResults, loadRegisters, decoded,
              initialRegisters]) w1
              (call_of (by simp [values, Atom.eval, r2, r1, regs, bindResults, loadRegisters,
                decoded, initialRegisters]) w2
                (call_of (by simp [values, Atom.eval, r2, r1, regs, bindResults,
                  loadRegisters, decoded, initialRegisters]) w3
                  (Within.branch (b := false) (by simp [Atom.eval, bindResults, hpar])
                    (Within.allocate (c := .cons cq rq)
                      (by simp [CellExpr.eval, Atom.eval, bindResults, Value.asPointer])
                      (ret_values (by simp [values, Atom.eval]) le_rfl))))))).mono ?_
          simp [CellExpr.args]
          omega
        · -- odd cycle: skipped
          refine ⟨m3, rq, e1.trans (e2.trans e3), v3, by simpa [scanEven, hxs, hpar] using b3, ?_⟩
          refine (Within.branch (b := false) (by simp [Atom.eval, r2, bindResults, hxs])
            (call_of (by simp [values, Atom.eval, r2, r1, regs, bindResults, loadRegisters, decoded,
              initialRegisters]) w1
              (call_of (by simp [values, Atom.eval, r2, r1, regs, bindResults, loadRegisters,
                decoded, initialRegisters]) w2
                (call_of (by simp [values, Atom.eval, r2, r1, regs, bindResults,
                  loadRegisters, decoded, initialRegisters]) w3
                  (Within.branch (b := true) (by simp [Atom.eval, bindResults, hpar])
                    (ret_values (by simp [values, Atom.eval, bindResults]) le_rfl)))))).mono ?_
          simp
          omega
    obtain ⟨out, q, he, ho', hq, hw⟩ := branchResult
    refine ⟨out, q, he, ho', hq, ?_⟩
    rw [hscan]
    refine (Within.load (pointer := op) (c := .cons xp rest) (by simp [Atom.eval, initialRegisters])
      cell (call_of (by simp [values, Atom.eval, r1, regs, loadRegisters, decoded,
        initialRegisters]) hmem hw)).mono ?_
    simp only [List.length_cons, List.length_nil, scanBudget_succ]
    omega

end WeightedMIS.RegisterKeyFaceEnumeration
