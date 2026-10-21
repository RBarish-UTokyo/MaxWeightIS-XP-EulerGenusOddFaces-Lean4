module

public import WeightedMIS.IncrementalComplement
public import WeightedMIS.RegisterIncidenceRows
public import WeightedMIS.ComputedEmbeddedMatrices

/-!
# Compiled incremental complement selection

The selection procedure walks the stored candidate rows. For each candidate
it allocates the search record `(c, zero)` and runs the compiled pivot search
of `RegisterRationalCut` over the current annihilator vectors. When a pivot
exists the candidate is accepted: the compiled `cut` replaces the annihilator
list, the tail is processed recursively, and the candidate's own row address
is prepended to the result. Otherwise the tail is processed with the same
annihilator list. The output is exactly `IncrementalComplement.selectW`.

The stage procedure builds the coordinate vectors, eliminates the face rows
from them with the compiled constraint loop, and runs the selection. With the
face rows of a ribbon and the deterministic candidate rows it returns rows
denoting `ComputedEmbeddedMatrices.globalRows`.
-/

@[expose] public section

namespace WeightedMIS.RegisterComplementSelect

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer StoredRational
open RegisterRationalRow (RowAt)
open RegisterRationalCut (RowsAt SearchAt)

variable {p N : ℕ}

/-- The accepting branch: cut, recurse on the tail, prepend the candidate. -/
def acceptBranch (self cut : Fin p) : Command p :=
  .call cut [.register 3, .register 2, .register 1] [8]
    (.call self [.register 4, .register 8, .register 2] [9]
      (.allocate 10 (.cons (.register 3) (.register 9)) (.ret [.register 10])))

/-- The rejecting branch: recurse on the tail with the same annihilator list. -/
def rejectBranch (self : Fin p) : Command p :=
  .call self [.register 4, .register 1, .register 2] [8] (.ret [.register 8])

/-- The candidate step after the cons cell is loaded. -/
def step (self find cut : Fin p) : Command p :=
  .allocate 5 (.pair (.register 3) (.register 2))
    (.call find [.register 1, .register 5] [6, 7]
      (.branch (.register 6) (acceptBranch self cut) (rejectBranch self)))

/-- Arguments 0=candidate rows, 1=annihilator vectors, 2=zero; result is the
list of accepted candidate rows (shared addresses). -/
def body (self find cut : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := step self find cut }

/-- Arguments 0=face rows, 1=candidate rows, 2=length witness (`m` items),
3=zero, 4=one; result is the list of accepted candidate rows. -/
def stageBody (coords fold select : Fin p) : Command p :=
  .call coords [.register 2, .register 3, .register 4] [5]
    (.call fold [.register 0, .register 3, .register 5] [6]
      (.call select [.register 1, .register 6, .register 3] [7] (.ret [.register 7])))

structure Procedures (p : ℕ) where
  elim : RegisterEliminateRows.Procedures p
  inc : RegisterIncidenceRows.Procedures p
  select : Fin p
  stage : Fin p

structure Procedures.Matches (ids : Procedures p) (code : Code p)
    (d : RegisterRationalProducts.Procedures p) : Prop where
  elim : ids.elim.Matches code d
  inc : ids.inc.Matches code
  select : code ids.select = body ids.select ids.elim.cut.find ids.elim.cut.cut
  stage : code ids.stage = stageBody ids.inc.coords ids.elim.fold ids.select

/-- Events of the pivot search over `k` vectors of length `m`. -/
def findBudget (N m k : ℕ) : ℕ := (RegisterRationalCut.nonzeroBudget N m + 30) * k + 15

/-- Events of the selection over `c` candidates with `k` annihilator vectors. -/
def selectBudget (N m k c : ℕ) : ℕ :=
  (findBudget N m k + RegisterRationalCut.cutBudget N m k + 60) * c + 13

/-- The compiled selection loop refines `IncrementalComplement.selectW`. -/
theorem select_compiled (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d) {m : ℕ}
    {zero : BinaryRational.Word N} :
    ∀ {cw : List (List (BinaryRational.Word N))} {h : Heap} {cp ap zp : Ptr}
      {aw : List (List (BinaryRational.Word N))}, Valid h →
      RowsAt h cp cw → RowsAt h ap aw → At h zp zero →
      (∀ c ∈ cw, c.length = m) → (∀ v ∈ aw, v.length = m) →
      ∃ out q, Extends h out ∧ Valid out ∧
        RowsAt out q (IncrementalComplement.selectW zero aw cw) ∧
        Within code h (initialRegisters [.pointer cp, .pointer ap, .pointer zp])
          (code ids.select) [.pointer q] out (selectBudget N m aw.length cw.length) := by
  intro cw
  induction cw with
  | nil =>
    intro h cp ap zp aw hh hc _ _ _ _
    obtain ⟨pointers, hlist, hrel⟩ := hc
    cases hrel
    cases hlist with
    | nil cell =>
      refine ⟨h, 0, .refl h, hh, RegisterListCommon.listRep_null hh, ?_⟩
      rw [hcode.select]
      unfold body
      apply Within.load (budget := 3) (pointer := cp) (c := .nil)
      · simp [Atom.eval, initialRegisters]
      · exact cell
      · simpa [values, Atom.eval, Cases.select] using
          Within.ret code h
            (loadRegisters (initialRegisters [.pointer cp, .pointer ap, .pointer zp]) 3 4 15 .nil)
            [.null]
  | cons c cs ih =>
    intro h cp ap zp aw hh hc ha hz hcl hal
    obtain ⟨pointers, hlist, hrel⟩ := hc
    cases hrel with
    | @cons xp _ ps _ hx hxs =>
    cases hlist with
    | @cons _ _ rest _ cell hrest =>
    have hcs : RowsAt h rest cs := ⟨ps, hrest, hxs⟩
    have hcm : c.length = m := hcl c List.mem_cons_self
    have hcsl : ∀ c' ∈ cs, c'.length = m := fun c' hc' => hcl c' (List.mem_cons_of_mem c hc')
    have hxl : xp < h.length := RegisterListCommon.ListAt.head_allocated hh cell
    -- allocate the search record
    obtain ⟨e1, v1, c1⟩ := RegisterRationalCut.allocate_pair hh hxl hz.allocated
    let h1 := h ++ [.pair xp zp]
    have hs : SearchAt h1 h.length (c, zero) :=
      ⟨xp, zp, c1, hx.mono e1, hz.mono e1⟩
    obtain ⟨h2, q, e2, v2, _, _, searched⟩ := RegisterListFind.compiled_const code
      ids.elim.cut.find ids.elim.cut.nonzero hcode.elim.cut.find RowAt SearchAt
      (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
      (fun d v => RationalWordRows.nonzeroW d.2 d.1 v)
      (RegisterRationalCut.nonzeroBudget N m) v1 (ha.mono e1) hs
      (fun {_} hv {_} {x} _ hx hd => by
        obtain ⟨out, e, vo, w⟩ :=
          RegisterRationalCut.nonzero_compiled code ids.elim.cut d hcode.elim.cut hv hx hd
        exact ⟨out, e, vo, by simpa [hcm] using w⟩)
    have e12 := e1.trans e2
    let found := (aw.find? (RationalWordRows.nonzeroW zero c)).isSome
    let r0 := initialRegisters [Value.pointer cp, .pointer ap, .pointer zp]
    let rl := loadRegisters r0 3 4 15 (.cons xp rest)
    let r1 := Function.update rl 5 (Value.pointer h.length)
    let r2 := bindResults r1 [6, 7] [Value.flag found, .pointer q]
    have fArgs : values r1 [.register 1, .register 5] = [.pointer ap, .pointer h.length] := by
      simp [r1, rl, r0, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    -- the shared prefix: load, allocate, search, branch
    have hpre : ∀ {final : Heap} {res : Value} {b : ℕ},
        Within code h2 r2 (if found then acceptBranch ids.select ids.elim.cut.cut
          else rejectBranch ids.select) [res] final b →
        Within code h r0 (code ids.select) [res] final
          (10 + (8 + (5 + findBudget N m aw.length + (3 + b)))) := by
      intro final res b hrest
      have br := Within.branch (test := .register 6) (b := found) (regs := r2)
        (yes := acceptBranch ids.select ids.elim.cut.cut) (no := rejectBranch ids.select)
        (by simp [r2, bindResults, Atom.eval]) hrest
      have fCall := Within.call (procedure := ids.elim.cut.find)
        (arguments := [.register 1, .register 5]) (results := [6, 7]) (regs := r1)
        (by simpa only [fArgs] using searched) br
      have a5 := Within.allocate (h := h) (regs := rl) (dst := 5)
        (expr := .pair (.register 3) (.register 2)) (c := .pair xp zp)
        (by simp [CellExpr.eval, Atom.eval, rl, r0, loadRegisters, decoded, initialRegisters,
          Value.asPointer]) fCall
      have loaded := Within.load (regs := r0) (address := .register 0) (first := 3)
        (second := 4) (bit := 15)
        (branches := { CompiledTrie.failCases with
          nil := .ret [.null]
          cons := step ids.select ids.elim.cut.find ids.elim.cut.cut })
        (by simp [Atom.eval, r0, initialRegisters]) cell a5
      rw [hcode.select]
      refine loaded.mono ?_
      simp only [findBudget, CellExpr.args, List.length_cons, List.length_nil]
      omega
    by_cases hfound : found = true
    · -- accept: cut, recurse, prepend
      obtain ⟨h3, ap', e3, v3, hcut, cutted⟩ := RegisterRationalCut.cut_compiled code
        ids.elim.cut d hcode.elim.cut v2 (hx.mono e12) (hz.mono e12) (ha.mono e12) hcm hal
      have e13 := e12.trans e3
      obtain ⟨h4, rq, e4, v4, hrq, recursed⟩ := ih v3 (hcs.mono e13) hcut (hz.mono e13) hcsl
        (RationalWordRows.cutW_lengths zero c aw m hal)
      have e14 := e13.trans e4
      obtain ⟨e5, v5, hres⟩ := RegisterListCommon.allocate_consRep
        (R := fun heap q (row : List (BinaryRational.Word N)) => RowAt heap q row)
        (fun ext _ _ hq => RowAt.mono ext hq) v4 (hx.mono e14)
        (lt_of_lt_of_le hxl e14.length_le) hrq
      have hsel : IncrementalComplement.selectW zero aw (c :: cs) =
          c :: IncrementalComplement.selectW zero (RationalWordRows.cutW zero c aw) cs := by
        have hf : (aw.find? (RationalWordRows.nonzeroW zero c)).isSome = true := hfound
        simp only [IncrementalComplement.selectW, hf, ↓reduceIte]
      refine ⟨h4 ++ [.cons xp rq], h4.length, e14.trans e5, v5, by rw [hsel]; exact hres, ?_⟩
      let r3 := bindResults r2 [8] [Value.pointer ap']
      let r4 := bindResults r3 [9] [Value.pointer rq]
      have last := RegisterListCommon.within_consRet code h4 (regs := r4) (dst := 10)
        (head := 3) (tail := 9) (a := xp) (t := rq)
        (by simp [r4, r3, r2, r1, rl, bindResults, loadRegisters, decoded])
        (by simp [r4, bindResults])
      have sArgs : values r3 [.register 4, .register 8, .register 2] =
          [.pointer rest, .pointer ap', .pointer zp] := by
        simp [r3, r2, r1, rl, r0, bindResults, loadRegisters, decoded, initialRegisters, values,
          Atom.eval]
      have sCall := Within.call (procedure := ids.select)
        (arguments := [.register 4, .register 8, .register 2]) (results := [9]) (regs := r3)
        (by simpa only [sArgs] using recursed) last
      have cArgs : values r2 [.register 3, .register 2, .register 1] =
          [.pointer xp, .pointer zp, .pointer ap] := by
        simp [r2, r1, rl, r0, bindResults, loadRegisters, decoded, initialRegisters, values,
          Atom.eval]
      have cCall := Within.call (procedure := ids.elim.cut.cut)
        (arguments := [.register 3, .register 2, .register 1]) (results := [8]) (regs := r2)
        (by simpa only [cArgs] using cutted) sCall
      have whole := hpre (by rw [hfound]; exact cCall)
      refine whole.mono ?_
      simp only [selectBudget, RationalWordRows.cutW_length, List.length_cons,
        List.length_nil]
      ring_nf
      omega
    · -- reject: recurse with the same annihilator list
      have hfalse : found = false := by simpa using hfound
      obtain ⟨h3, rq, e3, v3, hrq, recursed⟩ := ih v2 (hcs.mono e12) (ha.mono e12)
        (hz.mono e12) hcsl hal
      have hsel : IncrementalComplement.selectW zero aw (c :: cs) =
          IncrementalComplement.selectW zero aw cs := by
        have hf : (aw.find? (RationalWordRows.nonzeroW zero c)).isSome = false := hfalse
        simp only [IncrementalComplement.selectW, hf, Bool.false_eq_true, ↓reduceIte]
      refine ⟨h3, rq, e12.trans e3, v3, by rw [hsel]; exact hrq, ?_⟩
      let r3 := bindResults r2 [8] [Value.pointer rq]
      have last : Within code h3 r3 (.ret [.register 8]) [.pointer rq] h3 3 := by
        simpa [r3, bindResults, values, Atom.eval] using Within.ret code h3 r3 [.register 8]
      have sArgs : values r2 [.register 4, .register 1, .register 2] =
          [.pointer rest, .pointer ap, .pointer zp] := by
        simp [r2, r1, rl, r0, bindResults, loadRegisters, decoded, initialRegisters, values,
          Atom.eval]
      have sCall := Within.call (procedure := ids.select)
        (arguments := [.register 4, .register 1, .register 2]) (results := [8]) (regs := r2)
        (by simpa only [sArgs] using recursed) last
      have whole := hpre (by rw [hfalse]; exact sCall)
      refine whole.mono ?_
      simp only [selectBudget, List.length_cons, List.length_nil]
      ring_nf
      omega

/-- Events of the whole stage: coordinate vectors, face-row elimination, selection. -/
def stageBudget (N m L c : ℕ) : ℕ :=
  RegisterIncidenceRows.coordsBudget m + RegisterEliminateRows.budget N m m L +
    selectBudget N m m c + 30

/-- The word-level stage output. -/
def stageW (zero one : BinaryRational.Word N) (m : ℕ) (rw cw : List (List (BinaryRational.Word N))) :
    List (List (BinaryRational.Word N)) :=
  IncrementalComplement.selectW zero
    (RationalWordRows.eliminateRowsW zero rw (RationalWordRows.coordinateVectorsW zero one m)) cw

theorem stage_compiled_words {α : Type*} (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    (InputAt : Heap → Ptr → α → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    {h : Heap} (hh : Valid h) {rp cp lp zp op : Ptr} {m : ℕ} {L : List α}
    {rw cw : List (List (BinaryRational.Word N))} {zero one : BinaryRational.Word N}
    (hrw : RowsAt h rp rw) (hcw : RowsAt h cp cw) (hl : ListRep InputAt h lp L)
    (hz : At h zp zero) (ho : At h op one) (hL : L.length = m)
    (hrl : ∀ r ∈ rw, r.length = m) (hcl : ∀ c ∈ cw, c.length = m) :
    ∃ out q, Extends h out ∧ Valid out ∧ RowsAt out q (stageW zero one m rw cw) ∧
      Within code h (initialRegisters [.pointer rp, .pointer cp, .pointer lp, .pointer zp,
        .pointer op]) (code ids.stage) [.pointer q] out
        (stageBudget N m rw.length cw.length) := by
  subst hL
  obtain ⟨m1, coords, e1, v1, hcoords, coorded⟩ :=
    RegisterIncidenceRows.coords_compiled code ids.inc hcode.inc InputAt inputMono hh hl hz ho
  obtain ⟨m2, A, e2, v2, hA, eliminated⟩ := RegisterEliminateRows.compiled code ids.elim d
    hcode.elim v1 (hrw.mono e1) (hz.mono e1) hcoords (m := L.length) hrl
    (RationalWordRows.coordinateVectorsW_lengths _ _ _)
  have e12 := e1.trans e2
  obtain ⟨out, q, e3, v3, hq, selected⟩ := select_compiled code ids d hcode v2 (hcw.mono e12)
    hA (hz.mono e12) hcl
    (RationalWordRows.eliminateRowsW_lengths _ _ _ _ (RationalWordRows.coordinateVectorsW_lengths _ _ _))
  refine ⟨out, q, e12.trans e3, v3, hq, ?_⟩
  let r0 := initialRegisters [Value.pointer rp, .pointer cp, .pointer lp, .pointer zp,
    .pointer op]
  let r1 := bindResults r0 [5] [Value.pointer coords]
  let r2 := bindResults r1 [6] [Value.pointer A]
  let r3 := bindResults r2 [7] [Value.pointer q]
  have last : Within code out r3 (.ret [.register 7]) [.pointer q] out 3 := by
    simpa [r3, bindResults, values, Atom.eval] using Within.ret code out r3 [.register 7]
  have sArgs : values r2 [.register 1, .register 6, .register 3] =
      [.pointer cp, .pointer A, .pointer zp] := by
    simp [r2, r1, r0, bindResults, initialRegisters, values, Atom.eval]
  have sCall := Within.call (procedure := ids.select)
    (arguments := [.register 1, .register 6, .register 3]) (results := [7]) (regs := r2)
    (by simpa only [sArgs] using selected) last
  have fArgs : values r1 [.register 0, .register 3, .register 5] =
      [.pointer rp, .pointer zp, .pointer coords] := by
    simp [r1, r0, bindResults, initialRegisters, values, Atom.eval]
  have fCall := Within.call (procedure := ids.elim.fold)
    (arguments := [.register 0, .register 3, .register 5]) (results := [6]) (regs := r1)
    (by simpa only [fArgs] using eliminated) sCall
  have cArgs : values r0 [.register 2, .register 3, .register 4] =
      [.pointer lp, .pointer zp, .pointer op] := by
    simp [r0, initialRegisters, values, Atom.eval]
  have cCall := Within.call (procedure := ids.inc.coords)
    (arguments := [.register 2, .register 3, .register 4]) (results := [5]) (regs := r0)
    (by simpa only [cArgs] using coorded) fCall
  rw [hcode.stage]
  refine cCall.mono ?_
  simp only [stageBudget, RationalWordRows.eliminateRowsW_length,
    RationalWordRows.coordinateVectorsW_length, List.length_cons, List.length_nil]
  omega

/-- The compiled stage computes the deterministic kernel complement of
integer rows, from stored face rows and stored candidate rows. -/
theorem stage_compiled {α : Type*} {n m : ℕ} (left right : Fin m → Fin n)
    (ints : List (Fin m → ℤ)) (hints : ∀ r ∈ ints, ∀ j, (r j).natAbs ≤ 2)
    (hN : IncrementalComplement.selectWidth ints.length m ≤ N)
    (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    (InputAt : Heap → Ptr → α → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    {h : Heap} (hh : Valid h) {rp cp lp zp op : Ptr} {L : List α}
    {rw cw : List (List (BinaryRational.Word N))} {zero one : BinaryRational.Word N}
    (hzr : RationalWordRows.Rep zero 0) (hor : RationalWordRows.Rep one 1)
    (hrw : RowsAt h rp rw) (hrr : List.Forall₂ RationalWordRows.RowRep rw
      (ints.map ComputedKernel.rationalRow))
    (hcw : RowsAt h cp cw) (hcr : List.Forall₂ RationalWordRows.RowRep cw
      ((DeterministicKernel.candidates left right).map ComputedKernel.rationalRow))
    (hl : ListRep InputAt h lp L) (hL : L.length = m)
    (hz : At h zp zero) (ho : At h op one) :
    ∃ out q, ∃ acc : List (List (BinaryRational.Word N)),
      Extends h out ∧ Valid out ∧ RowsAt out q acc ∧
      List.Forall₂ RationalWordRows.RowRep acc
        ((DeterministicKernel.complement left right
          (ints.map ComputedKernel.rationalRow)).map ComputedKernel.rationalRow) ∧
      Within code h (initialRegisters [.pointer rp, .pointer cp, .pointer lp, .pointer zp,
        .pointer op]) (code ids.stage) [.pointer q] out
        (stageBudget N m ints.length (DeterministicKernel.candidates left right).length) := by
  have hrl : ∀ r ∈ rw, r.length = m := by
    intro r hr
    obtain ⟨x, _, hx⟩ := RationalWordRows.forall₂_mem_left hrr hr
    exact RationalWordRows.rowRep_length hx
  have hcl : ∀ c ∈ cw, c.length = m := by
    intro c hc
    obtain ⟨x, _, hx⟩ := RationalWordRows.forall₂_mem_left hcr hc
    exact RationalWordRows.rowRep_length hx
  obtain ⟨out, q, e, v, hq, w⟩ := stage_compiled_words code ids d hcode InputAt inputMono hh
    hrw hcw hl hz ho hL hrl hcl
  have hlr : rw.length = ints.length := by simpa using hrr.length_eq
  have hlc : cw.length = (DeterministicKernel.candidates left right).length := by
    simpa using hcr.length_eq
  refine ⟨out, q, _, e, v, hq, ?_, by simpa only [hlr, hlc] using w⟩
  exact IncrementalComplement.selectW_complement left right ints hints zero one hzr hor hN
    rw hrr cw hcr

/-- The integer face rows of a ribbon, in stored row order. -/
def faceInts {n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right) :
    List (Fin m → ℤ) :=
  List.ofFn fun i : R.EvenRowIndex (EmbeddingFaces.Flag.canonicalOrder m) =>
    fun e => R.computedIntegerMatrix (EmbeddingFaces.Flag.canonicalOrder m) i e

theorem localRows_eq {n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right) :
    ComputedEmbeddedMatrices.localRows R = (faceInts R).map ComputedKernel.rationalRow := by
  simp only [ComputedEmbeddedMatrices.localRows, faceInts, List.map_ofFn]
  rfl

theorem faceInts_bound {n m : ℕ} {left right : Fin m → Fin n} (R : EmbeddingFaces.Ribbon left right) :
    ∀ r ∈ faceInts R, ∀ j, (r j).natAbs ≤ 2 := by
  intro r hr j
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  have hsum := R.computedIntegerMatrix_column_bound (EmbeddingFaces.Flag.canonicalOrder m)
    (fun x => EmbeddingFaces.Flag.mem_canonicalOrder x) j
  exact le_trans (Finset.single_le_sum (f := fun r =>
    (R.computedIntegerMatrix (EmbeddingFaces.Flag.canonicalOrder m) r j).natAbs)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) hsum

theorem faceInts_length {n m : ℕ} {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) :
    (faceInts R).length ≤ 4 * m := by
  simpa [faceInts] using R.evenRow_count_le (EmbeddingFaces.Flag.canonicalOrder m)

/-- The compiled stage computes `ComputedEmbeddedMatrices.globalRows` from the
stored face rows of a ribbon and the stored deterministic candidate rows. -/
theorem globalRows_compiled {α : Type*} {n m : ℕ} {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right)
    (hN : IncrementalComplement.selectWidth (4 * m) m ≤ N)
    (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    (InputAt : Heap → Ptr → α → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    {h : Heap} (hh : Valid h) {rp cp lp zp op : Ptr} {L : List α}
    {rw cw : List (List (BinaryRational.Word N))} {zero one : BinaryRational.Word N}
    (hzr : RationalWordRows.Rep zero 0) (hor : RationalWordRows.Rep one 1)
    (hrw : RowsAt h rp rw) (hrr : List.Forall₂ RationalWordRows.RowRep rw
      (ComputedEmbeddedMatrices.localRows R))
    (hcw : RowsAt h cp cw) (hcr : List.Forall₂ RationalWordRows.RowRep cw
      ((DeterministicKernel.candidates left right).map ComputedKernel.rationalRow))
    (hl : ListRep InputAt h lp L) (hL : L.length = m)
    (hz : At h zp zero) (ho : At h op one) :
    ∃ out q, ∃ acc : List (List (BinaryRational.Word N)),
      Extends h out ∧ Valid out ∧ RowsAt out q acc ∧
      List.Forall₂ RationalWordRows.RowRep acc
        ((ComputedEmbeddedMatrices.globalRows R).map ComputedKernel.rationalRow) ∧
      Within code h (initialRegisters [.pointer rp, .pointer cp, .pointer lp, .pointer zp,
        .pointer op]) (code ids.stage) [.pointer q] out
        (stageBudget N m (4 * m) (m * m)) := by
  have hlen := faceInts_length R
  have hN' : IncrementalComplement.selectWidth (faceInts R).length m ≤ N := by
    refine le_trans ?_ hN
    unfold IncrementalComplement.selectWidth RationalWordRows.projectWidth
      RationalWordRows.elimWidth
    have h1 := Nat.mul_le_mul_right m (show (faceInts R).length + m + m + 2 * 1 ≤
      4 * m + m + m + 2 * 1 by omega)
    have h2 := Nat.mul_le_mul_right (m + 1) (show 2 + (((faceInts R).length + m + m + 2 * 1) * m
      + m ^ 2 + 1) + 1 ≤ 2 + ((4 * m + m + m + 2 * 1) * m + m ^ 2 + 1) + 1 by omega)
    have h3 := Nat.mul_le_mul_right m (show 2 + (((faceInts R).length + m + m + 2 * 1) * m
      + m ^ 2 + 1) + 1 ≤ 2 + ((4 * m + m + m + 2 * 1) * m + m ^ 2 + 1) + 1 by omega)
    omega
  rw [localRows_eq] at hrr
  obtain ⟨out, q, acc, e, v, hq, hrep, w⟩ := stage_compiled left right (faceInts R)
    (faceInts_bound R) hN' code ids d hcode InputAt inputMono hh hzr hor hrw hrr hcw hcr hl hL hz ho
  refine ⟨out, q, acc, e, v, hq, ?_, w.mono ?_⟩
  · rw [ComputedEmbeddedMatrices.globalRows, localRows_eq]
    exact hrep
  · have hc := (DeterministicKernel.candidates_spec left right).1
    unfold stageBudget RegisterEliminateRows.budget selectBudget
    gcongr

/-- The stage event bound is an explicit polynomial: degree seven in `N + m`. -/
theorem stageBudget_le (N m : ℕ) :
    stageBudget N m (4 * m) (m * m) ≤ 200000 * (N + m + 1) ^ 7 := by
  set s := N + m + 1 with hs
  have hN : N ≤ s := by omega
  have hN1 : N + 1 ≤ s := by omega
  have hm : m ≤ s := by omega
  have h1 : 1 ≤ s := by omega
  have p2 : s ≤ s ^ 2 := by nlinarith
  have p3 : s ^ 2 ≤ s ^ 3 := by nlinarith
  have p4 : s ^ 3 ≤ s ^ 4 := by nlinarith
  have p5 : s ^ 4 ≤ s ^ 5 := by nlinarith
  have p6 : s ^ 5 ≤ s ^ 6 := by nlinarith
  have p7 : s ^ 6 ≤ s ^ 7 := by nlinarith
  have hsc : RegisterStoredRational.scalarBudget N ≤ 3300 * s ^ 3 := by
    unfold RegisterStoredRational.scalarBudget; gcongr
  have hrow : RegisterRationalRow.budget N m ≤ 6673 * s ^ 4 := by
    unfold RegisterRationalRow.budget
    calc _ ≤ (2 * (3300 * s ^ 3) + 50) * s + 23 := by gcongr
      _ ≤ 6673 * s ^ 4 := by ring_nf; nlinarith
  have hsub : RegisterRationalProject.scaleSubBudget N m ≤ 6673 * s ^ 4 := by
    unfold RegisterRationalProject.scaleSubBudget
    calc _ ≤ (2 * (3300 * s ^ 3) + 50) * s + 23 := by gcongr
      _ ≤ 6673 * s ^ 4 := by ring_nf; nlinarith
  have hnz : RegisterRationalCut.nonzeroBudget N m + 30 ≤ 6873 * s ^ 4 := by
    unfold RegisterRationalCut.nonzeroBudget
    nlinarith
  have hproj : RegisterRationalProject.projectBudget N m m + 35 ≤ 16751 * s ^ 4 := by
    unfold RegisterRationalProject.projectBudget
    nlinarith
  have hcut : RegisterRationalCut.cutBudget N m m + 30 ≤ 30447 * s ^ 5 := by
    unfold RegisterRationalCut.cutBudget
    have a : (RegisterRationalCut.nonzeroBudget N m + 30) * m ≤ 6873 * s ^ 4 * s :=
      Nat.mul_le_mul hnz hm
    have b : (RegisterRationalProject.projectBudget N m m + 35) * m ≤ 16751 * s ^ 4 * s :=
      Nat.mul_le_mul hproj hm
    have e : s ^ 4 * s = s ^ 5 := by ring
    nlinarith
  have hfind : findBudget N m m ≤ 6888 * s ^ 5 := by
    unfold findBudget
    have a : (RegisterRationalCut.nonzeroBudget N m + 30) * m ≤ 6873 * s ^ 4 * s :=
      Nat.mul_le_mul hnz hm
    have e : s ^ 4 * s = s ^ 5 := by ring
    nlinarith
  have hmm : m * m ≤ s ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hm hm
  have hsel : selectBudget N m m (m * m) ≤ 37408 * s ^ 7 := by
    unfold selectBudget
    have a : (findBudget N m m + RegisterRationalCut.cutBudget N m m + 60) * (m * m) ≤
        (37395 * s ^ 5) * s ^ 2 := Nat.mul_le_mul (by nlinarith) hmm
    have e : s ^ 5 * s ^ 2 = s ^ 7 := by ring
    nlinarith
  have helim : RegisterEliminateRows.budget N m m (4 * m) ≤ 121803 * s ^ 6 := by
    unfold RegisterEliminateRows.budget
    have a : (RegisterRationalCut.cutBudget N m m + 30) * (4 * m) ≤ 30447 * s ^ 5 * (4 * s) :=
      Nat.mul_le_mul hcut (by omega)
    have e : s ^ 5 * s = s ^ 6 := by ring
    nlinarith
  have hco : RegisterIncidenceRows.coordsBudget m ≤ 177 * s ^ 2 := by
    unfold RegisterIncidenceRows.coordsBudget
    nlinarith
  unfold stageBudget
  nlinarith

end WeightedMIS.RegisterComplementSelect
