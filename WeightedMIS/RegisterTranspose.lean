module

public import WeightedMIS.RegisterComplementSelect
public import WeightedMIS.RegisterResize

/-!
# Compiled transposition of the selected complement rows

The selected rows are stored rational rows with small integer entries. A
stored rational is the record `.pair signCell denominator` whose sign cell
`.bit negative magnitude` already has the layout of a signed delta word, so
every entry is converted by the compiled signed resize to the delta width `k`.

The transposition walks a length witness with `m` items. For every item it
maps the head conversion over the remaining rows (one column), maps the tail
selection over the rows, and recurses. The output is the list of `m` delta
lists, one per edge. A second map produces the dimension shape list, one copy
of the shape word per selected row. With the selected rows denoting
`ComputedEmbeddedMatrices.globalRows R`, the delta values are exactly
`ComputedEmbeddedMatrices.globalColumn R`.
-/

@[expose] public section

namespace WeightedMIS.RegisterTranspose

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer StoredRational
open ExpandedWords
open RegisterRationalRow (RowAt)
open RegisterRationalCut (RowsAt)

variable {p N : ℕ}

/-! ## Reference functions -/

/-- The sign cell of a stored rational, read as a signed word of width `k`. -/
def signedOf (k : ℕ) (q : BinaryRational.Word N) : SignedWord k :=
  SignedWord.resizeTo k ⟨q.negative, q.magnitude⟩

/-- Conversion of the first entry of a row. -/
def headSigned (k : ℕ) : List (BinaryRational.Word N) → SignedWord k
  | [] => ⟨false, Bits.zero k⟩
  | q :: _ => signedOf k q

/-- The first `j` columns of a row list, as converted signed words. -/
def columnsW (k : ℕ) : ℕ → List (List (BinaryRational.Word N)) → List (List (SignedWord k))
  | 0, _ => []
  | j + 1, rows => rows.map (headSigned k) :: columnsW k j (rows.map List.tail)

/-- The first `j` columns of a list of integer lists. -/
def transposeZ : ℕ → List (List ℤ) → List (List ℤ)
  | 0, _ => []
  | j + 1, zss => zss.map (fun zs => zs.headD 0) :: transposeZ j (zss.map List.tail)

/-- A word row denoting a list of integers. -/
def IntRow (r : List (BinaryRational.Word N)) (zs : List ℤ) : Prop :=
  List.Forall₂ (fun q (z : ℤ) => RationalWordRows.Rep q (z : ℚ)) r zs

theorem intRow_of_rowRep {m : ℕ} {r : List (BinaryRational.Word N)} {g : Fin m → ℤ}
    (h : RationalWordRows.RowRep r (ComputedKernel.rationalRow g)) : IntRow r (List.ofFn g) := by
  unfold RationalWordRows.RowRep at h
  have he : List.ofFn (ComputedKernel.rationalRow g) = (List.ofFn g).map (fun z : ℤ => (z : ℚ)) := by
    rw [List.map_ofFn]
    rfl
  rw [he, List.forall₂_map_right_iff] at h
  exact h

theorem signedOf_value (k : ℕ) {q : BinaryRational.Word N} {z : ℤ}
    (hq : RationalWordRows.Rep q (z : ℚ)) (hz : z.natAbs < 2 ^ k) : (signedOf k q).value = z := by
  obtain ⟨hv, _, hmag, hden⟩ := hq
  have hden1 : q.denominator.value = 1 := by
    rw [hden, hv]
    simp
  have hnum : q.numerator = z := by
    have h := hv
    unfold BinaryRational.Word.value at h
    rw [hden1] at h
    exact_mod_cast (by simpa using h)
  have hmz : q.magnitude.value = z.natAbs := by
    rw [← BinaryRational.numerator_natAbs, hnum]
  unfold signedOf
  rw [SignedWord.resizeTo_value _ (by rw [hmz]; exact hz)]
  rw [← hnum]
  rfl

theorem columnsW_value (k : ℕ) :
    ∀ (j : ℕ) (rows : List (List (BinaryRational.Word N))) (zss : List (List ℤ)),
      List.Forall₂ IntRow rows zss → (∀ zs ∈ zss, ∀ z ∈ zs, z.natAbs < 2 ^ k) →
      (columnsW k j rows).map (List.map SignedWord.value) = transposeZ j zss := by
  intro j
  induction j with
  | zero => intro _ _ _ _; rfl
  | succ j ih =>
    intro rows zss hrel hb
    simp only [columnsW, transposeZ, List.map_cons, List.cons.injEq]
    constructor
    · rw [List.map_map]
      clear ih
      induction hrel with
      | nil => rfl
      | @cons r zs rows zss hr _ ihr =>
        simp only [List.map_cons, List.cons.injEq]
        refine ⟨?_, ihr (fun zs' hzs' => hb zs' (List.mem_cons_of_mem _ hzs'))⟩
        cases hr with
        | nil => simp [headSigned, SignedWord.value]
        | @cons q z qs zt hqz _ =>
          exact signedOf_value k hqz (hb (z :: zt) List.mem_cons_self z List.mem_cons_self)
    · apply ih
      · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact hrel.imp (fun r zs h => by
          cases h with
          | nil => exact .nil
          | cons _ ht => exact ht)
      · intro zs hzs z hz
        obtain ⟨zs0, hzs0, rfl⟩ := List.mem_map.mp hzs
        exact hb zs0 hzs0 z (List.mem_of_mem_tail hz)

theorem transposeZ_ofFn : ∀ (j : ℕ) (W : List (Fin j → ℤ)),
    transposeZ j (W.map List.ofFn) = List.ofFn (fun e : Fin j => W.map (fun g => g e)) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro W
    rw [transposeZ, List.ofFn_succ]
    congr 1
    · simp [List.map_map, Function.comp_def, List.ofFn_succ]
    · have ht : (W.map List.ofFn).map List.tail =
          (W.map (fun g : Fin (j + 1) → ℤ => fun i : Fin j => g i.succ)).map List.ofFn := by
        simp [List.map_map, Function.comp_def, List.ofFn_succ]
      rw [ht, ih]
      simp [List.map_map, Function.comp_def]

/-- Columns of word rows denoting integer rows, as signed values. -/
theorem columnsW_rows {m : ℕ} (k : ℕ) (W : List (Fin m → ℤ)) (hW : ∀ g ∈ W, ∀ e, (g e).natAbs < 2 ^ k)
    (rows : List (List (BinaryRational.Word N)))
    (hrows : List.Forall₂ RationalWordRows.RowRep rows (W.map ComputedKernel.rationalRow)) :
    (columnsW k m rows).map (List.map SignedWord.value) =
      List.ofFn (fun e : Fin m => W.map (fun g => g e)) := by
  rw [← transposeZ_ofFn]
  apply columnsW_value
  · rw [List.forall₂_map_right_iff] at hrows
    rw [List.forall₂_map_right_iff]
    exact hrows.imp (fun _ _ h => intRow_of_rowRep h)
  · intro zs hzs z hz
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hzs
    obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hz
    exact hW g hg e

theorem columnsW_length (k j : ℕ) (rows : List (List (BinaryRational.Word N))) :
    (columnsW k j rows).length = j := by
  induction j generalizing rows with
  | zero => rfl
  | succ j ih => simp [columnsW, ih]

/-! ## Register code -/

/-- Arguments 0=row, 1=shape word; result is the converted first entry. -/
def headBody (signed : Fin p) : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with
    cons := .load (.register 2) 4 5 15 { CompiledTrie.failCases with
      pair := .call signed [.register 4, .register 1] [6] (.ret [.register 6]) } }

/-- Arguments 0=row, 1=unused data; result is the tail of the row. -/
def tailBody : Command p :=
  .load (.register 0) 2 3 15 { CompiledTrie.failCases with cons := .ret [.register 3] }

/-- Arguments 0=length witness, 1=rows, 2=shape word; result is the column list. -/
def transposeBody (self heads tails : Fin p) : Command p :=
  .load (.register 0) 3 4 15 { CompiledTrie.failCases with
    nil := .ret [.null]
    cons := .call heads [.register 1, .register 2] [5]
      (.call tails [.register 1, .register 2] [6]
        (.call self [.register 4, .register 6, .register 2] [7]
          (.allocate 8 (.cons (.register 5) (.register 7)) (.ret [.register 8])))) }

/-- Arguments 0=length witness, 1=rows, 2=shape word; results are the column
list and the dimension shape list. -/
def stageBody (transpose shape : Fin p) : Command p :=
  .call transpose [.register 0, .register 1, .register 2] [3]
    (.call shape [.register 1, .register 2] [4] (.ret [.register 3, .register 4]))

structure Procedures (p : ℕ) where
  resize : RegisterResize.Procedures p
  signed : Fin p
  head : Fin p
  heads : Fin p
  tail : Fin p
  tails : Fin p
  transpose : Fin p
  constItem : Fin p
  shape : Fin p
  stage : Fin p

structure Procedures.Matches (ids : Procedures p) (code : Code p) : Prop where
  resize : ids.resize.Matches code
  signed : code ids.signed = RegisterResize.signedBody ids.resize.resize
  head : code ids.head = headBody ids.signed
  heads : code ids.heads = RegisterListMap.body ids.heads ids.head
  tail : code ids.tail = tailBody
  tails : code ids.tails = RegisterListMap.body ids.tails ids.tail
  transpose : code ids.transpose = transposeBody ids.transpose ids.heads ids.tails
  constItem : code ids.constItem = RegisterIncidenceRows.constBody
  shape : code ids.shape = RegisterListMap.body ids.shape ids.constItem
  stage : code ids.stage = stageBody ids.transpose ids.shape

def headBudget (N k : ℕ) : ℕ := RegisterResize.signedBudget k N + 28

theorem head_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {rp sp : Ptr} {k : ℕ} {row : List (BinaryRational.Word N)}
    {s : Bits k} (hrow : RowAt h rp row) (hne : row ≠ []) (hs : BitsAt h sp s) :
    ∃ out q, Extends h out ∧ Valid out ∧ SignedAt out q (headSigned k row) ∧
      Within code h (initialRegisters [.pointer rp, .pointer sp]) (code ids.head)
        [.pointer q] out (headBudget N k) := by
  obtain ⟨ps, hlist, hrel⟩ := hrow
  cases row with
  | nil => exact absurd rfl hne
  | cons x xs =>
  cases hrel with
  | @cons ap _ _ _ hx _ =>
  cases hlist with
  | @cons _ _ rest _ cell _ =>
  obtain ⟨sgn, np, dp, pair, bit, num, _⟩ := hx
  have hd : SignedAt h sgn (⟨x.negative, x.magnitude⟩ : SignedWord N) := ⟨np, bit, num⟩
  obtain ⟨out, q, e, v, hq, run⟩ := RegisterResize.signed_compiled code ids.resize
    hcode.resize ids.signed hcode.signed hh hd hs
  refine ⟨out, q, e, v, hq, ?_⟩
  let r0 := initialRegisters [Value.pointer rp, .pointer sp]
  let r1 := loadRegisters r0 2 3 15 (.cons ap rest)
  let r2 := loadRegisters r1 4 5 15 (.pair sgn dp)
  let r3 := bindResults r2 [6] [Value.pointer q]
  have last : Within code out r3 (.ret [.register 6]) [.pointer q] out 3 := by
    simpa [r3, bindResults, values, Atom.eval] using Within.ret code out r3 [.register 6]
  have sArgs : values r2 [.register 4, .register 1] = [.pointer sgn, .pointer sp] := by
    simp [r2, r1, r0, loadRegisters, decoded, initialRegisters, values, Atom.eval]
  have sCall := Within.call (procedure := ids.signed) (arguments := [.register 4, .register 1])
    (results := [6]) (regs := r2) (by simpa only [sArgs] using run) last
  have l2 := Within.load (regs := r1) (address := .register 2) (first := 4) (second := 5)
    (bit := 15) (branches := { CompiledTrie.failCases with
      pair := .call ids.signed [.register 4, .register 1] [6] (.ret [.register 6]) })
    (by simp [r1, r0, loadRegisters, decoded, Atom.eval]) pair sCall
  have l1 := Within.load (regs := r0) (address := .register 0) (first := 2) (second := 3)
    (bit := 15) (branches := { CompiledTrie.failCases with
      cons := .load (.register 2) 4 5 15 { CompiledTrie.failCases with
        pair := .call ids.signed [.register 4, .register 1] [6] (.ret [.register 6]) } })
    (by simp [r0, initialRegisters, Atom.eval]) cell l2
  rw [hcode.head]
  refine l1.mono ?_
  simp only [headBudget, List.length_cons, List.length_nil]
  omega

theorem tail_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {rp sp : Ptr} {row : List (BinaryRational.Word N)}
    (hrow : RowAt h rp row) (hne : row ≠ []) :
    ∃ out q, Extends h out ∧ Valid out ∧ RowAt out q row.tail ∧
      Within code h (initialRegisters [.pointer rp, .pointer sp]) (code ids.tail)
        [.pointer q] out 13 := by
  obtain ⟨ps, hlist, hrel⟩ := hrow
  cases row with
  | nil => exact absurd rfl hne
  | cons x xs =>
  cases hrel with
  | @cons ap _ pt _ _ hxs =>
  cases hlist with
  | @cons _ _ rest _ cell hrest =>
  refine ⟨h, rest, .refl h, hh, ⟨pt, hrest, hxs⟩, ?_⟩
  let r0 := initialRegisters [Value.pointer rp, .pointer sp]
  let r1 := loadRegisters r0 2 3 15 (.cons ap rest)
  have last : Within code h r1 (.ret [.register 3]) [.pointer rest] h 3 := by
    simpa [r1, r0, loadRegisters, decoded, initialRegisters, values, Atom.eval] using
      Within.ret code h r1 [.register 3]
  have l1 := Within.load (regs := r0) (address := .register 0) (first := 2) (second := 3)
    (bit := 15) (branches := { CompiledTrie.failCases with cons := .ret [.register 3] })
    (by simp [r0, initialRegisters, Atom.eval]) cell last
  rw [hcode.tail]
  exact l1

/-- Events of the transposition of `d` rows into `j` columns. -/
def transposeBudget (N k d j : ℕ) : ℕ :=
  ((headBudget N k + 35) * d + 48 * d + 70) * j + 13

theorem transpose_compiled {α : Type*} (code : Code p) (ids : Procedures p)
    (hcode : ids.Matches code) (InputAt : Heap → Ptr → α → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    {k : ℕ} {s : Bits k} :
    ∀ (L : List α) {h : Heap} {lp rp sp : Ptr} {rows : List (List (BinaryRational.Word N))},
      Valid h → ListRep InputAt h lp L → RowsAt h rp rows → BitsAt h sp s →
      (∀ r ∈ rows, r.length = L.length) →
      ∃ out q, Extends h out ∧ Valid out ∧
        ListRep (fun heap ptr ds => DeltasAt heap ptr ds) out q (columnsW k L.length rows) ∧
        Within code h (initialRegisters [.pointer lp, .pointer rp, .pointer sp])
          (code ids.transpose) [.pointer q] out (transposeBudget N k rows.length L.length) := by
  intro L
  induction L with
  | nil =>
    intro h lp rp sp rows hh hl _ _ _
    obtain ⟨pointers, hlist, hrel⟩ := hl
    cases hrel
    cases hlist with
    | nil cell =>
      refine ⟨h, 0, .refl h, hh, RegisterListCommon.listRep_null hh, ?_⟩
      rw [hcode.transpose]
      unfold transposeBody
      apply Within.load (budget := 3) (pointer := lp) (c := .nil)
      · simp [Atom.eval, initialRegisters]
      · exact cell
      · simpa [values, Atom.eval, Cases.select, transposeBudget] using
          Within.ret code h
            (loadRegisters (initialRegisters [.pointer lp, .pointer rp, .pointer sp]) 3 4 15 .nil)
            [.null]
  | cons x xs ih =>
    intro h lp rp sp rows hh hl hrows hs hlen
    obtain ⟨pointers, hlist, hrel⟩ := hl
    cases hrel with
    | @cons xp _ ps _ _ hxs =>
    cases hlist with
    | @cons _ _ rest _ cell hrest =>
    have hne : ∀ r ∈ rows, r ≠ [] := by
      intro r hr hnil
      have := hlen r hr
      rw [hnil] at this
      simp at this
    -- one column
    obtain ⟨h1, cp, e1, v1, hcol, headed⟩ := RegisterListMap.compiled_const code ids.heads
      ids.head hcode.heads RowAt (fun heap ptr (w : Bits k) => BitsAt heap ptr w)
      (fun heap ptr (d : SignedWord k) => SignedAt heap ptr d)
      (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
      (fun ext _ _ hx => hx.mono ext) (fun _ hx => hx.allocated)
      (fun _ row => headSigned k row) (headBudget N k) hh hrows hs
      (fun {_} hv {_} {_} hmem hx hd => head_compiled code ids hcode hv hx (hne _ hmem) hd)
    -- the remaining rows
    obtain ⟨h2, tp, e2, v2, htails, tailed⟩ := RegisterListMap.compiled_const code ids.tails
      ids.tail hcode.tails RowAt (fun heap ptr (w : Bits k) => BitsAt heap ptr w) RowAt
      (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
      (fun ext _ _ hx => hx.mono ext) (fun _ hx => ListRep.allocated hx)
      (fun _ row => row.tail) 13 v1 (hrows.mono e1) (hs.mono e1)
      (fun {_} hv {_} {_} hmem hx _ => tail_compiled code ids hcode hv hx (hne _ hmem))
    have e12 := e1.trans e2
    have htl : ∀ r ∈ rows.map List.tail, r.length = xs.length := by
      intro r hr
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
      have := hlen r0 hr0
      simp only [List.length_tail, this, List.length_cons, Nat.add_sub_cancel]
    obtain ⟨h3, rq, e3, v3, hrq, recursed⟩ := ih v2
      ⟨ps, hrest.mono e12, hxs.imp (fun _ _ h => inputMono e12 _ _ h)⟩ htails (hs.mono e12) htl
    have e13 := e12.trans e3
    have hcol3 : DeltasAt h3 cp (rows.map (headSigned k)) := DeltasAt.mono (e2.trans e3) hcol
    obtain ⟨e4, v4, hres⟩ := RegisterListCommon.allocate_consRep
      (R := fun heap ptr (ds : List (SignedWord k)) => DeltasAt heap ptr ds)
      (fun ext _ _ hq => DeltasAt.mono ext hq) v3 hcol3 (ListRep.allocated hcol3) hrq
    refine ⟨h3 ++ [.cons cp rq], h3.length, e13.trans e4, v4,
      by simpa only [List.length_cons, columnsW] using hres, ?_⟩
    let r0 := initialRegisters [Value.pointer lp, .pointer rp, .pointer sp]
    let rl := loadRegisters r0 3 4 15 (.cons xp rest)
    let r1 := bindResults rl [5] [Value.pointer cp]
    let r2 := bindResults r1 [6] [Value.pointer tp]
    let r3 := bindResults r2 [7] [Value.pointer rq]
    have last := RegisterListCommon.within_consRet code h3 (regs := r3) (dst := 8)
      (head := 5) (tail := 7) (a := cp) (t := rq)
      (by simp [r3, r2, r1, bindResults]) (by simp [r3, bindResults])
    have sArgs : values r2 [.register 4, .register 6, .register 2] =
        [.pointer rest, .pointer tp, .pointer sp] := by
      simp [r2, r1, rl, r0, bindResults, loadRegisters, decoded, initialRegisters, values,
        Atom.eval]
    have sCall := Within.call (procedure := ids.transpose)
      (arguments := [.register 4, .register 6, .register 2]) (results := [7]) (regs := r2)
      (by simpa only [sArgs] using recursed) last
    have tArgs : values r1 [.register 1, .register 2] = [.pointer rp, .pointer sp] := by
      simp [r1, rl, r0, bindResults, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have tCall := Within.call (procedure := ids.tails) (arguments := [.register 1, .register 2])
      (results := [6]) (regs := r1) (by simpa only [tArgs] using tailed) sCall
    have hArgs : values rl [.register 1, .register 2] = [.pointer rp, .pointer sp] := by
      simp [rl, r0, loadRegisters, decoded, initialRegisters, values, Atom.eval]
    have hCall := Within.call (procedure := ids.heads) (arguments := [.register 1, .register 2])
      (results := [5]) (regs := rl) (by simpa only [hArgs] using headed) tCall
    have loaded := Within.load (regs := r0) (address := .register 0) (first := 3) (second := 4)
      (bit := 15) (branches := { CompiledTrie.failCases with
        nil := .ret [.null]
        cons := .call ids.heads [.register 1, .register 2] [5]
          (.call ids.tails [.register 1, .register 2] [6]
            (.call ids.transpose [.register 4, .register 6, .register 2] [7]
              (.allocate 8 (.cons (.register 5) (.register 7)) (.ret [.register 8])))) })
      (by simp [r0, initialRegisters, Atom.eval]) cell hCall
    rw [hcode.transpose]
    refine loaded.mono ?_
    simp only [transposeBudget, List.length_map, List.length_cons, List.length_nil]
    ring_nf
    omega

/-- Events of the dimension shape list for `d` rows. -/
def shapeBudget (d : ℕ) : ℕ := 38 * d + 13

theorem shape_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {rp sp : Ptr} {k : ℕ} {rows : List (List (BinaryRational.Word N))}
    {s : Bits k} (hrows : RowsAt h rp rows) (hs : BitsAt h sp s) :
    ∃ out q, Extends h out ∧ Valid out ∧ WordsAt out q (List.replicate rows.length s) ∧
      Within code h (initialRegisters [.pointer rp, .pointer sp]) (code ids.shape)
        [.pointer q] out (shapeBudget rows.length) := by
  obtain ⟨out, q, e, v, hq, w⟩ := RegisterListMap.compiled_const code ids.shape ids.constItem
    hcode.shape RowAt (fun heap ptr (w : Bits k) => BitsAt heap ptr w)
    (fun heap ptr (w : Bits k) => BitsAt heap ptr w)
    (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
    (fun ext _ _ hx => hx.mono ext) (fun _ hx => hx.allocated) (fun s _ => s) 3 hh hrows hs
    (fun {h'} hv' {xp} {_} _ _ hd => by
      refine ⟨h', sp, .refl h', hv', hd, ?_⟩
      rw [hcode.constItem]
      simpa [RegisterIncidenceRows.constBody, values, Atom.eval, initialRegisters] using
        Within.ret code h' (initialRegisters [.pointer xp, .pointer sp]) [.register 1])
  refine ⟨out, q, e, v, ?_, w.mono (by simp [shapeBudget])⟩
  have h0 := hq
  rw [List.map_const'] at h0
  exact h0

/-- Events of the whole transposition stage. -/
def stageBudget (N k d m : ℕ) : ℕ := transposeBudget N k d m + shapeBudget d + 20

theorem stage_compiled_words {α : Type*} (code : Code p) (ids : Procedures p)
    (hcode : ids.Matches code) (InputAt : Heap → Ptr → α → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    {h : Heap} (hh : Valid h) {lp rp sp : Ptr} {k : ℕ} {L : List α}
    {rows : List (List (BinaryRational.Word N))} {s : Bits k}
    (hl : ListRep InputAt h lp L) (hrows : RowsAt h rp rows) (hs : BitsAt h sp s)
    (hlen : ∀ r ∈ rows, r.length = L.length) :
    ∃ out q1 q2, Extends h out ∧ Valid out ∧
      ListRep (fun heap ptr ds => DeltasAt heap ptr ds) out q1 (columnsW k L.length rows) ∧
      WordsAt out q2 (List.replicate rows.length s) ∧
      Within code h (initialRegisters [.pointer lp, .pointer rp, .pointer sp])
        (code ids.stage) [.pointer q1, .pointer q2] out
        (stageBudget N k rows.length L.length) := by
  obtain ⟨h1, q1, e1, v1, hq1, transposed⟩ :=
    transpose_compiled code ids hcode InputAt inputMono L hh hl hrows hs hlen
  obtain ⟨out, q2, e2, v2, hq2, shaped⟩ :=
    shape_compiled code ids hcode v1 (hrows.mono e1) (hs.mono e1)
  refine ⟨out, q1, q2, e1.trans e2, v2,
    ListRep.mono e2 (fun _ _ hx => DeltasAt.mono e2 hx) hq1, hq2, ?_⟩
  let r0 := initialRegisters [Value.pointer lp, .pointer rp, .pointer sp]
  let r1 := bindResults r0 [3] [Value.pointer q1]
  let r2 := bindResults r1 [4] [Value.pointer q2]
  have last : Within code out r2 (.ret [.register 3, .register 4]) [.pointer q1, .pointer q2]
      out 5 := by
    simpa [r2, r1, bindResults, values, Atom.eval] using
      Within.ret code out r2 [.register 3, .register 4]
  have sArgs : values r1 [.register 1, .register 2] = [.pointer rp, .pointer sp] := by
    simp [r1, r0, bindResults, initialRegisters, values, Atom.eval]
  have sCall := Within.call (procedure := ids.shape) (arguments := [.register 1, .register 2])
    (results := [4]) (regs := r1) (by simpa only [sArgs] using shaped) last
  have tArgs : values r0 [.register 0, .register 1, .register 2] =
      [.pointer lp, .pointer rp, .pointer sp] := by
    simp [r0, initialRegisters, values, Atom.eval]
  have tCall := Within.call (procedure := ids.transpose)
    (arguments := [.register 0, .register 1, .register 2]) (results := [3]) (regs := r0)
    (by simpa only [tArgs] using transposed) sCall
  rw [hcode.stage]
  refine tCall.mono ?_
  simp only [stageBudget, List.length_cons, List.length_nil]
  omega

theorem ofFn_globalColumn {n m : ℕ} {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) (e : Fin m) :
    List.ofFn (ComputedEmbeddedMatrices.globalColumn R e) =
      (ComputedEmbeddedMatrices.globalRows R).map (fun g => g e) := by
  unfold ComputedEmbeddedMatrices.globalColumn
  conv_rhs => rw [← List.ofFn_get (ComputedEmbeddedMatrices.globalRows R)]
  rw [List.map_ofFn]
  rfl

/-- From stored rows denoting `globalRows R`, the compiled stage produces one
delta list per edge whose signed values are exactly `globalColumn R e`, and a
shape list with one entry per selected row. -/
theorem global_compiled {α : Type*} {n m : ℕ} {left right : Fin m → Fin n}
    (R : EmbeddingFaces.Ribbon left right) (code : Code p) (ids : Procedures p)
    (hcode : ids.Matches code) (InputAt : Heap → Ptr → α → Prop)
    (inputMono : ∀ {h h' : Heap}, Extends h h' → ∀ ptr x, InputAt h ptr x → InputAt h' ptr x)
    {h : Heap} (hh : Valid h) {lp rp sp : Ptr} {k : ℕ} (hk : 2 ≤ k) {L : List α}
    {rows : List (List (BinaryRational.Word N))} {s : Bits k}
    (hl : ListRep InputAt h lp L) (hL : L.length = m) (hrows : RowsAt h rp rows)
    (hrep : List.Forall₂ RationalWordRows.RowRep rows
      ((ComputedEmbeddedMatrices.globalRows R).map ComputedKernel.rationalRow))
    (hs : BitsAt h sp s) :
    ∃ out q1 q2, ∃ cols : List (List (SignedWord k)), Extends h out ∧ Valid out ∧
      ListRep (fun heap ptr ds => DeltasAt heap ptr ds) out q1 cols ∧
      cols.map (List.map SignedWord.value) =
        List.ofFn (fun e => List.ofFn (ComputedEmbeddedMatrices.globalColumn R e)) ∧
      WordsAt out q2 (List.replicate (ComputedEmbeddedMatrices.globalRows R).length s) ∧
      Within code h (initialRegisters [.pointer lp, .pointer rp, .pointer sp])
        (code ids.stage) [.pointer q1, .pointer q2] out
        (stageBudget N k (ComputedEmbeddedMatrices.globalRows R).length m) := by
  subst hL
  have hlen : ∀ r ∈ rows, r.length = L.length := by
    intro r hr
    obtain ⟨x, _, hx⟩ := RationalWordRows.forall₂_mem_left hrep hr
    exact RationalWordRows.rowRep_length hx
  have hd : rows.length = (ComputedEmbeddedMatrices.globalRows R).length := by
    simpa using hrep.length_eq
  obtain ⟨out, q1, q2, e, v, hq1, hq2, w⟩ :=
    stage_compiled_words code ids hcode InputAt inputMono hh hl hrows hs hlen
  refine ⟨out, q1, q2, _, e, v, hq1, ?_, by simpa only [hd] using hq2,
    by simpa only [hd] using w⟩
  have hb : ∀ g ∈ ComputedEmbeddedMatrices.globalRows R, ∀ e, (g e).natAbs < 2 ^ k := by
    intro g hg e
    have hg' : g ∈ DeterministicKernel.candidates left right :=
      (ComputedKernel.selectInteger_sublist _ _).subset hg
    have h2 := ((DeterministicKernel.candidates_spec left right).2.1 g hg').2 e
    rw [Int.abs_eq_natAbs] at h2
    have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  rw [columnsW_rows k _ hb rows hrep]
  congr 1
  funext e
  rw [ofFn_globalColumn]

/-- The transposition stage bound is an explicit cubic polynomial. -/
theorem stageBudget_le (N k d m : ℕ) :
    stageBudget N k d m ≤ 400 * (N + k + d + m + 1) ^ 3 := by
  unfold stageBudget transposeBudget shapeBudget headBudget RegisterResize.signedBudget
    RegisterResize.resizeBudget
  set s := N + k + d + m + 1 with hs
  have hd : d ≤ s := by omega
  have hm : m ≤ s := by omega
  have hA : 60 * k + 30 * N + 60 + 30 + 28 + 35 ≤ 153 * s := by omega
  have hB : (60 * k + 30 * N + 60 + 30 + 28 + 35) * d + 48 * d + 70 ≤ 153 * s * s + 48 * s + 70 := by
    have := Nat.mul_le_mul hA hd
    omega
  have hC : ((60 * k + 30 * N + 60 + 30 + 28 + 35) * d + 48 * d + 70) * m ≤
      (153 * s * s + 48 * s + 70) * s := Nat.mul_le_mul hB hm
  have h1 : 1 ≤ s := by omega
  have hs3 : s ^ 3 = s * s * s := by ring
  have hss : s ≤ s * s := Nat.le_mul_of_pos_right _ (by omega)
  have hsss : s * s ≤ s * s * s := Nat.le_mul_of_pos_right _ (by omega)
  rw [hs3]
  nlinarith

end WeightedMIS.RegisterTranspose
