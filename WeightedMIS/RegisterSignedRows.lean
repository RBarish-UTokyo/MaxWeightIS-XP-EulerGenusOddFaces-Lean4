module

public import WeightedMIS.RegisterRationalCut
public import WeightedMIS.SignedWords
public import WeightedMIS.ComputedKernel

/-!
# Signed integer rows as stored rational rows

A signed word `(negative, magnitude)` is stored as the cell
`.bit negative magnitudePtr`. A stored rational is a record
`.pair signCell denominatorPtr` whose sign cell has exactly that layout.
Hence one `pair` allocation per entry, sharing the signed cell and a single
denominator word denoting `1`, converts a signed integer row into a stored
rational row without copying any bits. The converted words are canonical and
denote the same integers.
-/

@[expose] public section

namespace WeightedMIS.RegisterSignedRows

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer StoredRational
open RegisterRationalRow (RowAt)
open RegisterRationalCut (RowsAt)

variable {p N : ℕ}

/-- A signed integer word viewed as a rational word with denominator `one`. -/
def ratOf (one : Bits N) (g : RegisterPotentialStep.Word N) : BinaryRational.Word N :=
  ⟨g.1, g.2, one⟩

/-- Integer rows as signed words: each word denotes the coordinate. -/
def SignedRowRep {m : ℕ} (l : List (RegisterPotentialStep.Word N)) (g : Fin m → ℤ) : Prop :=
  List.Forall₂ (fun w z => RegisterPotentialStep.value w = z) l (List.ofFn g)

theorem ratOf_rep (one : Bits N) (hone : one.value = 1) (g : RegisterPotentialStep.Word N) :
    RationalWordRows.Rep (ratOf one g) (RegisterPotentialStep.value g : ℚ) := by
  have hnum : (ratOf one g).numerator = RegisterPotentialStep.value g := by
    rcases g with ⟨s, a⟩
    cases s <;> rfl
  have hval : (ratOf one g).value = (RegisterPotentialStep.value g : ℚ) := by
    unfold BinaryRational.Word.value
    rw [hnum]
    change _ / (one.value : ℚ) = _
    rw [hone]
    simp
  refine ⟨hval, ?_, ?_, ?_⟩
  · change 0 < one.value
    omega
  · rw [hval, Rat.num_intCast, ← hnum, BinaryRational.numerator_natAbs]
  · rw [hval, Rat.den_intCast]
    exact hone

theorem rowRep_of_signed {m : ℕ} (one : Bits N) (hone : one.value = 1)
    {l : List (RegisterPotentialStep.Word N)} {g : Fin m → ℤ} (h : SignedRowRep l g) :
    RationalWordRows.RowRep (l.map (ratOf one)) (ComputedKernel.rationalRow g) := by
  unfold RationalWordRows.RowRep
  have he : List.ofFn (ComputedKernel.rationalRow g) = (List.ofFn g).map (fun z : ℤ => (z : ℚ)) := by
    rw [List.map_ofFn]
    rfl
  rw [he, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h.imp (fun w z hw => by rw [← hw]; exact ratOf_rep one hone w)

theorem rowsRep_of_signed {m : ℕ} (one : Bits N) (hone : one.value = 1)
    {ls : List (List (RegisterPotentialStep.Word N))} {G : List (Fin m → ℤ)}
    (h : List.Forall₂ SignedRowRep ls G) :
    List.Forall₂ RationalWordRows.RowRep (ls.map (List.map (ratOf one)))
      (G.map ComputedKernel.rationalRow) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact h.imp (fun _ _ hl => rowRep_of_signed one hone hl)

/-! ## Register code -/

/-- Arguments 0=signed cell, 1=denominator word; returns the rational record. -/
def entryBody : Command p :=
  .allocate 2 (.pair (.register 0) (.register 1)) (.ret [.register 2])

structure Procedures (p : ℕ) where
  entry : Fin p
  row : Fin p
  rows : Fin p

structure Procedures.Matches (ids : Procedures p) (code : Code p) : Prop where
  entry : code ids.entry = entryBody
  row : code ids.row = RegisterListMap.body ids.row ids.entry
  rows : code ids.rows = RegisterListMap.body ids.rows ids.row

theorem entry_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {sp dp : Ptr} {g : RegisterPotentialStep.Word N} {one : Bits N}
    (hg : SignedWords.SignedAt h sp g) (hd : BitsAt h dp one) :
    ∃ out q, Extends h out ∧ Valid out ∧ At out q (ratOf one g) ∧
      Within code h (initialRegisters [.pointer sp, .pointer dp]) (code ids.entry)
        [.pointer q] out 11 := by
  obtain ⟨e, v, cell⟩ := RegisterRationalCut.allocate_pair hh (SignedWords.SignedAt.allocated hg)
    hd.allocated
  obtain ⟨np, bit, num⟩ := hg
  refine ⟨h ++ [.pair sp dp], h.length, e, v,
    ⟨sp, np, dp, cell, e.lookup bit, num.mono e, hd.mono e⟩, ?_⟩
  rw [hcode.entry]
  apply Within.allocate (budget := 3) (c := .pair sp dp)
  · simp [CellExpr.eval, Atom.eval, initialRegisters, Value.asPointer]
  · simpa [values, Atom.eval] using
      Within.ret code (h ++ [.pair sp dp])
        (Function.update (initialRegisters [.pointer sp, .pointer dp]) 2 (.pointer h.length))
        [.register 2]

def rowBudget (m : ℕ) : ℕ := 46 * m + 13

theorem row_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {lp dp : Ptr} {l : List (RegisterPotentialStep.Word N)}
    {one : Bits N} (hl : SignedWords.ListAt h lp l) (hd : BitsAt h dp one) :
    ∃ out q, Extends h out ∧ Valid out ∧ RowAt out q (l.map (ratOf one)) ∧
      Within code h (initialRegisters [.pointer lp, .pointer dp]) (code ids.row)
        [.pointer q] out (rowBudget l.length) := by
  obtain ⟨out, q, e, v, hq, w⟩ := RegisterListMap.compiled_const code ids.row ids.entry
    hcode.row (fun heap ptr (g : RegisterPotentialStep.Word N) => SignedWords.SignedAt heap ptr g)
    (fun heap ptr (w : Bits N) => BitsAt heap ptr w)
    (fun heap ptr (q : BinaryRational.Word N) => At heap ptr q)
    (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
    (fun ext _ _ hx => hx.mono ext) (fun _ hx => hx.allocated) (fun one g => ratOf one g) 11
    hh hl hd (fun {_} hv {_} {_} _ hx hd' => entry_compiled code ids hcode hv hx hd')
  exact ⟨out, q, e, v, hq, w.mono (by simp [rowBudget])⟩

/-- Convert a list of signed rows of length `m` into stored rational rows. -/
theorem rows_compiled (code : Code p) (ids : Procedures p) (hcode : ids.Matches code)
    {h : Heap} (hh : Valid h) {lp dp : Ptr} {m : ℕ}
    {ls : List (List (RegisterPotentialStep.Word N))} {one : Bits N}
    (hl : ListRep (fun heap ptr l => SignedWords.ListAt heap ptr l) h lp ls)
    (hd : BitsAt h dp one) (hlen : ∀ l ∈ ls, l.length = m) :
    ∃ out q, Extends h out ∧ Valid out ∧ RowsAt out q (ls.map (List.map (ratOf one))) ∧
      Within code h (initialRegisters [.pointer lp, .pointer dp]) (code ids.rows)
        [.pointer q] out ((rowBudget m + 35) * ls.length + 13) :=
  RegisterListMap.compiled_const code ids.rows ids.row hcode.rows
    (fun heap ptr l => SignedWords.ListAt heap ptr l) (fun heap ptr (w : Bits N) => BitsAt heap ptr w)
    (fun heap ptr (row : List (BinaryRational.Word N)) => RowAt heap ptr row)
    (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
    (fun ext _ _ hx => hx.mono ext) (fun _ hx => ListRep.allocated hx)
    (fun one l => l.map (ratOf one)) (rowBudget m) hh hl hd
    (fun {_} hv {_} {_} hmem hx hd' => by
      obtain ⟨o, q, e, v, hq, w⟩ := row_compiled code ids hcode hv hx hd'
      exact ⟨o, q, e, v, hq, by simpa [hlen _ hmem] using w⟩)

end WeightedMIS.RegisterSignedRows
