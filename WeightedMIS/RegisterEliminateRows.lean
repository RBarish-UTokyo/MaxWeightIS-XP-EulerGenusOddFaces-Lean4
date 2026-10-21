module

public import WeightedMIS.RegisterRationalCut
public import WeightedMIS.RegisterListFold

/-!
# Compiled outer constraint-elimination loop

A left fold over the stored constraint rows calls the compiled `cut`
procedure with the shared zero record as fold data and the current stored
vector list as fold state. The output is exactly
`RationalWordRows.eliminateRowsW`, with an event bound polynomial in the
word width, the vector length, and the numbers of rows and vectors.
-/

@[expose] public section

namespace WeightedMIS.RegisterEliminateRows

open PointerMemory RegisterMachine EfficientSearch EfficientSearch.Pointer StoredRational
open RegisterRationalRow (RowAt)
open RegisterRationalCut (RowsAt)

variable {p N : ℕ}

structure Procedures (p : ℕ) where
  cut : RegisterRationalCut.Procedures p
  fold : Fin p

structure Procedures.Matches (ids : Procedures p) (code : Code p)
    (d : RegisterRationalProducts.Procedures p) : Prop where
  cut : ids.cut.Matches code d
  fold : code ids.fold = RegisterListFold.body ids.fold ids.cut.cut

/-- Event bound for `rows` constraint rows acting on `k` vectors of length `m`. -/
def budget (N m k rows : ℕ) : ℕ :=
  (RegisterRationalCut.cutBudget N m k + 30) * rows + 15

/-- Arguments 0=constraint rows, 1=zero record, 2=vector list. -/
theorem compiled (code : Code p) (ids : Procedures p)
    (d : RegisterRationalProducts.Procedures p) (hcode : ids.Matches code d)
    {h : Heap} (hh : Valid h) {csp zp vsp : Ptr} {m : ℕ}
    {cs vs : List (List (BinaryRational.Word N))} {zero : BinaryRational.Word N}
    (hcs : RowsAt h csp cs) (hz : At h zp zero) (hvs : RowsAt h vsp vs)
    (hcl : ∀ c ∈ cs, c.length = m) (hvl : ∀ v ∈ vs, v.length = m) :
    ∃ out result, Extends h out ∧ Valid out ∧
      RowsAt out result (RationalWordRows.eliminateRowsW zero cs vs) ∧
      Within code h (initialRegisters [.pointer csp, .pointer zp, .pointer vsp])
        (code ids.fold) [.pointer result] out (budget N m vs.length cs.length) := by
  let StateAt : Heap → Ptr → List (List (BinaryRational.Word N)) → Prop :=
    fun heap ptr s => RowsAt heap ptr s ∧ (∀ v ∈ s, v.length = m) ∧ s.length = vs.length
  obtain ⟨out, result, e, vo, hstate, w⟩ := RegisterListFold.compiled_const code ids.fold
    ids.cut.cut hcode.fold RowAt At StateAt
    (fun ext _ _ hx => hx.mono ext) (fun ext _ _ hx => hx.mono ext)
    (fun zero s c => RationalWordRows.cutW zero c s)
    (RegisterRationalCut.cutBudget N m vs.length) hh hcs hz ⟨hvs, hvl, rfl⟩
    (fun pre x post hsplit {_} hv {_} {_} hx hzero hs => by
      have hxm : x ∈ cs := by rw [hsplit]; simp
      obtain ⟨o, r, e, vo, hr, w⟩ := RegisterRationalCut.cut_compiled code ids.cut d
        hcode.cut hv hx hzero hs.1 (hcl x hxm) hs.2.1
      refine ⟨o, r, e, vo, ⟨hr, RationalWordRows.cutW_lengths _ _ _ m hs.2.1,
        by rw [RationalWordRows.cutW_length]; exact hs.2.2⟩, ?_⟩
      simpa only [hs.2.2] using w)
  refine ⟨out, result, e, vo, ?_, w⟩
  rw [RationalWordRows.eliminateRowsW_foldl]
  exact hstate.1

end WeightedMIS.RegisterEliminateRows
