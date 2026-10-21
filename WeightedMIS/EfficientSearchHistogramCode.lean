module

public import WeightedMIS.EfficientSearchCode
public import WeightedMIS.EfficientSearchHistogram

/-! # Closed finite register code for counting recovered labels -/

@[expose] public section

namespace WeightedMIS.EfficientSearch.RegisterCode

open WeightedMIS.RegisterMachine

/-- Continuation after choosing the old count; all arithmetic is delegated to
the verified binary adder with carry-in true and a represented zero word. -/
def histogramUpdate {p : ℕ} (lookup add insert self : Fin p) (old : Atom) : Command p :=
  .call add [old, r 2, .flag true] [8, 9]
    (.call insert [r 3, r 8, r 1] [10]
      (.call self [r 4, r 10, r 2] [11, 12]
        (.branch (r 9) (.ret [r 11, .flag true]) (.ret [r 11, r 12]))))

/-- Arguments: label list, accumulated count dictionary, zero count word.
The entry is independent of all input sizes and bit widths. -/
def histogramBody {p : ℕ} (lookup add insert self : Fin p) : Command p :=
  .load (r 0) 3 4 15 (listCases (.ret [r 1, .flag false])
    (.call lookup [r 3, r 1] [5]
      (.load (r 5) 6 7 15 (listCases
        (histogramUpdate lookup add insert self (r 2))
        (histogramUpdate lookup add insert self (r 6))))))

end WeightedMIS.EfficientSearch.RegisterCode
