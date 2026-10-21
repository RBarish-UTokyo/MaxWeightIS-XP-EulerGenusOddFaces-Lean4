module

public import WeightedMIS.RationalRowSemantics
public import WeightedMIS.DeterministicKernelWidth

/-!
# Word-level rational elimination

Rows are lists of fixed-width binary rational words. The functions below are
the exact reference semantics of the compiled pivot search, projection, cut,
and outer constraint loop: every arithmetic step is the verified binary
operation (`multiply`, `add`, `subtract`, `divide`) and the zero test is the
binary magnitude test `isZero`.

`RowRep l x` states that the words of `l` are canonical and denote the
coordinates of `x`. Under one explicit width inequality, derived from the
determinant bounds of `EliminationCertificate`, the word-level elimination
refines `RationalElimination.eliminateRows` and in particular computes the
rational incidence-kernel generators `DeterministicKernel.initial`.
-/

@[expose] public section

namespace WeightedMIS.RationalWordRows

open Matrix BinaryRational RationalWidth RationalElimination

variable {N : ℕ}

/-- A canonical word denoting a rational. -/
def Rep (w : Word N) (q : ℚ) : Prop := w.value = q ∧ Canonical w

/-- A canonical word row denoting a rational vector. -/
def RowRep {m : ℕ} (l : List (Word N)) (x : Fin m → ℚ) : Prop :=
  List.Forall₂ Rep l (List.ofFn x)

/-! ## Reference functions -/

/-- Dot product exactly as computed by `RegisterRationalRow`. -/
def dotW (zero : Word N) (c v : List (Word N)) : Word N :=
  RegisterRationalRow.dotWords zero c v

/-- The pivot predicate: the binary zero test fails on the dot product. -/
def nonzeroW (zero : Word N) (c v : List (Word N)) : Bool :=
  !(isZero (dotW zero c v)).1

/-- Coordinatewise `v_i - coef * p_i`. -/
def scaleSubW (coef : Word N) : List (Word N) → List (Word N) → List (Word N)
  | v :: vs, p :: ps => (subtract v (multiply coef p).1).1 :: scaleSubW coef vs ps
  | _, _ => []

/-- Projection of `v` along the pivot `p` with cached pivot value `pv`. -/
def projectW (zero : Word N) (c p : List (Word N)) (pv : Word N) (v : List (Word N)) :
    List (Word N) :=
  scaleSubW (divide (dotW zero c v) pv).1 v p

/-- Process one constraint row: first nonzero pivot, then project every vector. -/
def cutW (zero : Word N) (c : List (Word N)) (vs : List (List (Word N))) :
    List (List (Word N)) :=
  match vs.find? (nonzeroW zero c) with
  | none => vs
  | some p => vs.map (projectW zero c p (dotW zero c p))

/-- Process all constraint rows in order. -/
def eliminateRowsW (zero : Word N) : List (List (Word N)) → List (List (Word N)) →
    List (List (Word N))
  | [], vs => vs
  | c :: cs, vs => eliminateRowsW zero cs (cutW zero c vs)

theorem eliminateRowsW_foldl (zero : Word N) (cs vs : List (List (Word N))) :
    eliminateRowsW zero cs vs = cs.foldl (fun s c => cutW zero c s) vs := by
  induction cs generalizing vs with
  | nil => rfl
  | cons c cs ih => exact ih _

/-- Coordinate vectors built by sharing suffixes: `e_0 = one :: zeros` and
`e_{i+1} = zero :: e_i`. -/
def coordinateVectorsW (zero one : Word N) : ℕ → List (List (Word N))
  | 0 => []
  | k + 1 => (one :: List.replicate k zero) :: (coordinateVectorsW zero one k).map (zero :: ·)

/-! ## Lengths -/

theorem scaleSubW_length (coef : Word N) (v p : List (Word N)) :
    (scaleSubW coef v p).length = min v.length p.length := by
  induction v generalizing p with
  | nil => simp [scaleSubW]
  | cons a v ih =>
    cases p with
    | nil => simp [scaleSubW]
    | cons b p => simp [scaleSubW, ih, Nat.succ_min_succ]

theorem cutW_length (zero : Word N) (c : List (Word N)) (vs : List (List (Word N))) :
    (cutW zero c vs).length = vs.length := by
  unfold cutW
  split <;> simp

/-- Every vector keeps length `m` when all inputs have length `m`. -/
theorem cutW_lengths (zero : Word N) (c : List (Word N)) (vs : List (List (Word N))) (m : ℕ)
    (hvs : ∀ v ∈ vs, v.length = m) : ∀ v ∈ cutW zero c vs, v.length = m := by
  unfold cutW
  split
  · exact hvs
  · next p hp =>
    have hpm := hvs p (List.mem_of_find?_eq_some hp)
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    simp [projectW, scaleSubW_length, hvs v hv, hpm]

theorem eliminateRowsW_length (zero : Word N) (cs vs : List (List (Word N))) :
    (eliminateRowsW zero cs vs).length = vs.length := by
  induction cs generalizing vs with
  | nil => rfl
  | cons c cs ih => simp [eliminateRowsW, ih, cutW_length]

theorem eliminateRowsW_lengths (zero : Word N) (cs vs : List (List (Word N))) (m : ℕ)
    (hvs : ∀ v ∈ vs, v.length = m) : ∀ v ∈ eliminateRowsW zero cs vs, v.length = m := by
  induction cs generalizing vs with
  | nil => exact hvs
  | cons c cs ih => exact ih _ (cutW_lengths zero c vs m hvs)

theorem coordinateVectorsW_length (zero one : Word N) (m : ℕ) :
    (coordinateVectorsW zero one m).length = m := by
  induction m with
  | zero => rfl
  | succ k ih => simp [coordinateVectorsW, ih]

theorem coordinateVectorsW_lengths (zero one : Word N) (m : ℕ) :
    ∀ v ∈ coordinateVectorsW zero one m, v.length = m := by
  induction m with
  | zero => simp [coordinateVectorsW]
  | succ k ih =>
    intro v hv
    simp only [coordinateVectorsW, List.mem_cons, List.mem_map] at hv
    rcases hv with rfl | ⟨w, hw, rfl⟩
    · simp
    · simp [ih w hw]

/-! ## Generic list facts -/

theorem forall₂_mem_left {α β : Type*} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {a : α} (ha : a ∈ l) : ∃ b ∈ l', R a b := by
  induction h with
  | nil => simp at ha
  | cons hab _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hr⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem forall₂_imp_mem {α β : Type*} {R S : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') (hS : ∀ a b, a ∈ l → b ∈ l' → R a b → S a b) :
    List.Forall₂ S l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    exact .cons (hS _ _ List.mem_cons_self List.mem_cons_self hab)
      (ih (fun a b ha hb hr => hS a b (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb) hr))

theorem find?_rel {α β : Type*} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') (P : α → Bool) (Q : β → Bool)
    (hPQ : ∀ a b, a ∈ l → b ∈ l' → R a b → P a = Q b) :
    Option.Rel R (l.find? P) (l'.find? Q) := by
  induction h with
  | nil => exact .none
  | @cons a b l l' hab _ ih =>
    have he := hPQ a b List.mem_cons_self List.mem_cons_self hab
    by_cases hp : P a = true
    · have hq : Q b = true := he ▸ hp
      simp only [List.find?_cons, hp, hq]
      exact .some hab
    · have hp' : P a = false := by simpa using hp
      have hq : Q b = false := he ▸ hp'
      simp only [List.find?_cons, hp', hq]
      exact ih (fun a' b' ha' hb' hr =>
        hPQ a' b' (List.mem_cons_of_mem _ ha') (List.mem_cons_of_mem _ hb') hr)

theorem rowRep_length {m : ℕ} {l : List (Word N)} {x : Fin m → ℚ} (h : RowRep l x) :
    l.length = m := by
  simpa using h.length_eq

theorem rowRep_mem {m : ℕ} {l : List (Word N)} {x : Fin m → ℚ} (h : RowRep l x)
    {w : Word N} (hw : w ∈ l) : ∃ i, Rep w (x i) := by
  obtain ⟨q, hq, hr⟩ := forall₂_mem_left h hw
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  exact ⟨i, hr⟩

/-! ## Arithmetic steps -/

theorem negate_canonical {q : Word N} (hq : Canonical q) : Canonical (negate q) := by
  refine ⟨hq.1, ?_, ?_⟩
  · rw [negate_value]
    simpa [Rat.num_neg_eq_neg_num, negate] using hq.2.1
  · rw [negate_value]
    simpa [negate] using hq.2.2

theorem subtract_width_safe (q r : Word N) (a b : ℕ) (hq : Canonical q) (hr : Canonical r)
    (hqa : Fits q.value a) (hrb : Fits r.value b) (hn : a + b + 1 ≤ N) :
    (subtract q r).1.value = q.value - r.value ∧ Canonical (subtract q r).1 := by
  have h := add_width_safe q (negate r) a b hq (negate_canonical hr) hqa
    (by rw [negate_value]; exact fits_neg hrb) hn
  refine ⟨?_, h.2.1⟩
  change (add q (negate r)).1.value = _
  rw [h.1, negate_value, sub_eq_add_neg]

theorem dotValue_rowRep {m : ℕ} {c v : List (Word N)} {x y : Fin m → ℚ}
    (hc : RowRep c x) (hv : RowRep v y) :
    RegisterRationalRow.dotValue c v = dotProduct x y := by
  induction m generalizing c v with
  | zero =>
    have hc0 : c = [] := List.eq_nil_of_length_eq_zero (rowRep_length hc)
    subst hc0
    simp [RegisterRationalRow.dotValue, dotProduct]
  | succ k ih =>
    unfold RowRep at hc hv
    rw [List.ofFn_succ] at hc hv
    cases hc with
    | cons hc0 hct =>
    cases hv with
    | cons hv0 hvt =>
    simp only [RegisterRationalRow.dotValue, dotProduct, Fin.sum_univ_succ]
    rw [hc0.1, hv0.1, ih hct hvt]
    rfl

/-- Width needed for the dot product, pivot ratio, product and subtraction. -/
def projectWidth (a W m : ℕ) : ℕ :=
  (a + W + 1) * (m + 1) + 2 * ((a + W + 1) * m + 1) + 2 * W + 3

theorem dotW_rep {m : ℕ} (zero : Word N) (hz : Rep zero 0) {c v : List (Word N)}
    {x y : Fin m → ℚ} (hc : RowRep c x) (hv : RowRep v y) (a b : ℕ)
    (hxa : ∀ i, Fits (x i) a) (hyb : ∀ i, Fits (y i) b)
    (hN : (a + b + 1) * (m + 1) + 2 ≤ N) :
    Rep (dotW zero c v) (dotProduct x y) := by
  have hcorrect := RegisterRationalRow.dotWords_correct c v zero a b hz.1 hz.2
    (fun q hq => (rowRep_mem hc hq).elim fun _ h => h.2)
    (fun r hr => (rowRep_mem hv hr).elim fun _ h => h.2)
    (fun q hq => (rowRep_mem hc hq).elim fun i h => h.1 ▸ hxa i)
    (fun r hr => (rowRep_mem hv hr).elim fun i h => h.1 ▸ hyb i)
    (by rw [rowRep_length hc]; exact hN)
  exact ⟨hcorrect.1.trans (dotValue_rowRep hc hv), hcorrect.2⟩

theorem scaleSubW_rep {m : ℕ} (coef : Word N) (κ : ℚ) (hκ : Rep coef κ) (K W : ℕ)
    (hK : Fits κ K) {v p : List (Word N)} {z y : Fin m → ℚ}
    (hv : RowRep v z) (hp : RowRep p y) (hz : ∀ i, Fits (z i) W) (hy : ∀ i, Fits (y i) W)
    (hN : 2 * W + K + 1 ≤ N) :
    RowRep (scaleSubW coef v p) (fun j => z j - κ * y j) := by
  induction m generalizing v p with
  | zero =>
    have hv0 : v = [] := List.eq_nil_of_length_eq_zero (rowRep_length hv)
    subst hv0
    simp [scaleSubW, RowRep]
  | succ k ih =>
    unfold RowRep at hv hp ⊢
    rw [List.ofFn_succ] at hv hp
    rw [List.ofFn_succ]
    cases hv with
    | @cons vh ph vt _ hv0 hvt =>
    cases hp with
    | @cons pw _ pt _ hp0 hpt =>
    have hm := multiply_width_safe coef _ K W hκ.2 hp0.2 (hκ.1 ▸ hK) (hp0.1 ▸ hy 0)
      (by omega)
    have hmf : Fits (multiply coef pw).1.value (K + W) := by
      rw [hm.1, hκ.1, hp0.1]
      exact fits_mul hK (hy 0)
    have hs := subtract_width_safe _ _ W (K + W) hv0.2 hm.2.1 (hv0.1 ▸ hz 0) hmf (by omega)
    refine .cons ⟨?_, hs.2⟩ (ih hvt hpt (fun i => hz i.succ) (fun i => hy i.succ))
    rw [hs.1, hm.1, hκ.1, hv0.1, hp0.1]

theorem project_eq {m : ℕ} (x y z : Fin m → ℚ) :
    project (rowMap x) y z = fun j => z j - dotProduct x z / dotProduct x y * y j := by
  rw [project_apply]
  funext j
  simp [smul_eq_mul]

theorem projectW_rep {m : ℕ} (zero : Word N) (hz0 : Rep zero 0) {c p v : List (Word N)}
    {x y z : Fin m → ℚ} {pv : Word N} (hc : RowRep c x) (hp : RowRep p y) (hv : RowRep v z)
    (hpv : Rep pv (dotProduct x y)) (hne : dotProduct x y ≠ 0) (a W : ℕ)
    (hx : ∀ i, Fits (x i) a) (hy : ∀ i, Fits (y i) W) (hzW : ∀ i, Fits (z i) W)
    (hN : projectWidth a W m ≤ N) :
    RowRep (projectW zero c p pv v) (project (rowMap x) y z) := by
  unfold projectWidth at hN
  have hd := dotW_rep zero hz0 hc hv a W hx hzW (by omega)
  have hdf : Fits (dotW zero c v).value ((a + W + 1) * m + 1) := by
    rw [hd.1]; exact fits_dot x z a W hx hzW
  have hpf : Fits pv.value ((a + W + 1) * m + 1) := by
    rw [hpv.1]; exact fits_dot x y a W hx hy
  have hq := divide_width_safe _ _ _ _ hd.2 hpv.2 hdf hpf (by omega) (by rw [hpv.1]; exact hne)
  rw [hd.1, hpv.1] at hq
  have hqf : Fits (dotProduct x z / dotProduct x y)
      ((a + W + 1) * m + 1 + ((a + W + 1) * m + 1)) :=
    fits_div (fits_dot x z a W hx hzW) (fits_dot x y a W hx hy)
  rw [project_eq]
  exact scaleSubW_rep _ _ ⟨hq.1, hq.2.1⟩ _ W hqf hv hp hzW hy (by omega)

/-! ## Cut and elimination -/

theorem nonzeroW_eq {m : ℕ} (zero : Word N) (hz : Rep zero 0) {c v : List (Word N)}
    {x y : Fin m → ℚ} (hc : RowRep c x) (hv : RowRep v y) (a b : ℕ)
    (hxa : ∀ i, Fits (x i) a) (hyb : ∀ i, Fits (y i) b)
    (hN : (a + b + 1) * (m + 1) + 2 ≤ N) :
    nonzeroW zero c v = decide (rowMap x y ≠ 0) := by
  have hd := dotW_rep zero hz hc hv a b hxa hyb hN
  have hiff := isZero_correct (dotW zero c v) hd.2.1
  rw [hd.1] at hiff
  unfold nonzeroW
  rw [rowMap_apply]
  by_cases h0 : dotProduct x y = 0
  · simp [hiff.mpr h0, h0]
  · have hf : (isZero (dotW zero c v)).1 = false := by
      cases hb : (isZero (dotW zero c v)).1
      · rfl
      · exact absurd (hiff.mp hb) h0
    simp [hf, h0]

theorem cutW_correct {m : ℕ} (zero : Word N) (hz : Rep zero 0) {c : List (Word N)}
    {x : Fin m → ℚ} (hc : RowRep c x) (a W : ℕ) (hx : ∀ i, Fits (x i) a)
    {vs : List (List (Word N))} {ws : List (Fin m → ℚ)}
    (hvs : List.Forall₂ RowRep vs ws) (hws : ∀ w ∈ ws, ∀ i, Fits (w i) W)
    (hN : projectWidth a W m ≤ N) :
    List.Forall₂ RowRep (cutW zero c vs) (cut (rowMap x) ws) := by
  have hdotN : (a + W + 1) * (m + 1) + 2 ≤ N := by unfold projectWidth at hN; omega
  have hrel := find?_rel hvs (nonzeroW zero c) (fun w => decide (rowMap x w ≠ 0))
    (fun v w _ hw hr => nonzeroW_eq zero hz hc hr a W hx (hws w hw) hdotN)
  unfold cutW cut
  rcases h1 : vs.find? (nonzeroW zero c) with _ | p <;>
    rcases h2 : ws.find? (fun w => decide (rowMap x w ≠ 0)) with _ | y <;>
    rw [h1, h2] at hrel <;> cases hrel
  · exact hvs
  · next hpy =>
    have hymem : y ∈ ws := List.mem_of_find?_eq_some h2
    have hne : rowMap x y ≠ 0 := by
      have h3 := List.find?_some h2
      simpa only [decide_eq_true_eq] using h3
    rw [rowMap_apply] at hne
    have hpv := dotW_rep zero hz hc hpy a W hx (hws y hymem) hdotN
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact forall₂_imp_mem hvs (fun v w _ hw hr =>
      projectW_rep zero hz hc hpy hr hpv hne a W hx (hws y hymem) (hws w hw) hN)

theorem coordinateVectorsW_correct (zero one : Word N) (hz : Rep zero 0) (ho : Rep one 1)
    (m : ℕ) : List.Forall₂ RowRep (coordinateVectorsW zero one m) (coordinateVectors m) := by
  induction m with
  | zero => exact .nil
  | succ k ih =>
    unfold coordinateVectors at ih ⊢
    rw [List.ofFn_succ]
    refine .cons ?_ ?_
    · unfold RowRep
      rw [List.ofFn_succ]
      refine .cons (by simpa using ho) ?_
      have hzero : (fun i : Fin k => (Pi.single (0 : Fin (k + 1)) (1 : ℚ) : Fin (k + 1) → ℚ) i.succ) = fun _ => 0 := by
        funext i
        simp [Fin.succ_ne_zero]
      rw [hzero]
      simp only [List.ofFn_const]
      clear ih hzero
      induction k with
      | zero => exact .nil
      | succ k ihk => exact .cons hz ihk
    · rw [List.forall₂_map_left_iff]
      have hshift : (fun i : Fin k => (Pi.single i.succ (1 : ℚ) : Fin (k + 1) → ℚ)) =
          fun i => Fin.cons 0 (Pi.single i 1) := by
        funext i j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp [Fin.succ_ne_zero]
        · simp [Pi.single_apply, Fin.succ_inj]
      rw [hshift]
      refine List.forall₂_iff_get.mpr ⟨by simpa using ih.length_eq, fun i h1 h2 => ?_⟩
      have hi := List.forall₂_iff_get.mp ih |>.2 i h1 (by simpa using h2)
      simp only [List.get_eq_getElem, List.getElem_ofFn] at hi ⊢
      unfold RowRep at hi ⊢
      rw [List.ofFn_succ]
      exact .cons (by simpa using hz) (by simpa using hi)

theorem eliminateRows_append {M : Type*} [AddCommGroup M] [Module ℚ M]
    (a b : List (M →ₗ[ℚ] ℚ)) (vs : List M) :
    eliminateRows (a ++ b) vs = eliminateRows b (eliminateRows a vs) := by
  induction a generalizing vs with
  | nil => rfl
  | cons c a ih => exact ih _

/-- Integer constraint rows viewed as linear functionals. -/
def rowFunctional {m : ℕ} (r : Fin m → ℤ) : (Fin m → ℚ) →ₗ[ℚ] ℚ :=
  rowMap fun j => (r j : ℚ)

/-- Width of all stored elimination coordinates (determinant bound). -/
def elimWidth (L m B : ℕ) : ℕ := (L + m + 2 * B) * m + m ^ 2 + 1

theorem eliminateRowsW_prefix {m : ℕ} (rows : List (Fin m → ℤ)) (B : ℕ)
    (hrows : ∀ r ∈ rows, ∀ j, (r j).natAbs ≤ 2 ^ B) (zero : Word N) (hz : Rep zero 0)
    (hN : projectWidth (B + 1) (elimWidth rows.length m B) m ≤ N)
    (cs : List (List (Word N))) (k : ℕ)
    (hcs : List.Forall₂ RowRep cs ((rows.drop k).map fun r j => (r j : ℚ)))
    (vs : List (List (Word N)))
    (hvs : List.Forall₂ RowRep vs
      (eliminateRows ((rows.take k).map rowFunctional) (coordinateVectors m))) :
    List.Forall₂ RowRep (eliminateRowsW zero cs vs)
      (eliminateRows (rows.map rowFunctional) (coordinateVectors m)) := by
  induction cs generalizing k vs with
  | nil =>
    have hd : rows.length ≤ k := by
      have := hcs.length_eq
      simp at this
      omega
    have ht : rows.take k = rows := List.take_of_length_le hd
    rw [ht] at hvs
    exact hvs
  | cons c cs ih =>
    rcases hdrop : rows.drop k with _ | ⟨r, rest⟩
    · rw [hdrop] at hcs; cases hcs
    rw [hdrop] at hcs
    cases hcs with
    | cons hc hcs' =>
    have hget : rows[k]? = some r := by
      have := congrArg (·[0]?) hdrop
      simpa [List.getElem?_drop] using this
    have htake : rows.take (k + 1) = rows.take k ++ [r] := by
      rw [List.take_add_one, hget]; rfl
    have hdrop' : rows.drop (k + 1) = rest := by
      rw [← List.drop_drop, hdrop]; rfl
    have hrmem : r ∈ rows := List.mem_of_getElem? hget
    apply ih (k + 1) (by rw [hdrop']; exact hcs')
    rw [htake, List.map_append, eliminateRows_append]
    exact cutW_correct zero hz hc (B + 1) _
      (fun j => fits_int _ _ (hrows r hrmem j)) hvs
      (fun w hw j => EliminationCertificate.prefix_coordinate_size rows B hrows k w hw j) hN

/-- Word-level elimination of integer constraint rows from the coordinate
vectors refines the rational elimination. -/
theorem eliminateRowsW_correct {m : ℕ} (rows : List (Fin m → ℤ)) (B : ℕ)
    (hrows : ∀ r ∈ rows, ∀ j, (r j).natAbs ≤ 2 ^ B) (zero one : Word N)
    (hz : Rep zero 0) (ho : Rep one 1)
    (hN : projectWidth (B + 1) (elimWidth rows.length m B) m ≤ N)
    (cs : List (List (Word N)))
    (hcs : List.Forall₂ RowRep cs (rows.map fun r j => (r j : ℚ))) :
    List.Forall₂ RowRep (eliminateRowsW zero cs (coordinateVectorsW zero one m))
      (eliminateRows (rows.map rowFunctional) (coordinateVectors m)) :=
  eliminateRowsW_prefix rows B hrows zero hz hN cs 0 (by simpa using hcs) _
    (by simpa [eliminateRows] using coordinateVectorsW_correct zero one hz ho m)

/-! ## Incidence kernel generators -/

/-- The integer incidence equations, one per vertex, in vertex order. -/
def incidenceRows {n m : ℕ} (left right : Fin m → Fin n) : List (Fin m → ℤ) :=
  List.ofFn fun v e => KernelBasis.entry left right e v

theorem initial_eq_eliminateRows {n m : ℕ} (left right : Fin m → Fin n) :
    DeterministicKernel.initial left right =
      eliminateRows ((incidenceRows left right).map rowFunctional) (coordinateVectors m) := by
  rw [DeterministicKernel.initial_eq, ComputedKernel.rationalGenerators, kernelGenerators,
    incidenceRows, List.map_ofFn]
  congr 1
  congr 1
  funext v
  simp only [Function.comp_apply, rowFunctional]
  congr 1
  funext e
  simp [KernelBasis.entry, Incidence.unsigned, Matrix.transpose_apply]

/-- The uniform working width for the incidence elimination. -/
def kernelWidth (n m : ℕ) : ℕ := projectWidth 2 (elimWidth n m 1) m

/-- The rational incidence-kernel generators, computed with word arithmetic
from word rows denoting the incidence equations. -/
theorem initialW_correct {n m : ℕ} (left right : Fin m → Fin n) (zero one : Word N)
    (hz : Rep zero 0) (ho : Rep one 1) (hN : kernelWidth n m ≤ N)
    (cs : List (List (Word N)))
    (hcs : List.Forall₂ RowRep cs (List.ofFn fun v e => Incidence.unsigned left right e v)) :
    List.Forall₂ RowRep (eliminateRowsW zero cs (coordinateVectorsW zero one m))
      (DeterministicKernel.initial left right) := by
  rw [initial_eq_eliminateRows]
  apply eliminateRowsW_correct (incidenceRows left right) 1 ?_ zero one hz ho
    (by simpa [incidenceRows, kernelWidth] using hN)
  · simp only [incidenceRows, List.map_ofFn]
    convert hcs using 2
    funext v e
    simp [KernelBasis.entry, Incidence.unsigned]
  · intro r hr j
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hr
    simp only [KernelBasis.entry]
    split_ifs <;> norm_num

theorem kernelWidth_le (n m : ℕ) : kernelWidth n m ≤ 64 * (n + m + 3) ^ 3 := by
  unfold kernelWidth projectWidth elimWidth
  set s := n + m + 3 with hs
  have hm : m ≤ s := by omega
  have h1 : (n + m + 2 * 1) * m ≤ s * s := Nat.mul_le_mul (by omega) hm
  have h2 : m ^ 2 ≤ s * s := by rw [pow_two]; exact Nat.mul_le_mul hm hm
  have hW : (n + m + 2 * 1) * m + m ^ 2 + 1 ≤ 2 * (s * s) + 1 := by omega
  have hA : 2 + ((n + m + 2 * 1) * m + m ^ 2 + 1) + 1 ≤ 3 * (s * s) := by
    have : 3 ≤ s := by omega
    have : 9 ≤ s * s := Nat.mul_le_mul this this
    omega
  have hB : (2 + ((n + m + 2 * 1) * m + m ^ 2 + 1) + 1) * (m + 1) ≤ 3 * (s * s) * s :=
    Nat.mul_le_mul hA (by omega)
  have hC : (2 + ((n + m + 2 * 1) * m + m ^ 2 + 1) + 1) * m ≤ 3 * (s * s) * s :=
    Nat.mul_le_mul hA hm
  have hs3 : s ^ 3 = s * s * s := by ring
  have hss : s * s ≤ s * s * s := Nat.le_mul_of_pos_right _ (by omega)
  have h1s : 1 ≤ s * s * s := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [hs3]
  nlinarith

end WeightedMIS.RationalWordRows
