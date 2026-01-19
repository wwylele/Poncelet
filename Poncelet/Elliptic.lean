import Mathlib
import Poncelet.Circle

open WeierstrassCurve.Affine

variable {K : Type*} [Field K]
variable (cf : Config K)

@[grind .]
theorem k_eq_zero : cf.k = 0 ↔ cf.r = 1 - cf.u ∨ cf.r = -1 - cf.u := by
  rw [← sq_eq_zero_iff, cf.k_sq]
  grind

/-- The elliptic curve associated with the two circles configuration. -/
def elliptic := (WeierstrassCurve.mk 0
  ((1 - cf.u ^ 2 - cf.r ^ 2) / cf.r ^ 2) 0 (cf.u ^ 2 / cf.r ^ 2) 0).toAffine

theorem equation_elliptic (x y : K) :
    (elliptic cf).Equation x y ↔
    cf.r ^ 2 * y ^ 2 = x * (cf.r ^ 2 * x ^ 2 + (1 - cf.u ^ 2 - cf.r ^ 2) * x + cf.u ^ 2) := by
  obtain _ := cf.hr
  simp_rw [WeierstrassCurve.Affine.equation_iff, elliptic]
  field_simp
  ring_nf

@[grind =]
theorem nonsingular_elliptic [hchar : NeZero (2 : K)] (x y : K) :
    (elliptic cf).Nonsingular x y ↔
    cf.r ^ 2 * y ^ 2 = x * (cf.r ^ 2 * x ^ 2 + (1 - cf.u ^ 2 - cf.r ^ 2) * x + cf.u ^ 2) ∧ (
      3 * cf.r ^ 2 * x ^ 2 + 2 * (1 - cf.u ^ 2 - cf.r ^ 2) * x + cf.u ^ 2 ≠ 0
      ∨ y ≠ 0) := by
  obtain _ := cf.hr
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  congrm $(by rw [equation_elliptic cf]) ∧ (?_ ∨ $(by simp [elliptic, hchar.out]))
  simp_rw [elliptic]
  field_simp
  grind

theorem singular_elliptic [hchar : NeZero (2 : K)] (x y : K) :
    (elliptic cf).Equation x y ∧ ¬ (elliptic cf).Nonsingular x y ↔
    (((cf.u = cf.r - 1 ∨ cf.u = 1 - cf.r) ∧ x = (cf.r - 1) / cf.r) ∨
    ((cf.u = cf.r + 1 ∨ cf.u = -cf.r - 1) ∧ x = (cf.r + 1) / cf.r)) ∧ y = 0 := by
  obtain _ := cf.hr
  rw [equation_elliptic, nonsingular_elliptic]
  trans cf.r ^ 2 * y ^ 2 = x * (cf.r ^ 2 * x ^ 2 + (1 - cf.u ^ 2 - cf.r ^ 2) * x + cf.u ^ 2) ∧
        (3 * cf.r ^ 2 * x ^ 2 + 2 * (1 - cf.u ^ 2 - cf.r ^ 2) * x + cf.u ^ 2 = 0 ∧ y = 0)
  · tauto
  constructor
  · rintro ⟨h1, h2, hy⟩
    rw [hy] at h1
    symm at h1
    have hx : x ≠ 0 := by
      contrapose! h2
      simp [h2, cf.hu]
    have hx2 : cf.r ^ 2 * x ^ 2 + (1 - cf.u ^ 2 - cf.r ^ 2) * x + cf.u ^ 2 = 0 := by
      simpa [hx] using h1
    have hx3 : (2 * cf.r ^ 2 * x + (1 - cf.u ^ 2 - cf.r ^ 2)) * x = 0 := by
      linear_combination h2 - hx2
    have hx4 : 2 * cf.r ^ 2 * x + (1 - cf.u ^ 2 - cf.r ^ 2) = 0 := by
      simpa [hx] using hx3
    have hx5 : x = -(1 - cf.u ^ 2 - cf.r ^ 2) / (2 * cf.r ^ 2) := by
      field_simp
      linear_combination hx4
    rw [hx5] at h1
    field_simp at h1
    have h : (1 - cf.u ^ 2 - cf.r ^ 2) * (cf.u - cf.r + 1) * (cf.u - cf.r - 1) *
        (cf.u + cf.r - 1) * (cf.u + cf.r + 1) = 0 := by
      linear_combination h1
    obtain h | h | h | h | h : 1 - cf.u ^ 2 - cf.r ^ 2 = 0 ∨
        cf.u - cf.r + 1 = 0 ∨ cf.u - cf.r - 1 = 0 ∨
        cf.u + cf.r - 1 = 0 ∨ cf.u + cf.r + 1 = 0 := by simpa [or_assoc] using h
    · simp [h, hx, cf.hr, hchar.out] at hx4
    · have hu : cf.u = cf.r - 1 := by linear_combination h
      rw [hu] at hx5
      suffices x = (cf.r - 1) / cf.r by simp [hu, this, hy]
      field_simp at hx5 ⊢
      rw [← mul_left_inj' (show 2 * cf.r ≠ 0 by simp [cf.hr, hchar.out])]
      linear_combination hx5
    · have hu : cf.u = cf.r + 1 := by linear_combination h
      rw [hu] at hx5
      suffices x = (cf.r + 1) / cf.r by simp [hu, this, hy]
      field_simp at hx5 ⊢
      rw [← mul_left_inj' (show 2 * cf.r ≠ 0 by simp [cf.hr, hchar.out])]
      linear_combination hx5
    · have hu : cf.u = 1 - cf.r := by linear_combination h
      rw [hu] at hx5
      suffices x = (cf.r - 1) / cf.r by simp [hu, this, hy]
      field_simp at hx5 ⊢
      rw [← mul_left_inj' (show 2 * cf.r ≠ 0 by simp [cf.hr, hchar.out])]
      linear_combination hx5
    · have hu : cf.u = -cf.r - 1 := by linear_combination h
      rw [hu] at hx5
      suffices x = (cf.r + 1) / cf.r by simp [hu, this, hy]
      field_simp at hx5 ⊢
      rw [← mul_left_inj' (show 2 * cf.r ≠ 0 by simp [cf.hr, hchar.out])]
      linear_combination hx5
  · intro h
    obtain ⟨⟨hu | hu, hx⟩ | ⟨hu | hu, hx⟩, hy⟩ := h
    all_goals
    simp_rw [hu, hx, hy]
    exact ⟨by field, by field, by simp⟩

/-- Map a point on the elliptic curve to a vertex, expressed in raw coordinates. -/
def fPointRaw (p : (elliptic cf).Point) : Fin 3 → K := match p with
| .zero => ![cf.u + cf.r, 0, 1]
| .some (x := x) (y := y) _ =>
  ![cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 + 2 * cf.r * (1 - cf.r ^ 2 - cf.r * cf.u) * x
      + cf.u ^ 2 * (cf.u + cf.r),
    -2 * cf.r ^ 2 * cf.k * y,
    (cf.r * x + cf.u) ^ 2]

@[simp]
theorem fPointRaw_zero : fPointRaw cf .zero = ![cf.u + cf.r, 0, 1] := by simp [fPointRaw]

@[simp]
theorem fPointRaw_zero' : fPointRaw cf 0 = ![cf.u + cf.r, 0, 1] := fPointRaw_zero cf

/-- Map a point on the elliptic curve to a vertex. -/
def fPoint [hchar : NeZero (2 : K)] (p : (elliptic cf).Point) : P2 K :=
  P2.mk (fPointRaw cf p) <| by
  cases p with
  | zero =>
    simp [fPointRaw]
  | @some x y hxy =>
    by_cases! hx : cf.r * x + cf.u ≠ 0
    · simp [fPointRaw, hx]
    suffices fPointRaw cf (.some hxy) 1 ≠ 0 by
      contrapose! this
      simp [this]
    suffices cf.k ≠ 0 ∧ y ≠ 0 by simpa [fPointRaw, cf.hr, hchar.out]
    grind

@[simp]
theorem fPoint_zero [hchar : NeZero (2 : K)] :
    fPoint cf .zero = P2.mk ![cf.u + cf.r, 0, 1] (by simp) := by
  simp [fPoint]

@[simp]
theorem fPoint_zero' [hchar : NeZero (2 : K)] :
    fPoint cf 0 = P2.mk ![cf.u + cf.r, 0, 1] (by simp) :=
  fPoint_zero cf

theorem outerCircle_fPoint [hchar : NeZero (2 : K)] (p : (elliptic cf).Point) :
    OuterCircle cf (fPoint cf p) := by
  change (fPointRaw cf p 0 - cf.u * fPointRaw cf p 2) ^ 2 + fPointRaw cf p 1 ^ 2 =
    cf.r ^ 2 * fPointRaw cf p 2 ^ 2
  cases p with
  | zero => simp [fPointRaw]
  | @some x y hxy =>
    rw [nonsingular_elliptic cf] at hxy
    obtain ⟨heq, hs⟩ := hxy
    suffices
      (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 + 2 * cf.r * (1 - cf.r ^ 2 - cf.r * cf.u) * x +
        cf.u ^ 2 * (cf.u + cf.r) - cf.u * (cf.r * x + cf.u) ^ 2) ^ 2 +
      (2 * cf.r) ^ 2 * (cf.k) ^ 2 * (cf.r ^ 2 * y ^ 2) =
      cf.r ^ 2 * ((cf.r * x + cf.u) ^ 2) ^ 2 by
      convert this using 1
      simp [fPointRaw]
      ring
    rw [heq, cf.k_sq]
    ring

/-- Map a point on the elliptic curve to an edge, expressed in raw coordinates.
This is only correct when it is non-zero -/
def fChordNormal (x y : K) : Fin 3 → K :=
  ![-2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u) * y +
    (cf.r * x + cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
      2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2),
    -cf.k * (2 * cf.r ^ 2 * (cf.r * x + cf.u) * y +
      (cf.r * x - cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
      2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2)),
    (cf.r * x + cf.u) * ((cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x)]

theorem fChordNormal_onCircle [hchar : NeZero (2 : K)] {x y : K}
    (hxy : (elliptic cf).Nonsingular x y) :
    fChordNormal cf x y 0 ^ 2 + fChordNormal cf x y 1 ^ 2 = fChordNormal cf x y 2 ^ 2 := by
  rw [nonsingular_elliptic cf] at hxy
  obtain ⟨heq, hs⟩ := hxy
  suffices
      (2 * cf.r * ((cf.u + cf.r) ^ 2 - 1) * (cf.u - cf.r * x) * (cf.r * y) +
        (cf.r * x + cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
        2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2)) ^ 2 +
      cf.k ^ 2 * ((2 * cf.r * (cf.r * x + cf.u) * (cf.r * y) +
        (cf.r * x - cf.u) *
        (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 + 2 * cf.r * (1 - cf.r * (cf.r + cf.u)) * x +
        (cf.u + cf.r) * cf.u ^ 2))) ^ 2 =
      ((cf.r * x + cf.u) * ((cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x)) ^ 2 by
      convert this using 1
      · simp [fChordNormal]
        ring
  rw [cf.k_sq]
  grind

theorem presingular [hchar : NeZero (2 : K)] {x y : K} (hxy : (elliptic cf).Nonsingular x y)
    (h : (cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x = 0) :
    (2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u) * y) ^ 2 =
    ((cf.r * x + cf.u) *
      (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 + 2 * cf.r *
      (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2)) ^ 2 := by
  suffices (2 * cf.r * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u)) ^ 2 * (cf.r ^ 2 * y ^ 2) =
    ((cf.r * x + cf.u) *
      (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 + 2 * cf.r *
      (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2)) ^ 2 by
    linear_combination this
  rw [nonsingular_elliptic cf] at hxy
  obtain ⟨heq, hs⟩ := hxy
  rw [heq]
  suffices ((cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x) *
      ( (4*cf.r^6*x^3 - 4*cf.r^6*x^2 + 8*cf.r^5*cf.u*x^3 - 8*cf.r^5*cf.u*x^2
      + 4*cf.r^4* cf.u^2* x^3 - 8* cf.r^4* cf.u^2* x^2 +
      4* cf.r^4* cf.u^2* x - cf.r^4 *x^4 - 4* cf.r^4* x^3 + 8* cf.r^4* x^2
      - 8* cf.r^3* cf.u^3* x^2 + 8* cf.r^3* cf.u^3* x -
      4* cf.r^3* cf.u* x^3 + 8* cf.r^3* cf.u* x^2 - 4* cf.r^2* cf.u^4* x^2
      + 4* cf.r^2* cf.u^4* x + 2* cf.r^2* cf.u^2* x^2 -
      4* cf.r^2* cf.u^2* x - 4 *cf.r^2* x^2 - 4 *cf.r* cf.u^3* x - cf.u^4)) = 0 by
    linear_combination this
  simp [h]

/-- A predicate that `fChordNormal` vanishes -/
def SingularAbc [DecidableEq K] (x y : K) := fChordNormal cf x y = 0 deriving Decidable

theorem SingularAbc.mk [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (hxy : (elliptic cf).Nonsingular x y)
    (ha : -2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u) * y +
      (cf.r * x + cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
      2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2) = 0)
    (hc : (cf.r * x + cf.u) * ((cf.r * x - cf.u) ^ 2 *
      (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x) = 0) :
    SingularAbc cf x y := by
  unfold SingularAbc
  unfold fChordNormal
  simp only [Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true]
  refine ⟨ha, ?_, hc⟩
  obtain h := fChordNormal_onCircle cf hxy
  unfold fChordNormal at h
  rw [ha, hc] at h
  simpa using h

theorem SingularAbc.a_eq_zero [DecidableEq K] {x y : K}
    (h : SingularAbc cf x y) :
    -2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u) * y +
    (cf.r * x + cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
    2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2)
    = 0
  := congr($h 0)

theorem SingularAbc.y_eq [DecidableEq K] {x y : K} (h : SingularAbc cf x y) :
    2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u) * y =
    (cf.r * x + cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
    2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2) := by
  simpa [neg_add_eq_zero] using h.a_eq_zero

theorem SingularAbc.b_eq_zero [DecidableEq K] {x y : K} (h : SingularAbc cf x y) :
    cf.k * ((2 * cf.r ^ 2 * (cf.r * x + cf.u) * y +
    (cf.r * x - cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
    2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2))) = 0 := by
  simpa [fChordNormal] using congr($h 1)

theorem SingularAbc.y_eq' [DecidableEq K] {x y : K} (h : SingularAbc cf x y) :
    cf.k * (2 * cf.r ^ 2 * (cf.r * x + cf.u) * y) =
    -(cf.k * ((cf.r * x - cf.u) *
      (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
      2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2))) := by
  apply eq_of_sub_eq_zero
  linear_combination h.b_eq_zero

theorem SingularAbc.rx_add_u_ne_zero [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (h : SingularAbc cf x y)
    (hxy : ((elliptic cf)).Nonsingular x y) : cf.r * x + cf.u ≠ 0 := by
  obtain h2 := hchar.out
  obtain _ := cf.hr
  have : (4 : K) ≠ 0 := by
    contrapose! h2
    have : (2 : K) * 2 = 0 := by linear_combination h2
    simpa using this
  obtain ha := h.a_eq_zero
  rw [nonsingular_elliptic cf] at hxy
  obtain ⟨heq, hs⟩ := hxy
  grind

theorem SingularAbc.c_factor_eq_zero [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (h : SingularAbc cf x y)
    (hxy : (elliptic cf).Nonsingular x y) :
    (cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x = 0 := by
  suffices cf.r * x + cf.u ≠ 0 by
    simpa [fChordNormal, this] using congr($h 2)
  exact h.rx_add_u_ne_zero cf hxy

theorem Polynomial.roots_eq_of_natDegree_eq_two {K : Type*} [CommRing K] [IsDomain K]
    {p : Polynomial K} (hdeg : p.natDegree = 2) {x1 x2 : K}
    (hp1 : p.eval x1 = 0) (hp2 : p.eval x2 = 0) (h : x1 ≠ x2) :
    p.roots = {x1, x2} := by
  have hp0 : p ≠ 0 := by
    contrapose! hdeg
    simp [hdeg]
  have hm1 : x1 ∈ p.roots := by
    simp [hp0, hp1]
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hm1
  have hm2 : x2 ∈ p.roots := by
    simp [hp0, hp2]
  have hm2' : x2 ∈ t := by
    rw [ht] at hm2
    simpa [h.symm] using hm2
  obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem hm2'
  symm
  obtain hcard := Polynomial.card_roots' p
  have hcard : u.card + 1 < 2 := by simpa [hdeg, ht, hu] using hcard
  have hcard : u.card = 0 := by grind
  simpa [hdeg, ht, hu] using hcard

theorem Polynomial.add_eq_of_natDegree_eq_two {K : Type*} [Field K]
    {p : Polynomial K} {a b c : K} (ha : a ≠ 0)
    (hp : p = C a * X ^ 2 + C b * X + C c)
    {x1 x2 : K}
    (hp1 : p.eval x1 = 0) (hp2 : p.eval x2 = 0) (h : x1 ≠ x2) :
    x1 + x2 = -b / a := by
  have hdeg : p.natDegree = 2 := by
    rw [hp]
    compute_degree <;> grind
  obtain hroots := roots_eq_of_natDegree_eq_two hdeg hp1 hp2 h
  rw [hp] at hroots
  obtain hxx := Polynomial.eq_neg_mul_add_of_roots_quadratic_eq_pair hroots
  field_simp
  linear_combination hxx

theorem Polynomial.mul_eq_of_natDegree_eq_two {K : Type*} [Field K]
    {p : Polynomial K} {a b c : K} (ha : a ≠ 0)
    (hp : p = C a * X ^ 2 + C b * X + C c)
    {x1 x2 : K}
    (hp1 : p.eval x1 = 0) (hp2 : p.eval x2 = 0) (h : x1 ≠ x2) :
    x1 * x2 = c / a := by
  have hdeg : p.natDegree = 2 := by
    rw [hp]
    compute_degree <;> grind
  obtain hroots := roots_eq_of_natDegree_eq_two hdeg hp1 hp2 h
  rw [hp] at hroots
  obtain hxx := Polynomial.eq_mul_mul_of_roots_quadratic_eq_pair hroots
  field_simp
  linear_combination -hxx

theorem SingularAbc.c_factor_add [DecidableEq K] [hchar : NeZero (2 : K)] {x1 y1 x2 y2 : K}
    (h1 : SingularAbc cf x1 y1) (h2 : SingularAbc cf x2 y2)
    (hxy1 : (elliptic cf).Nonsingular x1 y1) (hxy2 : (elliptic cf).Nonsingular x2 y2)
    (h : x1 ≠ x2) (hur : cf.u + cf.r ≠ 0) :
    x1 + x2 = (2 * cf.u * (cf.u + cf.r) ^ 2 - 4 * cf.u) / ((cf.u + cf.r) ^ 2 * cf.r) := by
  let p := Polynomial.C ((cf.u + cf.r) ^ 2 * cf.r ^ 2) * Polynomial.X ^ 2
    + Polynomial.C (4 * cf.u * cf.r - 2 * cf.u * cf.r * (cf.u + cf.r) ^ 2) * Polynomial.X
    + Polynomial.C ((cf.u + cf.r) ^ 2 * cf.u ^ 2)
  have hc2 : (cf.u + cf.r) ^ 2 * cf.r ^ 2 ≠ 0 := by simp [cf.hr, hur]
  have hp1 : Polynomial.eval x1 p = 0 := by
    simp [p]
    linear_combination h1.c_factor_eq_zero cf hxy1
  have hp2 : Polynomial.eval x2 p = 0 := by
    simp [p]
    linear_combination h2.c_factor_eq_zero cf hxy2
  obtain h := Polynomial.add_eq_of_natDegree_eq_two hc2 (rfl) hp1 hp2 h
  field_simp at h ⊢
  linear_combination h

theorem SingularAbc.y_eq_reduced_aux [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (h : SingularAbc cf x y)
    (hxy : (elliptic cf).Nonsingular x y) :
    cf.r * (cf.u + cf.r) * (cf.r * x - cf.u) * y * ((cf.u + cf.r) ^ 2 - 1) =
    (cf.u - cf.r) * x * (cf.r * x + cf.u) * ((cf.u + cf.r) ^ 2 - 1) := by
  have h : cf.r * (cf.u + cf.r) * (cf.r * x - cf.u) * y * ((cf.u + cf.r) ^ 2 - 1) * 2 * cf.r =
    (cf.u - cf.r) * x * (cf.r * x + cf.u) * ((cf.u + cf.r) ^ 2 - 1) * 2 * cf.r := by
    linear_combination (cf.u + cf.r) * (h.y_eq cf) + (cf.r * x + cf.u) * h.c_factor_eq_zero cf hxy
  simpa [cf.hr, hchar.out] using h

theorem SingularAbc.xy_linear [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (h : SingularAbc cf x y)
    (hxy : (elliptic cf).Nonsingular x y) :
    -2 * cf.r ^ 2 * (cf.u + cf.r) * y =
    (cf.u - cf.r) * (cf.r * ((cf.u + cf.r) ^ 2 - 2) * x - cf.u * (cf.u + cf.r) ^ 2) := by
  by_cases h0 : (cf.u + cf.r) ^ 2 - 1 = 0
  · have h0' : (cf.u + cf.r) ^ 2 = 1 := by simpa [sub_eq_zero] using h0
    obtain hc := h.c_factor_eq_zero cf hxy
    rw [h0'] at hc
    have hc' : (cf.r * x + cf.u) ^ 2 = 0 := by linear_combination hc
    have hc' : cf.r * x + cf.u = 0 := by simpa using hc'
    rw [nonsingular_elliptic cf] at hxy
    obtain ⟨heq, hs⟩ := hxy
    have heq' : cf.r ^ 2 * y ^ 2 = x * ((cf.r * x + cf.u) ^ 2 - ((cf.u + cf.r) ^ 2 - 1) * x) := by
      linear_combination heq
    have hy : y = 0 := by simpa [hc', h0', cf.hr] using heq'
    suffices cf.r * (1 - 2) * x - cf.u = 0 by simp [hy, h0', this]
    linear_combination -hc'
  · have : -2 * cf.r ^ 2 * (cf.u + cf.r) * y * ((cf.u + cf.r) ^ 2 - 1) * 2 * cf.u ^ 2 =
      (cf.u - cf.r) * (cf.r * ((cf.u + cf.r) ^ 2 - 2) * x - cf.u * (cf.u + cf.r) ^ 2) *
      ((cf.u + cf.r) ^ 2 - 1) * 2 * cf.u ^ 2 := by
      linear_combination
        cf.r * ((cf.r * (cf.u + cf.r) ^ 2 * x + 4 * cf.u - cf.u * (cf.u + cf.r) ^ 2) *
        h.y_eq_reduced_aux cf hxy
        - cf.r * (cf.u + cf.r) * y * ((cf.u + cf.r) ^ 2 - 1) * h.c_factor_eq_zero cf hxy +
        (cf.u - cf.r) * x * ((cf.u + cf.r) ^ 2 - 1) * h.c_factor_eq_zero cf hxy)
        + (cf.u - cf.r) * ((cf.u + cf.r) ^ 2 - 1) * 2 * cf.u * h.c_factor_eq_zero cf hxy
    simpa [cf.hu, -neg_mul, h0, hchar.out] using this

theorem SingularAbc.x_relation [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (h : SingularAbc cf x y)
    (hxy : (elliptic cf).Nonsingular x y) :
    -(2 * cf.u * cf.k) ^ 2 =
    (cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) ^ 2 := by
  simp_rw [mul_pow, cf.k_sq]
  obtain h' := h.c_factor_eq_zero cf hxy
  grind

theorem SingularAbc.k_ne_zero [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (h : SingularAbc cf x y)
    (hxy : (elliptic cf).Nonsingular x y) :
    cf.k ≠ 0 := by
  by_contra! hk
  have hur : (cf.u + cf.r) ^ 2 = 1 := by
    obtain hk2 := congr($hk ^ 2)
    simpa [cf.k_sq, sub_eq_zero] using hk2
  obtain hx := (h.x_relation cf hxy)
  grind

theorem SingularAbc.fPointRaw_eq [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (h : SingularAbc cf x y)
    (hxy : (elliptic cf).Nonsingular x y) (hur : cf.u + cf.r ≠ 0) :
    fPointRaw cf (.some hxy) = ![
      2 * cf.r * x * ((cf.u + cf.r) ^ 2 - 1) / (cf.u + cf.r) ^ 2 * (cf.u ^ 2 - cf.r ^ 2),
      2 * cf.r * x * ((cf.u + cf.r) ^ 2 - 1) / (cf.u + cf.r) ^ 2 *
        ((cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) /
        (2 * cf.u * cf.k) * (cf.u ^ 2 - cf.r ^ 2)),
      2 * cf.r * x * ((cf.u + cf.r) ^ 2 - 1) / (cf.u + cf.r) ^ 2 * (2 * cf.u)] := by
  obtain h2 := hchar.out
  have : (4 : K) ≠ 0 := by
    contrapose! h2
    have : (2 : K) * 2 = 0 := by linear_combination h2
    simpa using this
  suffices
    cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 + 2 * cf.r * (1 - cf.r ^ 2 - cf.r * cf.u) * x +
      cf.u ^ 2 * (cf.u + cf.r) =
      2 * cf.r * x * ((cf.u + cf.r) ^ 2 - 1) / (cf.u + cf.r) ^ 2 * (cf.u ^ 2 - cf.r ^ 2) ∧
    -(2 * cf.r ^ 2 * cf.k * y) =
      2 * cf.r * x * ((cf.u + cf.r) ^ 2 - 1) / (cf.u + cf.r) ^ 2 *
        ((cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) /
        (2 * cf.u * cf.k) * (cf.u ^ 2 - cf.r ^ 2)) ∧
    (cf.r * x + cf.u) ^ 2 = 2 * cf.r * x * ((cf.u + cf.r) ^ 2 - 1) /
      (cf.u + cf.r) ^ 2 * (2 * cf.u) by
    simpa [fPointRaw]
  obtain hx := h.c_factor_eq_zero cf hxy
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    grind
  · obtain hk := h.k_ne_zero cf hxy
    obtain hy := h.y_eq
    have hrxu : cf.r * x - cf.u ≠ 0 := by grind
    obtain _ := cf.hu
    field_simp
    rw [cf.k_sq]
    rw [← mul_left_inj' hrxu]
    suffices -(2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) *
      (cf.r * x - cf.u) * y) * cf.u * (cf.u + cf.r) ^ 2 = x * ((cf.u + cf.r) ^ 2 - 1) *
      (cf.r * x * (cf.u + cf.r) ^ 2 - cf.u * ((cf.u + cf.r) ^ 2 - 2)) *
      (cf.u ^ 2 - cf.r ^ 2) * (cf.r * x - cf.u) * cf.r by
      convert this using 1
      · ring
      · ring
    rw [hy]
    simp_rw [neg_mul, neg_eq_iff_add_eq_zero]
    suffices
      - (cf.r + cf.u) * (cf.r^4 * x + cf.r^3 * cf.u * x - cf.r^2 * cf.u^2 * x
      - cf.r^2 * x - cf.r * cf.u^3 * x - cf.u^2) *
        ((cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x) = 0 by
      convert this using 1
      ring
    simp [hx]
  · field_simp
    grind

theorem SingularAbc.x_eq_zero_of_casePos [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (h : SingularAbc cf x y) (hxy : (elliptic cf).Nonsingular x y) (hur : cf.u + cf.r = 0) :
    x = 0 := by
  obtain h2 := hchar.out
  have h4 : (4 : K) ≠ 0 := by
    contrapose! h2
    have : (2 : K) * 2 = 0 := by linear_combination h2
    simpa using this
  simpa [hur, cf.hu, cf.hr, h4] using h.c_factor_eq_zero cf hxy

theorem SingularAbc.y_eq_zero_of_casePos [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (h : SingularAbc cf x y) (hxy : (elliptic cf).Nonsingular x y) (hur : cf.u + cf.r = 0) :
    y = 0 := by
  obtain hx := h.x_eq_zero_of_casePos cf hxy hur
  rw [nonsingular_elliptic cf] at hxy
  obtain ⟨heq, hs⟩ := hxy
  simpa [hx, cf.hr] using heq

theorem SingularAbc.fPointRaw_eq_of_casePos [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (h : SingularAbc cf x y) (hxy : (elliptic cf).Nonsingular x y) (hur : cf.u + cf.r = 0) :
  fPointRaw cf (.some hxy) = ![0, 0, cf.u ^ 2] := by
  obtain hx := h.x_eq_zero_of_casePos cf hxy hur
  obtain hy := h.y_eq_zero_of_casePos cf hxy hur
  simp [fPointRaw, hx, hy, hur]

theorem SingularAbc.y_eq_zero_of_caseNeg [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (h : SingularAbc cf x y) (hxy : (elliptic cf).Nonsingular x y) (hur : cf.u = cf.r) :
    y = 0 := by
  obtain hxy := h.xy_linear cf hxy
  simpa [hur, cf.hr, hchar.out, ← two_mul] using hxy

theorem SingularAbc.fPoint_eq [DecidableEq K] [hchar : NeZero (2 : K)]
    {x y : K} (h : SingularAbc cf x y)
    (hxy : (elliptic cf).Nonsingular x y) :
    fPoint cf (.some hxy) = P2.mk ![
      2 * cf.u * cf.k * (cf.u ^ 2 - cf.r ^ 2),
      ((cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) * (cf.u ^ 2 - cf.r ^ 2)),
      4 * cf.u ^ 2 * cf.k] (by
    obtain h2 := hchar.out
    have h4 : (4 : K) ≠ 0 := by
      contrapose! h2
      have : (2 : K) * 2 = 0 := by linear_combination h2
      simpa using this
    simp [cf.hu, h.k_ne_zero cf hxy, h2, h4]
    ) := by
  by_cases hur : cf.u + cf.r = 0
  · have hur2 : cf.u ^ 2 - cf.r ^ 2 = 0 := by grind
    suffices P2.mk ![0, 0, cf.u ^ 2] _ = P2.mk ![0, 0, 4 * cf.u ^ 2 * cf.k] _ by
      simpa [fPoint, h.fPointRaw_eq_of_casePos cf hxy hur, hur, hur2]
    symm
    rw [P2.mk_eq_mk']
    use 4 * cf.k
    simp [field]
  suffices P2.mk ![2 * cf.r * x * ((cf.u + cf.r) ^ 2 - 1) /
        (cf.u + cf.r) ^ 2 * (cf.u ^ 2 - cf.r ^ 2),
      2 * cf.r * x * ((cf.u + cf.r) ^ 2 - 1) / (cf.u + cf.r) ^ 2 *
        ((cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) /
        (2 * cf.u * cf.k) * (cf.u ^ 2 - cf.r ^ 2)),
      2 * cf.r * x * ((cf.u + cf.r) ^ 2 - 1) / (cf.u + cf.r) ^ 2 * (2 * cf.u)] _ =
    P2.mk ![2 * cf.u * cf.k * (cf.u ^ 2 - cf.r ^ 2),
    (cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) * (cf.u ^ 2 - cf.r ^ 2),
      4 * cf.u ^ 2 * cf.k]
    _ by
    simpa [fPoint, h.fPointRaw_eq cf hxy hur]
  rw [P2.mk_eq_mk']
  use cf.r * x * ((cf.u + cf.r) ^ 2 - 1) / ((cf.u + cf.r) ^ 2 * cf.u * cf.k)
  simp only [Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty, Matrix.vecCons_inj, and_true]
  obtain hk := h.k_ne_zero cf hxy
  obtain _ := cf.hu
  refine ⟨?_, ?_, ?_⟩
  · field
  · field
  · field

theorem singularAbc_zero_iff [DecidableEq K] :
    SingularAbc cf 0 0 ↔ cf.u + cf.r = 0 := by
  simp [SingularAbc, fChordNormal, cf.hu, imp_and, imp_or]

/-- Map a point on the elliptic curve to an edge, expressed in raw coordinates. -/
def fChordRaw [DecidableEq K] (p : (elliptic cf).Point) : Fin 3 → K := match p with
| .zero => ![1, -cf.k, cf.u + cf.r]
| .some (x := x) (y := y) _ =>
  if SingularAbc cf x y then
    ![2 * cf.u * cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2),
      (cf.r * (cf.u + cf.r) ^ 2 * x
      - cf.u * ((cf.u + cf.r) ^ 2 - 2)) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2),
      8 * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2)]
  else
    fChordNormal cf x y

@[simp]
theorem fChordRaw_zero [DecidableEq K] :
    fChordRaw cf .zero = ![1, -cf.k, cf.u + cf.r] := by simp [fChordRaw]

@[simp]
theorem fChordRaw_zero' [DecidableEq K] :
    fChordRaw cf 0 = ![1, -cf.k, cf.u + cf.r] := fChordRaw_zero cf

theorem SingularAbc.fChordRaw_ne_zero [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (h : SingularAbc cf x y) (hxy : (elliptic cf).Nonsingular x y) :
    fChordRaw cf (Point.some hxy) ≠ 0 := by
  obtain h2 := hchar.out
  have h4 : (4 : K) ≠ 0 := by
    contrapose! h2
    have : (2 : K) * 2 = 0 := by linear_combination h2
    simpa using this
  have h8 : (8 : K) ≠ 0 := by
    contrapose! h2
    have : (2 : K) * 2 * 2 = 0 := by linear_combination h2
    simpa using this
  obtain hk := h.k_ne_zero cf hxy
  by_cases hur : cf.u ^ 2 - cf.r ^ 2 = 0
  · suffices fChordRaw cf (Point.some hxy) 0 ≠ 0 by
      contrapose! this
      simp [this]
    simp [fChordRaw, h, hk, cf.hu, hur, h2, h4]
  · suffices fChordRaw cf (Point.some hxy) 2 ≠ 0 by
      contrapose! this
      simp [this]
    simp [fChordRaw, h, hk, cf.hu, hur, h8]

/-- Map a point on the elliptic curve to an edge. -/
def fChord [DecidableEq K] [hchar : NeZero (2 : K)] (p : (elliptic cf).Point) : P2 K :=
    P2.mk (fChordRaw cf p) <| by
  cases p with
  | zero =>
    simp [fChordRaw]
  | @some x y hxy =>
    by_cases h0 : SingularAbc cf x y
    · exact h0.fChordRaw_ne_zero cf hxy
    · suffices fChordNormal cf x y ≠ 0 by simpa [fChordRaw, h0]
      exact h0

theorem SingularAbc.fChord_eq [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (h : SingularAbc cf x y) (hxy : (elliptic cf).Nonsingular x y) :
    fChord cf (.some hxy) = P2.mk ![2 * cf.u * cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2),
      (cf.r * (cf.u + cf.r) ^ 2 * x
        - cf.u * ((cf.u + cf.r) ^ 2 - 2)) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2),
      8 * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2)]
      (by simpa [fChordRaw, h] using h.fChordRaw_ne_zero cf hxy) := by
  simp [fChord, fChordRaw, h]

@[simp]
theorem fChord_zero [DecidableEq K] [hchar : NeZero (2 : K)] :
    fChord cf .zero = P2.mk ![1, -cf.k, cf.u + cf.r] (by simp) := by
  simp [fChord]

@[simp]
theorem fChord_zero' [DecidableEq K] [hchar : NeZero (2 : K)] :
    fChord cf 0 = P2.mk ![1, -cf.k, cf.u + cf.r] (by simp) := fChord_zero cf

theorem innerCircle_fChord [DecidableEq K] [hchar : NeZero (2 : K)] (p : (elliptic cf).Point) :
    InnerCircle cf (fChord cf p) := by
  change fChordRaw cf p 0 ^ 2 + fChordRaw cf p 1 ^ 2 = fChordRaw cf p 2 ^ 2
  cases p with
  | zero =>
    simp [fChordRaw, cf.k_sq]
  | @some x y hxy =>
    by_cases hsingular : SingularAbc cf x y
    · suffices
        (2 * cf.u * cf.k) ^ 2 * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2) ^ 2 +
        (cf.r * (cf.u + cf.r) ^ 2 * x
        - cf.u * ((cf.u + cf.r) ^ 2 - 2)) ^ 2 * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2) ^ 2 =
        (2 * cf.u * cf.k) ^ 2 * (4 * cf.u * (cf.u ^ 2 - cf.r ^ 2)) ^ 2 by
        convert this using 1
        · simp [fChordRaw, hsingular]
          ring
        · simp [fChordRaw, hsingular]
          ring
      rw [← hsingular.x_relation cf hxy]
      ring
    rw [nonsingular_elliptic cf] at hxy
    obtain ⟨heq, hs⟩ := hxy
    simpa [fChordRaw, hsingular] using fChordNormal_onCircle cf hxy

theorem incidence_fPoint_fChord [DecidableEq K] [hchar : NeZero (2 : K)] (p : (elliptic cf).Point) :
    Incidence cf (fPoint cf p) (fChord cf p) := by
  have _ := cf.hu
  have _ := cf.hr
  change fPointRaw cf p 0 * fChordRaw cf p 0 + fPointRaw cf p 1 * fChordRaw cf p 1 =
    fPointRaw cf p 2 * fChordRaw cf p 2
  cases p with
  | zero =>
    simp [fChordRaw, fPointRaw]
  | @some x y hxy =>
    by_cases hsingular : SingularAbc cf x y
    · by_cases hur : cf.u + cf.r = 0
      · have hur2 : cf.u ^ 2 - cf.r ^ 2 = 0 := by grind
        simp [hsingular.fPointRaw_eq_of_casePos cf hxy hur, fChordRaw, hsingular, hur2]
      simp_rw [hsingular.fPointRaw_eq cf hxy hur]
      suffices
        2 * cf.r * x * ((cf.u + cf.r) ^ 2 - 1) /
          (cf.u + cf.r) ^ 2 * ((cf.u ^ 2 - cf.r ^ 2) * fChordRaw cf (.some hxy) 0 +
          ((cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) /
          (2 * cf.u * cf.k) * (cf.u ^ 2 - cf.r ^ 2)) *
          fChordRaw cf (.some hxy) 1) =
        2 * cf.r * x * ((cf.u + cf.r) ^ 2 - 1) /
        (cf.u + cf.r) ^ 2 * ((2 * cf.u) * fChordRaw cf (.some hxy) 2) by
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val]
        convert this using 1
        · ring
        · ring
      congrm(_ * ?_)
      obtain hk := hsingular.k_ne_zero cf hxy
      suffices (cf.u ^ 2 - cf.r ^ 2) *
        (cf.u ^ 2 * 2 ^ 2 * cf.k ^ 2 * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + cf.u ^ 2 * 4) +
        (cf.r * (cf.u + cf.r) ^ 2 * x
        - cf.u * ((cf.u + cf.r) ^ 2 - 2)) ^ 2 * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - cf.u ^ 2 * 4)) =
         cf.u ^ 4 * (cf.u ^ 2 - cf.r ^ 2) * 2 ^ 2 * cf.k ^ 2 * 8 by
        simpa [fChordRaw, hsingular, field]
      rw [← hsingular.x_relation cf hxy]
      ring
    rw [nonsingular_elliptic cf] at hxy
    obtain ⟨heq, hs⟩ := hxy
    suffices (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2
      + 2 * cf.r * (1 - cf.r ^ 2 - cf.r * cf.u) * x + cf.u ^ 2 * (cf.u + cf.r)) *
      (-(2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u) * y) +
        (cf.r * x + cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2
        + 2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2)) +
        2 * cf.r ^ 2 * cf.k ^ 2 * y *
      ((2 * cf.r ^ 2 * (cf.r * x + cf.u) * y +
          (cf.r * x - cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
            2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2))) =
      (cf.r * x + cf.u) ^ 2 *
        ((cf.r * x + cf.u) * ((cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x)) by
      convert this using 1
      · simp [fPointRaw, fChordRaw, hsingular, fChordNormal]
        ring
      · simp [fPointRaw, fChordRaw, hsingular, fChordNormal]
    rw [cf.k_sq]
    grind

/-- Map a point on the elliptic curve to a vertex-edge pair. -/
def f [DecidableEq K] [hchar : NeZero (2 : K)] (p : (elliptic cf).Point) : P2 K × P2 K :=
  ⟨fPoint cf p, fChord cf p⟩

@[simp]
theorem f_zero [DecidableEq K] [hchar : NeZero (2 : K)] :
    f cf .zero =
    ⟨P2.mk ![cf.u + cf.r, 0, 1] (by simp), P2.mk ![1, -cf.k, cf.u + cf.r] (by simp)⟩ := by
  simp [f]

theorem mapsTo_f [DecidableEq K] [hchar : NeZero (2 : K)] : Set.MapsTo (f cf) Set.univ (dom cf) :=
  fun p _ ↦ ⟨outerCircle_fPoint cf p, innerCircle_fChord cf p, incidence_fPoint_fChord cf p⟩

/-- The special point related to `fChord`. -/
def o : (elliptic cf).Point :=
  .some (show (elliptic cf).Nonsingular 0 0 by simp [elliptic, cf.hu, cf.hr])

@[simp]
theorem fPointRaw_o : fPointRaw cf (o cf) =
    ![cf.u ^ 2 * (cf.u + cf.r), 0, cf.u ^ 2] := by
  simp [fPointRaw, o]

@[simp]
theorem fPoint_o [hchar : NeZero (2 : K)] : fPoint cf (o cf) =
    P2.mk ![(cf.u + cf.r), 0, 1] (by simp) := by
  suffices P2.mk ![cf.u ^ 2 * (cf.u + cf.r), 0, cf.u ^ 2] _ = P2.mk ![cf.u + cf.r, 0, 1] _ by
    simpa [fPoint]
  rw [P2.mk_eq_mk']
  use cf.u ^ 2
  simp

@[simp]
theorem fChord_o [DecidableEq K] [hchar : NeZero (2 : K)] :
    fChord cf (o cf) = P2.mk ![1, cf.k, cf.u + cf.r] (by simp) := by
  by_cases hsingular : SingularAbc cf 0 0
  · obtain huv := (singularAbc_zero_iff cf).mp hsingular
    have hreq : cf.r = -cf.u := (neg_eq_of_add_eq_zero_right huv).symm
    have hk : cf.k ^ 2 = -1 := by simp [cf.k_sq, huv]
    unfold fChord
    rw [P2.mk_eq_mk']
    use 4 * cf.u ^ 2 * cf.k * (cf.u - cf.r)
    suffices 2 * cf.u * cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2) =
      4 * cf.u ^ 2 * cf.k * (cf.u - cf.r) ∧
      -(cf.u * ((cf.u + cf.r) ^ 2 - 2) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2)) =
        4 * cf.u ^ 2 * cf.k * (cf.u - cf.r) * cf.k ∧
      8 * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2) =
      4 * cf.u ^ 2 * cf.k * (cf.u - cf.r) * (cf.u + cf.r) by
      simpa [fChordRaw, o, hsingular]
    grind
  unfold fChord
  rw [P2.mk_eq_mk']
  simp [fChordRaw, o, hsingular, fChordNormal]
  grind

@[simp]
theorem f_o [DecidableEq K] [hchar : NeZero (2 : K)] : f cf (o cf) =
    ⟨P2.mk ![cf.u + cf.r, 0, 1] (by simp), P2.mk ![1, cf.k, cf.u + cf.r] (by simp)⟩ := by
  simp [f]

theorem eq_o_iff [hchar : NeZero (2 : K)] {x y : K} (h : (elliptic cf).Nonsingular x y) :
    .some h = o cf ↔ x = 0 where
  mp h0 := by
    have : x = 0 ∧ y = 0 := by simpa [o] using h0
    exact this.1
  mpr h0 := by
    suffices y = 0 by simp [this, o, h0]
    rw [nonsingular_elliptic cf] at h
    obtain ⟨heq, hs⟩ := h
    simpa [h0, cf.hr] using heq

theorem nonsingular_o_sub [CharZero K] {x y : K}
    (h : (elliptic cf).Nonsingular x y) :
    (elliptic cf).Nonsingular (cf.u ^ 2 / (cf.r ^ 2 * x)) (cf.u ^ 2 * y / (cf.r ^ 2 * x ^ 2)) := by
  rw [nonsingular_elliptic cf] at ⊢ h
  obtain _ := cf.hu
  obtain _ := cf.hr
  grind

theorem o_sub [DecidableEq K] [CharZero K] {x y : K} (h : (elliptic cf).Nonsingular x y)
    (ho : Point.some h ≠ o cf) :
    o cf - Point.some h = Point.some (nonsingular_o_sub cf h) := by
  obtain _ := cf.hu
  obtain _ := cf.hr
  obtain hx0 := (eq_o_iff cf h).ne.mp ho
  rw [nonsingular_elliptic cf] at h
  obtain ⟨heq, hs⟩ := h
  rw [sub_eq_iff_eq_add]
  by_cases hx : cf.u ^ 2 / (cf.r ^ 2 * x) = x
  · have hx' : cf.r ^ 2 * x ^ 2 = cf.u ^ 2 := by
      rw [div_eq_iff (by simp [cf.hr, hx0])] at hx
      rw [hx]
      ring
    have hy0 : y ≠ 0 := by grind
    have hy : cf.u ^ 2 * y / (cf.r ^ 2 * x ^ 2) ≠ (elliptic cf).negY x y := by
      suffices cf.u ^ 2 * y / (cf.r ^ 2 * x ^ 2) ≠ -y by simpa [elliptic]
      rw [hx']
      rw [mul_div_cancel_left_of_imp (by simp [cf.hu])]
      exact self_ne_neg.mpr hy0
    rw [Point.add_of_Y_ne hy]
    obtain hslope := WeierstrassCurve.Affine.slope_of_Y_ne hx hy
    simp_rw [o, Point.some.injEq, addX, hslope]
    simp only [elliptic, zero_mul, sub_zero, negY, sub_neg_eq_add, add_zero, addY, negAddY, addX,
      neg_add_rev]
    constructor
    · field_simp
      grind
    · rw [mul_comm, ← eq_div_iff_mul_eq (by simpa using cf.hr), ← div_pow] at hx'
      obtain hx' | hx' := eq_or_eq_neg_of_sq_eq_sq _ _ hx'
      all_goals
      rw [hx']
      field_simp
      grind
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  have : cf.u ^ 2 - cf.r ^ 2 * x ^ 2 ≠ 0 := by grind
  simp only [elliptic, o, addX, ne_eq, hx, not_false_eq_true, slope_of_X_ne, zero_mul, add_zero,
    addY, negY, negAddY, neg_add_rev, sub_zero, Point.some.injEq]
  constructor
  · field_simp
    grind
  · field_simp
    grind

theorem nonsingular_w [hchar : NeZero (2 : K)] :
    (elliptic cf).Nonsingular (cf.u ^ 2 / cf.r ^ 2) (cf.u ^ 2 / cf.r ^ 3) := by
  rw [nonsingular_elliptic cf]
  obtain _ := cf.hr
  refine ⟨?_, Or.inr (by simp [cf.hu, cf.hr])⟩
  field

/-- The special point related to `fPoint`. -/
def w [hchar : NeZero (2 : K)] : (elliptic cf).Point := .some (nonsingular_w cf)

theorem slope_w [DecidableEq K] [hchar : NeZero (2 : K)] :
    (elliptic cf).slope (cf.u ^ 2 / cf.r ^ 2) (cf.u ^ 2 / cf.r ^ 2)
    (cf.u ^ 2 / cf.r ^ 3) (cf.u ^ 2 / cf.r ^ 3) =
    (2 + cf.u ^ 2 - cf.r ^ 2) / (2 * cf.r) := by
  unfold elliptic
  obtain _ := cf.hu
  obtain _ := cf.hr
  obtain h2 := hchar.out
  have h11 : (1 : K) + 1 ≠ 0 := by
    contrapose! h2
    linear_combination h2
  rw [slope_of_Y_ne rfl (by
    suffices cf.u ^ 2 / cf.r ^ 3 ≠ -(cf.u ^ 2 / cf.r ^ 3) by simpa
    rw [← add_eq_zero_iff_eq_neg.ne, ← two_mul]
    simp [h2, cf.hu, cf.hr])]
  simp
  field

theorem addX_w_w [DecidableEq K] [hchar : NeZero (2 : K)] :
    (elliptic cf).addX (cf.u ^ 2 / cf.r ^ 2) (cf.u ^ 2 / cf.r ^ 2)
      ((elliptic cf).slope (cf.u ^ 2 / cf.r ^ 2) (cf.u ^ 2 / cf.r ^ 2)
      (cf.u ^ 2 / cf.r ^ 3) (cf.u ^ 2 / cf.r ^ 3))
      = (cf.r ^ 2 - cf.u ^ 2) ^ 2 / (4 * cf.r ^ 2) := by
  obtain _ := cf.hr
  obtain h2 := hchar.out
  have h4 : (4 : K) ≠ 0 := by
    contrapose! h2
    have : (2 : K) * 2 = 0 := by linear_combination h2
    simpa using this
  rw [slope_w cf]
  unfold addX elliptic
  simp
  field

theorem addY_w_w [DecidableEq K] [hchar : NeZero (2 : K)] :
    (elliptic cf).addY (cf.u ^ 2 / cf.r ^ 2) (cf.u ^ 2 / cf.r ^ 2) (cf.u ^ 2 / cf.r ^ 3)
      ((elliptic cf).slope (cf.u ^ 2 / cf.r ^ 2) (cf.u ^ 2 / cf.r ^ 2)
      (cf.u ^ 2 / cf.r ^ 3) (cf.u ^ 2 / cf.r ^ 3))
      = (cf.r ^ 2 - cf.u ^ 2) * ((cf.r ^ 2 - cf.u ^ 2) ^ 2
      - 2 * (cf.r ^ 2 + cf.u ^ 2)) / (8 * cf.r ^ 3) := by
  obtain h2 := hchar.out
  have h4 : (4 : K) ≠ 0 := by
    contrapose! h2
    have : (2 : K) * 2 = 0 := by linear_combination h2
    simpa using this
  have h8 : (8 : K) ≠ 0 := by
    contrapose! h2
    have : (2 : K) * 2 * 2 = 0 := by linear_combination h2
    simpa using this
  rw [slope_w cf]
  unfold addY elliptic
  simp
  field

theorem nonsingular_2w [hchar : NeZero (2 : K)] :
    (elliptic cf).Nonsingular ((cf.r ^ 2 - cf.u ^ 2) ^ 2 / (4 * cf.r ^ 2))
    ((cf.r ^ 2 - cf.u ^ 2) *
    ((cf.r ^ 2 - cf.u ^ 2) ^ 2 - 2 * (cf.r ^ 2 + cf.u ^ 2)) / (8 * cf.r ^ 3)) := by
  classical
  rw [← addX_w_w cf, ← addY_w_w cf]
  apply nonsingular_add (nonsingular_w cf) (nonsingular_w cf)
  suffices cf.u ^ 2 / cf.r ^ 3 ≠ -(cf.u ^ 2 / cf.r ^ 3) by simpa [elliptic]
  rw [← add_eq_zero_iff_eq_neg.ne, ← two_mul]
  simp [hchar.out, cf.hu, cf.hr]

theorem two_w [DecidableEq K] [hchar : NeZero (2 : K)] :
    w cf + w cf = .some (nonsingular_2w cf) := by
  unfold w
  rw [Point.add_self_of_Y_ne (by
    suffices cf.u ^ 2 / cf.r ^ 3 ≠ -(cf.u ^ 2 / cf.r ^ 3) by simpa [elliptic]
    rw [← add_eq_zero_iff_eq_neg.ne, ← two_mul]
    simp [hchar.out, cf.hu, cf.hr])]
  congr
  · apply addX_w_w cf
  · apply addY_w_w cf

theorem slope_w_sub [DecidableEq K] {x : K} (hx : x ≠ cf.u ^ 2 / cf.r ^ 2)
    (y : K) : (elliptic cf).slope (cf.u ^ 2 / cf.r ^ 2) x (cf.u ^ 2 / cf.r ^ 3) (-y) =
    (cf.u ^ 2 + cf.r ^ 3 * y) / (cf.u ^ 2 * cf.r - cf.r ^ 3 * x) := by
  rw [slope_of_X_ne hx.symm]
  obtain _ := cf.hu
  obtain _ := cf.hr
  have : cf.u ^ 2 - cf.r ^ 2 * x ≠ 0 := by grind
  field

theorem addX_w_sub [DecidableEq K] [hchar : NeZero (2 : K)]
    {x y : K} (hxy : (elliptic cf).Nonsingular x y)
    (hx : x ≠ cf.u ^ 2 / cf.r ^ 2) :
    (elliptic cf).addX (cf.u ^ 2 / cf.r ^ 2) x
      ((elliptic cf).slope (cf.u ^ 2 / cf.r ^ 2) x (cf.u ^ 2 / cf.r ^ 3) (-y)) =
    cf.u ^ 2 * (cf.r ^ 2 * x ^ 2 + (2 - cf.r ^ 2 - cf.u ^ 2) * x + cf.u ^ 2 + 2 * cf.r * y)
      / (cf.r ^ 2 * x - cf.u ^ 2) ^ 2 := by
  have : cf.r ^ 2 * x - cf.u ^ 2 ≠ 0 := by grind
  have : cf.u ^ 2 - cf.r ^ 2 * x ≠ 0 := by grind
  rw [slope_w_sub cf hx]
  simp only [addX, elliptic, zero_mul, add_zero]
  rw [nonsingular_elliptic cf] at hxy
  obtain ⟨heq, hnonsingular⟩ := hxy
  obtain _ := cf.hr
  field_simp
  linear_combination  cf.r ^ 4 * (cf.r ^ 2 * x - cf.u ^ 2) ^ 2 * heq

theorem addY_w_sub [DecidableEq K] [hchar : NeZero (2 : K)] {x y : K}
    (hxy : (elliptic cf).Nonsingular x y)
    (hx : x ≠ cf.u ^ 2 / cf.r ^ 2) :
    (elliptic cf).addY (cf.u ^ 2 / cf.r ^ 2) x (cf.u ^ 2 / cf.r ^ 3)
      ((elliptic cf).slope (cf.u ^ 2 / cf.r ^ 2) x (cf.u ^ 2 / cf.r ^ 3) (-y)) =
      cf.u ^ 2 *
        (cf.r ^ 4 * x ^ 3 + cf.r ^ 2 * (2 + cf.u ^ 2 - 2 * cf.r ^ 2) * x ^ 2
          + cf.u ^ 2 * (2 - 2 * cf.u ^ 2 + cf.r ^ 2) * x + cf.u ^ 4
          + (cf.r ^ 2 * (2 + cf.u ^ 2 - cf.r ^ 2) * x
          + cf.u ^ 2 * (2 - cf.u ^ 2 + cf.r ^ 2)) * cf.r * y)
      / (cf.r * (cf.r ^ 2 * x - cf.u ^ 2) ^ 3) := by
  have : cf.r ^ 2 * x - cf.u ^ 2 ≠ 0 := by grind
  have : cf.u ^ 2 - cf.r ^ 2 * x ≠ 0 := by grind
  rw [addY, negAddY, addX_w_sub cf hxy hx]
  rw [slope_w_sub cf hx]
  simp only [negY, neg_add_rev, elliptic, zero_mul, sub_zero]
  rw [nonsingular_elliptic cf] at hxy
  obtain ⟨heq, hnonsingular⟩ := hxy
  obtain _ := cf.hr
  obtain _ := cf.hu
  field_simp
  linear_combination (-2) * cf.r^4 * (cf.r^2*x - cf.u^2) * heq

theorem nonsingular_w_sub [hchar : NeZero (2 : K)] {x y : K}
    (hxy : (elliptic cf).Nonsingular x y)
    (hx : x ≠ cf.u ^ 2 / cf.r ^ 2) :
    (elliptic cf).Nonsingular
      (cf.u ^ 2 * (cf.r ^ 2 * x ^ 2 + (2 - cf.r ^ 2 - cf.u ^ 2) * x + cf.u ^ 2 + 2 * cf.r * y)
      / (cf.r ^ 2 * x - cf.u ^ 2) ^ 2)
    (cf.u ^ 2 *
        (cf.r ^ 4 * x ^ 3 + cf.r ^ 2 * (2 + cf.u ^ 2 - 2 * cf.r ^ 2) * x ^ 2
          + cf.u ^ 2 * (2 - 2 * cf.u ^ 2 + cf.r ^ 2) * x + cf.u ^ 4
          + (cf.r ^ 2 * (2 + cf.u ^ 2 - cf.r ^ 2) * x
          + cf.u ^ 2 * (2 - cf.u ^ 2 + cf.r ^ 2)) * cf.r * y)
      / (cf.r * (cf.r ^ 2 * x - cf.u ^ 2) ^ 3)) := by
  classical
  have hnegy : (elliptic cf).negY x y = -y := by simp [elliptic]
  have : ¬(cf.u ^ 2 / cf.r ^ 2 = x ∧
      cf.u ^ 2 / cf.r ^ 3 = (elliptic cf).negY x ((elliptic cf).negY x y)) := by
    simp [hx.symm]
  convert (elliptic cf).nonsingular_add (nonsingular_w cf) ((nonsingular_neg _ _).mpr hxy) this
      using 1
  · simp_rw [hnegy]
    rw [addX_w_sub cf hxy hx]
  · simp_rw [hnegy]
    rw [addY_w_sub cf hxy hx]

theorem w_sub [DecidableEq K] [hchar : NeZero (2 : K)]
    {x y : K} (hxy : (elliptic cf).Nonsingular x y)
    (hx : x ≠ cf.u ^ 2 / cf.r ^ 2) :
    w cf - .some hxy = .some (nonsingular_w_sub cf hxy hx) := by
  have hxy' : (elliptic cf).Nonsingular x (-y) := by
    simpa [elliptic] using (WeierstrassCurve.Affine.nonsingular_neg _ _).mpr hxy
  have hneg : - Point.some hxy = .some hxy' := by simp [elliptic]
  rw [sub_eq_add_neg, hneg]
  unfold w
  rw [Point.add_of_X_ne hx.symm]
  rw [Point.some.injEq]
  rw [addX_w_sub cf hxy hx]
  rw [addY_w_sub cf hxy hx]
  simp

theorem nonsingular_neg_w [hchar : NeZero (2 : K)] :
    (elliptic cf).Nonsingular (cf.u ^ 2 / cf.r ^ 2) (-cf.u ^ 2 / cf.r ^ 3)  := by
  convert (WeierstrassCurve.Affine.nonsingular_neg _ _).mpr (nonsingular_w cf) using 1
  simp [elliptic, neg_div]

theorem neg_w [hchar : NeZero (2 : K)] : -w cf = .some (nonsingular_neg_w cf) := by
  simp [w, elliptic, neg_div]

theorem x_not_at_w [hchar : NeZero (2 : K)] {x y : K} (hxy : (elliptic cf).Nonsingular x y)
    (hpw : .some hxy ≠ w cf) (hpnw : .some hxy ≠ -w cf) :
    x ≠ cf.u ^ 2 / cf.r ^ 2 := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  obtain ⟨heq, hnonsingular⟩ := (nonsingular_elliptic cf _ _).mp hxy
  unfold w at hpw hpnw
  by_contra! h
  have h1 : y ≠ cf.u ^ 2 / cf.r ^ 3 := by simpa [h] using hpw
  have h2 : y ≠ -(cf.u ^ 2 / cf.r ^ 3) := by simpa [elliptic, h] using hpnw
  simp_rw [h] at heq
  field_simp at heq
  have hy : (cf.r ^ 3 * y) ^ 2 = (cf.u ^ 2) ^ 2 := by linear_combination heq
  obtain hy | hy := eq_or_eq_neg_of_sq_eq_sq _ _ hy
  · contrapose! h1
    field_simp
    linear_combination hy
  · contrapose! h2
    field_simp
    linear_combination hy

theorem nonsingular_g [hchar : NeZero (2 : K)] : (elliptic cf).Nonsingular 1 cf.r⁻¹ := by
  rw [nonsingular_elliptic cf]
  obtain _ := cf.hr
  refine ⟨?_, Or.inr (by simp [cf.hr])⟩
  field

/-- The special point related to `next`. -/
def g [hchar : NeZero (2 : K)] : (elliptic cf).Point := .some (nonsingular_g cf)

theorem o_sub_w [DecidableEq K] [hchar : NeZero (2 : K)] : o cf - w cf = g cf := by
  obtain h2 := hchar.out
  have h4 : (4 : K) ≠ 0 := by
    contrapose! h2
    have : (2 : K) * 2 = 0 := by linear_combination h2
    simpa using this
  obtain _ := cf.hr
  obtain _ := cf.hu
  rw [sub_eq_iff_eq_add']
  unfold o w g
  by_cases hur : cf.u ^ 2 = cf.r ^ 2
  · have hx : cf.u ^ 2 / cf.r ^ 2 = 1 := by
      field_simp
      exact hur
    have hy : cf.u ^ 2 / cf.r ^ 3 ≠ (elliptic cf).negY 1 cf.r⁻¹ := by
      simp only [negY, elliptic, mul_one, sub_zero, ne_eq, hur]
      by_contra! h
      field_simp at h
      contrapose! h2
      have : (1 : K) = 1 := rfl
      linear_combination h + this
    rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hy]
    simp_rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy]
    simp [elliptic]
    field_simp
    grind
  · have hx : cf.u ^ 2 / cf.r ^ 2 ≠ 1 := by
      contrapose! hur
      field_simp at hur
      exact hur
    have : cf.u ^ 2 - cf.r ^ 2 ≠ 0 := by
      rw [sub_eq_zero.ne]
      contrapose! hx
      field_simp
      rw [hx]
    simp [hx, elliptic]
    field_simp
    grind

/-

Special points

       | elliptic           | xyz                                   | abc                     |
-------|--------------------|---------------------------------------|-------------------------|
Two intersections at infinity. Each has two tangent lines coincide
o - G⁺ = G⁺  (reflect chord)
o - G⁻ = G⁻
-------|--------------------|---------------------------------------|-------------------------|
G⁺, G⁻ | (-u / r,           | [1 : ∓i : 0]                          | [1 : ∓i : 0]            |
       |  ±i * u * k / r^2) |                                       |                         |
-------|--------------------|---------------------------------------|-------------------------|
H⁺ = w - G⁺  (reflect point)
H⁻ = w - G⁻
-------|--------------------|---------------------------------------|-------------------------|
H⁺, H⁻ | (u * (±2 * i * k + (u+r)^2 - 2) / (r * (u+r)^2), <...±...>)|
       |                    |                                       |
       |                    | [u^2 - r^2 : ∓i * (u^2 - r^2) : 2 * u]| [1 : ∓i : 0]
-------|--------------------|---------------------------------------|-------------------------|
L⁺ = o - H⁺  (reflect chord)
L⁻ = o - H⁻
-------|--------------------|---------------------------------------|-------------------------|
L⁺, L⁻ | (u * (∓2 * i * k + (u+r)^2 - 2) / (r * (u+r)^2), <...±...>)|
       |                    |                                       |
       |                    | [u^2 - r^2 : ∓i * (u^2 - r^2) : 2 * u]| [(u^2 - r^2)^2 + 4 * u^2 :
       |                    |                                       |∓i * ((u^2 - r^2)^2 - 4 * u^2):
       |                    |                                       |  4 * u * (u^2 - r^2)]
-------|--------------------|---------------------------------------|-------------------------|

Special parameter: u + r = 0, k = i

       | elliptic           | xyz                                   | abc                     |
-------|--------------------|---------------------------------------|-------------------------|
G⁺ = w, 2 * w = o
G⁻ = -w
-------|--------------------|---------------------------------------|-------------------------|
G⁺, G⁻ | (1, ±1 / u)        | [1 : ∓i : 0]                          | [1 : ∓i : 0]
-------|--------------------|---------------------------------------|-------------------------|
H⁺ = w - G⁺ = 0
H⁻ = w - G⁻ = 2 * w = o
-------|--------------------|---------------------------------------|-------------------------|
H⁺, H⁻ | ∞, (0, 0)          | [0 : 0 : 1]                           | [1 : ∓i : 0]
-------|--------------------|---------------------------------------|-------------------------|
L⁺ = o - H⁺ = o = H⁻
L⁻ = o - H⁻ = 0 = H⁺
-------|--------------------|---------------------------------------|-------------------------|
L⁺, L⁻ | (0, 0), ∞          | [0 : 0 : 1]                           | [1 : ±i : 0]
-------|--------------------|---------------------------------------|-------------------------|

Special parameter: u = r

       | elliptic           | xyz                                   | abc                     |
-------|--------------------|---------------------------------------|-------------------------|
o - G⁺ = G⁺
o - G⁻ = G⁻
-------|--------------------|---------------------------------------|-------------------------|
G⁺, G⁻ | (-1, ±i * k / u)   | [1 : ∓i : 0]                          | [1 : ∓i : 0]            |
-------|--------------------|---------------------------------------|-------------------------|
H⁺ = w - G⁺
H⁻ = w - G⁻
-------|--------------------|---------------------------------------|-------------------------|
H⁺, H⁻ | (u * (±2 * i * k + (u+r)^2 - 2) / (r * (u+r)^2), 0)        |
       |                    |                                       |
       |                    | [0 : 0 : 1]                           | [1 : ∓i : 0]
-------|--------------------|---------------------------------------|-------------------------|
L⁺ = o - H⁺  (reflect chord)
L⁻ = o - H⁻
-------|--------------------|---------------------------------------|-------------------------|
L⁺, L⁻ | (u * (∓2 * i * k + (u+r)^2 - 2) / (r * (u+r)^2), 0)        |
       |                    |                                       |
       |                    | [0 : 0 : 1]                           | [1 : ±i : 0]
-------|--------------------|---------------------------------------|-------------------------|
-/
