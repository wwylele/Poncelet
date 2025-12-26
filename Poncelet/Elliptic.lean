import Mathlib
import Poncelet.Basic

open WeierstrassCurve.Affine

variable (u r : ℂ)

noncomputable
def k := ((u + r) ^ 2 - 1) ^ (1 / 2 : ℂ)

theorem k_sq : k u r ^ 2 = (u + r) ^ 2 - 1 := by
  simp [k]

@[grind .]
theorem k_eq_zero : k u r = 0 ↔ r = 1 - u ∨ r = -1 - u := by
  rw [← sq_eq_zero_iff, k_sq]
  grind

noncomputable
def elliptic := (WeierstrassCurve.mk 0 ((1 - u ^ 2 - r ^ 2) / r ^ 2) 0 (u ^ 2 / r ^ 2) 0).toAffine

theorem equation_elliptic (hr : r ≠ 0) (x y : ℂ) :
    (elliptic u r).Equation x y ↔
    r ^ 2 * y ^ 2 = x * (r ^ 2 * x ^ 2 + (1 - u ^ 2 - r ^ 2) * x + u ^ 2) := by
  simp_rw [WeierstrassCurve.Affine.equation_iff, elliptic]
  field_simp
  ring_nf

variable {r} in
@[grind =]
theorem nonsingular_elliptic (hr : r ≠ 0) (x y : ℂ) :
    (elliptic u r).Nonsingular x y ↔
    r ^ 2 * y ^ 2 = x * (r ^ 2 * x ^ 2 + (1 - u ^ 2 - r ^ 2) * x + u ^ 2) ∧ (
      3 * r ^ 2 * x ^ 2 + 2 * (1 - u ^ 2 - r ^ 2) * x + u ^ 2 ≠ 0
      ∨ y ≠ 0) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  congrm $(by rw [equation_elliptic u r hr]) ∧ (?_ ∨ $(by simp [elliptic]))
  simp_rw [elliptic]
  field_simp
  grind

noncomputable
def fxyzRaw (p : (elliptic u r).Point) : Fin 3 → ℂ := match p with
| .zero => ![u + r, 0, 1]
| .some (x := x) (y := y) _ =>
  ![r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r ^ 2 - r * u) * x + u ^ 2 * (u + r),
    -2 * r ^ 2 * k u r * y,
    (r * x + u) ^ 2]

@[simp]
theorem fxyzRaw_zero : fxyzRaw u r .zero = ![u + r, 0, 1] := by simp [fxyzRaw]

@[simp]
theorem fxyzRaw_zero' : fxyzRaw u r 0 = ![u + r, 0, 1] := fxyzRaw_zero u r

variable {r} in
noncomputable
def fxyz (hr : r ≠ 0) (p : (elliptic u r).Point) : P2 :=
  P2.mk (fxyzRaw u r p) <| by
  cases p with
  | zero =>
    simp [fxyzRaw]
  | @some x y hxy =>
    by_cases! hx : r * x + u ≠ 0
    · simp [fxyzRaw, hx]
    suffices fxyzRaw u r (.some hxy) 1 ≠ 0 by
      contrapose! this
      simp [this]
    suffices (¬r = 0 ∧ ¬k u r = 0) ∧ ¬y = 0 by simpa [fxyzRaw]
    grind

variable {r} in
@[simp]
theorem fxyz_zero (hr : r ≠ 0) : fxyz u hr .zero = P2.mk ![u + r, 0, 1] (by simp) := by
  simp [fxyz]

variable {r} in
@[simp]
theorem fxyz_zero' (hr : r ≠ 0) : fxyz u hr 0 = P2.mk ![u + r, 0, 1] (by simp) := fxyz_zero u hr

variable {r} in
theorem outerCircle_fxyz (hr : r ≠ 0) (p : (elliptic u r).Point) :
    OuterCircle u r (fxyz u hr p) := by
  change (fxyzRaw u r p 0 - u * fxyzRaw u r p 2) ^ 2 + fxyzRaw u r p 1 ^ 2 =
    r ^ 2 * fxyzRaw u r p 2 ^ 2
  cases p with
  | zero => simp [fxyzRaw]
  | @some x y hxy =>
    rw [nonsingular_elliptic u hr] at hxy
    obtain ⟨heq, hs⟩ := hxy
    suffices
      (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r ^ 2 - r * u) * x +
        u ^ 2 * (u + r) - u * (r * x + u) ^ 2) ^ 2 +
      (2 * r) ^ 2 * (k u r) ^ 2 * (r ^ 2 * y ^ 2) =
      r ^ 2 * ((r * x + u) ^ 2) ^ 2 by
      convert this using 1
      simp [fxyzRaw]
      ring
    rw [heq, k_sq]
    ring

noncomputable
def fabcNormal (x y : ℂ) : Fin 3 → ℂ :=
  ![-2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y +
    (r * x + u) * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2),
    -k u r * (2 * r ^ 2 * (r * x + u) * y +
    (r * x - u) * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2)),
    (r * x + u) * ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x)]

variable {r} in
theorem fabcNormal_onCircle (hr : r ≠ 0) {x y : ℂ} (hxy : (elliptic u r).Nonsingular x y) :
    fabcNormal u r x y 0 ^ 2 + fabcNormal u r x y 1 ^ 2 = fabcNormal u r x y 2 ^ 2 := by
  rw [nonsingular_elliptic u hr] at hxy
  obtain ⟨heq, hs⟩ := hxy
  suffices
      (2 * r * ((u + r) ^ 2 - 1) * (u - r * x) * (r * y) +
        (r * x + u) * (r ^ 2 * (u + r) * x ^ 2 +
        2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2)) ^ 2 +
      k u r ^ 2 * ((2 * r * (r * x + u) * (r * y) +
        (r * x - u) *
        (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (r + u)) * x + (u + r) * u ^ 2))) ^ 2 =
      ((r * x + u) * ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x)) ^ 2 by
      convert this using 1
      · simp [fabcNormal]
        ring
  rw [k_sq]
  grind

variable {r} in
theorem presingular (hr : r ≠ 0) {x y : ℂ} (hxy : (elliptic u r).Nonsingular x y)
    (h : (r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x = 0) :
    (2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y) ^ 2 =
    ((r * x + u) *
      (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2)) ^ 2 := by
  suffices (2 * r * ((u + r) ^ 2 - 1) * (r * x - u)) ^ 2 * (r ^ 2 * y ^ 2) =
    ((r * x + u) *
      (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2)) ^ 2 by
    linear_combination this
  rw [nonsingular_elliptic u hr] at hxy
  obtain ⟨heq, hs⟩ := hxy
  rw [heq]
  suffices ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x) *
      ( (4*r^6*x^3 - 4*r^6*x^2 + 8*r^5*u*x^3 - 8*r^5*u*x^2 + 4*r^4* u^2* x^3 - 8* r^4* u^2* x^2 +
      4* r^4* u^2* x - r^4 *x^4 - 4* r^4* x^3 + 8* r^4* x^2 - 8* r^3* u^3* x^2 + 8* r^3* u^3* x -
      4* r^3* u* x^3 + 8* r^3* u* x^2 - 4* r^2* u^4* x^2 + 4* r^2* u^4* x + 2* r^2* u^2* x^2 -
      4* r^2* u^2* x - 4 *r^2* x^2 - 4 *r* u^3* x - u^4)) = 0 by
    linear_combination this
  simp [h]

def SingularAbc (x y : ℂ) := fabcNormal u r x y = 0

variable {r} in
theorem SingularAbc.mk (hr : r ≠ 0) {x y : ℂ} (hxy : (elliptic u r).Nonsingular x y)
    (ha : -2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y +
      (r * x + u) * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2) = 0)
    (hc : (r * x + u) * ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x) = 0) :
    SingularAbc u r x y := by
  unfold SingularAbc
  unfold fabcNormal
  simp only [Matrix.cons_eq_zero_iff, Matrix.zero_empty, and_true]
  refine ⟨ha, ?_, hc⟩
  obtain h := fabcNormal_onCircle u hr hxy
  unfold fabcNormal at h
  rw [ha, hc] at h
  simpa using h

theorem SingularAbc.a_eq_zero {x y : ℂ} (h : SingularAbc u r x y) :
    -2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y +
    (r * x + u) * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2)
    = 0
  := congr($h 0)

theorem SingularAbc.y_eq {x y : ℂ} (h : SingularAbc u r x y) :
    2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y =
    (r * x + u) * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2) := by
  simpa [neg_add_eq_zero] using h.a_eq_zero

theorem SingularAbc.b_eq_zero {x y : ℂ} (h : SingularAbc u r x y) :
    k u r * ((2 * r ^ 2 * (r * x + u) * y +
    (r * x - u) * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2)))
    = 0
  := by
  simpa [fabcNormal] using congr($h 1)

theorem SingularAbc.y_eq' {x y : ℂ} (h : SingularAbc u r x y) :
    k u r * (2 * r ^ 2 * (r * x + u) * y) =
    -(k u r * ((r * x - u) *
      (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2))) := by
  apply eq_of_sub_eq_zero
  linear_combination h.b_eq_zero

variable {r} in
theorem SingularAbc.rx_add_u_ne_zero (hr : r ≠ 0) {x y : ℂ} (h : SingularAbc u r x y)
    (hxy : ((elliptic u r)).Nonsingular x y) : r * x + u ≠ 0 := by
  obtain ha := h.a_eq_zero
  rw [nonsingular_elliptic u hr] at hxy
  obtain ⟨heq, hs⟩ := hxy
  grind

variable {r} in
theorem SingularAbc.c_factor_eq_zero (hr : r ≠ 0) {x y : ℂ} (h : SingularAbc u r x y)
    (hxy : ((elliptic u r)).Nonsingular x y) :
    (r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x = 0 := by
  suffices r * x + u ≠ 0 by
    simpa [fabcNormal, this] using congr($h 2)
  exact h.rx_add_u_ne_zero u hr hxy

variable {r} in
theorem SingularAbc.c_factor_add (hr : r ≠ 0) {x1 y1 x2 y2 : ℂ}
    (h1 : SingularAbc u r x1 y1) (h2 : SingularAbc u r x2 y2)
    (hxy1 : ((elliptic u r)).Nonsingular x1 y1) (hxy2 : ((elliptic u r)).Nonsingular x2 y2)
    (h : x1 ≠ x2) (hur : u + r ≠ 0) :
    x1 + x2 = (2 * u * (u + r) ^ 2 - 4 * u) / ((u + r) ^ 2 * r) := by
  let p := Polynomial.C ((u + r) ^ 2 * r ^ 2) * Polynomial.X ^ 2
    + Polynomial.C (4 * u * r - 2 * u * r * (u + r) ^ 2) * Polynomial.X
    + Polynomial.C ((u + r) ^ 2 * u ^ 2)
  have hc2 : (u + r) ^ 2 * r ^ 2 ≠ 0 := by simp [hr, hur]
  have hdeg : p.natDegree = 2 := by
    unfold p
    compute_degree <;> grind
  have hp1 : Polynomial.eval x1 p = 0 := by
    simp [p]
    linear_combination h1.c_factor_eq_zero u hr hxy1
  have hp2 : Polynomial.eval x2 p = 0 := by
    simp [p]
    linear_combination h2.c_factor_eq_zero u hr hxy2
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
  have hroots : p.roots = {x1, x2} := by
    symm
    rw [ht, hu]
    suffices u = 0 by simpa
    obtain hcard := Polynomial.card_roots' p
    simpa [hdeg, ht, hu] using hcard
  obtain hxx := Polynomial.eq_neg_mul_add_of_roots_quadratic_eq_pair hroots
  field_simp
  rw [← mul_left_inj' hr]
  linear_combination hxx

variable {r} in
theorem SingularAbc.y_eq_reduced_aux (hr : r ≠ 0) {x y : ℂ} (h : SingularAbc u r x y)
    (hxy : ((elliptic u r)).Nonsingular x y) :
    r * (u + r) * (r * x - u) * y * ((u + r) ^ 2 - 1) =
    (u - r) * x * (r * x + u) * ((u + r) ^ 2 - 1) := by
  have h : r * (u + r) * (r * x - u) * y * ((u + r) ^ 2 - 1) * 2 * r =
    (u - r) * x * (r * x + u) * ((u + r) ^ 2 - 1) * 2 * r := by
    linear_combination (u + r) * (h.y_eq u r) + (r * x + u) * h.c_factor_eq_zero u hr hxy
  simpa [hr] using h

variable {u r} in
theorem SingularAbc.xy_linear (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (h : SingularAbc u r x y)
    (hxy : ((elliptic u r)).Nonsingular x y) :
    -2 * r ^ 2 * (u + r) * y = (u - r) * (r * ((u + r) ^ 2 - 2) * x - u * (u + r) ^ 2) := by
  by_cases h0 : (u + r) ^ 2 - 1 = 0
  · have h0' : (u + r) ^ 2 = 1 := by simpa [sub_eq_zero] using h0
    obtain hc := h.c_factor_eq_zero u hr hxy
    rw [h0'] at hc
    have hc' : (r * x + u) ^ 2 = 0 := by linear_combination hc
    have hc' : r * x + u = 0 := by simpa using hc'
    rw [nonsingular_elliptic u hr] at hxy
    obtain ⟨heq, hs⟩ := hxy
    have heq' : r ^ 2 * y ^ 2 = x * ((r * x + u) ^ 2 - ((u + r) ^ 2 - 1) * x) := by
      linear_combination heq
    have hy : y = 0 := by simpa [hc', h0', hr] using heq'
    suffices r * (1 - 2) * x - u = 0 by simp [hy, h0', this]
    linear_combination -hc'
  · have : -2 * r ^ 2 * (u + r) * y * ((u + r) ^ 2 - 1) * 2 * u ^ 2 =
      (u - r) * (r * ((u + r) ^ 2 - 2) * x - u * (u + r) ^ 2) * ((u + r) ^ 2 - 1) * 2 * u ^ 2 := by
      linear_combination
        r * ((r * (u + r) ^ 2 * x + 4 * u - u * (u + r) ^ 2) * h.y_eq_reduced_aux u hr hxy
        - r * (u + r) * y * ((u + r) ^ 2 - 1) * h.c_factor_eq_zero u hr hxy +
        (u - r) * x * ((u + r) ^ 2 - 1) * h.c_factor_eq_zero u hr hxy)
        + (u - r) * ((u + r) ^ 2 - 1) * 2 * u * h.c_factor_eq_zero u hr hxy
    simpa [hu, -neg_mul, h0] using this

variable {r} in
theorem SingularAbc.x_relation (hr : r ≠ 0) {x y : ℂ} (h : SingularAbc u r x y)
    (hxy : ((elliptic u r)).Nonsingular x y) :
    -(2 * u * k u r) ^ 2 = (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) ^ 2 := by
  simp_rw [mul_pow, k_sq]
  obtain h' := h.c_factor_eq_zero u hr hxy
  grind

variable {r} in
theorem SingularAbc.k_ne_zero (hr : r ≠ 0) {x y : ℂ} (h : SingularAbc u r x y)
    (hxy : ((elliptic u r)).Nonsingular x y) :
    k u r ≠ 0 := by
  by_contra! hk
  have hur : (u + r) ^ 2 = 1 := by
    obtain hk2 := congr($hk ^ 2)
    simpa [k_sq, sub_eq_zero] using hk2
  obtain hx := (h.x_relation u hr hxy)
  grind

variable {u r} in
theorem SingularAbc.fxyzRaw_eq (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (h : SingularAbc u r x y)
    (hxy : ((elliptic u r)).Nonsingular x y) (hur : u + r ≠ 0) :
    fxyzRaw u r (.some hxy) = ![
      2 * r * x * ((u + r) ^ 2 - 1) / (u + r) ^ 2 * (u ^ 2 - r ^ 2),
      2 * r * x * ((u + r) ^ 2 - 1) / (u + r) ^ 2 *
        ((r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) / (2 * u * k u r) * (u ^ 2 - r ^ 2)),
      2 * r * x * ((u + r) ^ 2 - 1) / (u + r) ^ 2 * (2 * u)] := by
  suffices
    r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r ^ 2 - r * u) * x + u ^ 2 * (u + r) =
      2 * r * x * ((u + r) ^ 2 - 1) / (u + r) ^ 2 * (u ^ 2 - r ^ 2) ∧
    -(2 * r ^ 2 * k u r * y) =
      2 * r * x * ((u + r) ^ 2 - 1) / (u + r) ^ 2 *
        ((r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) / (2 * u * k u r) * (u ^ 2 - r ^ 2)) ∧
    (r * x + u) ^ 2 = 2 * r * x * ((u + r) ^ 2 - 1) / (u + r) ^ 2 * (2 * u) by
    simpa [fxyzRaw]
  obtain hx := h.c_factor_eq_zero u hr hxy
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    grind
  · obtain hk := h.k_ne_zero u hr hxy
    obtain hy := h.y_eq
    have hrxu : r * x - u ≠ 0 := by grind
    field_simp
    rw [k_sq]
    rw [← mul_left_inj' hrxu]
    rw [← mul_left_inj' hr]
    suffices -(2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y) * u * (u + r) ^ 2 =
      x * ((u + r) ^ 2 - 1) *
      (r * x * (u + r) ^ 2 - u * ((u + r) ^ 2 - 2)) * (u ^ 2 - r ^ 2) * (r * x - u) * r by
      convert this using 1
      ring
    rw [hy]
    simp_rw [neg_mul, neg_eq_iff_add_eq_zero]
    suffices
      - (r + u) * (r^4 * x + r^3 * u * x - r^2 * u^2 * x - r^2 * x - r * u^3 * x - u^2) *
        ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x) = 0 by
      convert this using 1
      ring
    simp [hx]
  · field_simp
    grind

variable {u r} in
theorem SingularAbc.x_eq_zero_of_casePos (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ}
    (h : SingularAbc u r x y) (hxy : ((elliptic u r)).Nonsingular x y) (hur : u + r = 0) :
    x = 0 := by
  simpa [hur, hu, hr] using h.c_factor_eq_zero u hr hxy


variable {u r} in
theorem SingularAbc.y_eq_zero_of_casePos (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ}
    (h : SingularAbc u r x y) (hxy : ((elliptic u r)).Nonsingular x y) (hur : u + r = 0) :
    y = 0 := by
  obtain hx := h.x_eq_zero_of_casePos hu hr hxy hur
  rw [nonsingular_elliptic u hr] at hxy
  obtain ⟨heq, hs⟩ := hxy
  simpa [hx, hr] using heq

variable {u r} in
theorem SingularAbc.fxyzRaw_eq_of_casePos (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ}
    (h : SingularAbc u r x y) (hxy : ((elliptic u r)).Nonsingular x y) (hur : u + r = 0) :
  fxyzRaw u r (.some hxy) = ![0, 0, u ^ 2] := by
  obtain hx := h.x_eq_zero_of_casePos hu hr hxy hur
  obtain hy := h.y_eq_zero_of_casePos hu hr hxy hur
  simp [fxyzRaw, hx, hy, hur]

variable {u r} in
theorem SingularAbc.fxyz_eq (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (h : SingularAbc u r x y)
    (hxy : ((elliptic u r)).Nonsingular x y) :
    fxyz u hr (.some hxy) = P2.mk ![
      2 * u * k u r * (u ^ 2 - r ^ 2),
      ((r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * (u ^ 2 - r ^ 2)),
      4 * u ^ 2 * k u r] (by simp [hu, h.k_ne_zero u hr hxy]) := by
  by_cases hur : u + r = 0
  · have hur2 : u ^ 2 - r ^ 2 = 0 := by grind
    suffices P2.mk ![0, 0, u ^ 2] _ = P2.mk ![0, 0, 4 * u ^ 2 * k u r] _ by
      simpa [fxyz, h.fxyzRaw_eq_of_casePos hu hr hxy hur, hur, hur2]
    symm
    rw [P2.mk_eq_mk']
    use 4 * k u r
    simp [field]
  suffices P2.mk ![2 * r * x * ((u + r) ^ 2 - 1) / (u + r) ^ 2 * (u ^ 2 - r ^ 2),
      2 * r * x * ((u + r) ^ 2 - 1) / (u + r) ^ 2 *
        ((r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) / (2 * u * k u r) * (u ^ 2 - r ^ 2)),
      2 * r * x * ((u + r) ^ 2 - 1) / (u + r) ^ 2 * (2 * u)] _ =
    P2.mk ![2 * u * k u r * (u ^ 2 - r ^ 2),
    (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * (u ^ 2 - r ^ 2),
      4 * u ^ 2 * k u r]
    _ by
    simpa [fxyz, h.fxyzRaw_eq hu hr hxy hur]
  rw [P2.mk_eq_mk']
  use r * x * ((u + r) ^ 2 - 1) / ((u + r) ^ 2 * u * k u r)
  simp only [Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty, Matrix.vecCons_inj, and_true]
  obtain hk := h.k_ne_zero u hr hxy
  refine ⟨?_, ?_, ?_⟩
  · field
  · field
  · field


variable {u} in
theorem singularAbc_zero_iff (hu : u ≠ 0) : SingularAbc u r 0 0 ↔ u + r = 0 := by
  simp [SingularAbc, fabcNormal, hu, imp_and, imp_or]

open Classical in
noncomputable
def fabcRaw (p : (elliptic u r).Point) : Fin 3 → ℂ := match p with
| .zero => ![1, -k u r, u + r]
| .some (x := x) (y := y) _ =>
  if SingularAbc u r x y then
    ![2 * u * k u r * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u ^ 2),
      (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * ((u ^ 2 - r ^ 2) ^ 2 - 4 * u ^ 2),
      8 * u ^ 2 * k u r * (u ^ 2 - r ^ 2)]
  else
    fabcNormal u r x y

@[simp]
theorem fabcRaw_zero : fabcRaw u r .zero = ![1, -k u r, u + r] := by simp [fabcRaw]

@[simp]
theorem fabcRaw_zero' : fabcRaw u r 0 = ![1, -k u r, u + r] := fabcRaw_zero u r

variable {u r} in
theorem SingularAbc.fabcRaw_ne_zero (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ}
    (h : SingularAbc u r x y) (hxy : (elliptic u r).Nonsingular x y) :
    fabcRaw u r (Point.some hxy) ≠ 0 := by
  obtain hk := h.k_ne_zero u hr hxy
  by_cases hur : u ^ 2 - r ^ 2 = 0
  · suffices fabcRaw u r (Point.some hxy) 0 ≠ 0 by
      contrapose! this
      simp [this]
    simp [fabcRaw, h, hk, hu, hur]
  · suffices fabcRaw u r (Point.some hxy) 2 ≠ 0 by
      contrapose! this
      simp [this]
    simp [fabcRaw, h, hk, hu, hur]

variable {u r} in
noncomputable
def fabc (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) : P2 :=
    P2.mk (fabcRaw u r p) <| by
  cases p with
  | zero =>
    simp [fabcRaw]
  | @some x y hxy =>
    by_cases h0 : SingularAbc u r x y
    · exact h0.fabcRaw_ne_zero hu hr hxy
    · suffices fabcNormal u r x y ≠ 0 by simpa [fabcRaw, h0]
      exact h0

variable {u r} in
theorem SingularAbc.fabc_eq (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ}
    (h : SingularAbc u r x y) (hxy : (elliptic u r).Nonsingular x y) :
    fabc hu hr (.some hxy) = P2.mk ![2 * u * k u r * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u ^ 2),
      (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * ((u ^ 2 - r ^ 2) ^ 2 - 4 * u ^ 2),
      8 * u ^ 2 * k u r * (u ^ 2 - r ^ 2)]
      (by simpa [fabcRaw, h] using h.fabcRaw_ne_zero hu hr hxy) := by
  simp [fabc, fabcRaw, h]

variable {u r} in
@[simp]
theorem fabc_zero (hu : u ≠ 0) (hr : r ≠ 0) :
    fabc hu hr .zero = P2.mk ![1, -k u r, u + r] (by simp) := by
  simp [fabc]

variable {u r} in
@[simp]
theorem fabc_zero' (hu : u ≠ 0) (hr : r ≠ 0) :
    fabc hu hr 0 = P2.mk ![1, -k u r, u + r] (by simp) := fabc_zero hu hr

variable {u r} in
theorem innerCircle_fabc (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) :
    InnerCircle (fabc hu hr p) := by
  change fabcRaw u r p 0 ^ 2 + fabcRaw u r p 1 ^ 2 = fabcRaw u r p 2 ^ 2
  cases p with
  | zero =>
    simp [fabcRaw, k_sq]
  | @some x y hxy =>
    by_cases hsingular : SingularAbc u r x y
    · suffices
        (2 * u * k u r) ^ 2 * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u ^ 2) ^ 2 +
        (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) ^ 2 * ((u ^ 2 - r ^ 2) ^ 2 - 4 * u ^ 2) ^ 2 =
        (2 * u * k u r) ^ 2 * (4 * u * (u ^ 2 - r ^ 2)) ^ 2 by
        convert this using 1
        · simp [fabcRaw, hsingular]
          ring
        · simp [fabcRaw, hsingular]
          ring
      rw [← hsingular.x_relation u hr hxy]
      ring
    rw [nonsingular_elliptic u hr] at hxy
    obtain ⟨heq, hs⟩ := hxy
    simpa [fabcRaw, hsingular] using fabcNormal_onCircle u hr hxy

variable {u r} in
theorem incidence_fxyz_fabc (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) :
    Incidence (fxyz u hr p) (fabc hu hr p) := by
  change fxyzRaw u r p 0 * fabcRaw u r p 0 + fxyzRaw u r p 1 * fabcRaw u r p 1 =
    fxyzRaw u r p 2 * fabcRaw u r p 2
  cases p with
  | zero =>
    simp [fabcRaw, fxyzRaw]
  | @some x y hxy =>
    by_cases hsingular : SingularAbc u r x y
    · by_cases hur : u + r = 0
      · have hur2 : u ^ 2 - r ^ 2 = 0 := by grind
        simp [hsingular.fxyzRaw_eq_of_casePos hu hr hxy hur, fabcRaw, hsingular, hur2]
      simp_rw [hsingular.fxyzRaw_eq hu hr hxy hur]
      suffices
        2 * r * x * ((u + r) ^ 2 - 1) / (u + r) ^ 2 * ((u ^ 2 - r ^ 2) * fabcRaw u r (.some hxy) 0 +
          ((r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) / (2 * u * k u r) * (u ^ 2 - r ^ 2)) *
          fabcRaw u r (.some hxy) 1) =
        2 * r * x * ((u + r) ^ 2 - 1) / (u + r) ^ 2 * ((2 * u) * fabcRaw u r (.some hxy) 2) by
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val]
        convert this using 1
        · ring
        · ring
      congrm(_ * ?_)
      obtain hk := hsingular.k_ne_zero u hr hxy
      suffices (u ^ 2 - r ^ 2) *
        (u ^ 2 * 2 ^ 2 * k u r ^ 2 * ((u ^ 2 - r ^ 2) ^ 2 + u ^ 2 * 4) +
        (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) ^ 2 * ((u ^ 2 - r ^ 2) ^ 2 - u ^ 2 * 4)) =
         u ^ 4 * (u ^ 2 - r ^ 2) * 2 ^ 2 * k u r ^ 2 * 8 by
        simpa [fabcRaw, hsingular, field]
      rw [← hsingular.x_relation u hr hxy]
      ring
    rw [nonsingular_elliptic u hr] at hxy
    obtain ⟨heq, hs⟩ := hxy
    suffices (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r ^ 2 - r * u) * x + u ^ 2 * (u + r)) *
      (-(2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y) +
        (r * x + u) * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2)) +
        2 * r ^ 2 * k u r ^ 2 * y *
      ((2 * r ^ 2 * (r * x + u) * y +
          (r * x - u) * (r ^ 2 * (u + r) * x ^ 2 +
            2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2))) =
      (r * x + u) ^ 2 * ((r * x + u) * ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x)) by
      convert this using 1
      · simp [fxyzRaw, fabcRaw, hsingular, fabcNormal]
        ring
      · simp [fxyzRaw, fabcRaw, hsingular, fabcNormal]
    rw [k_sq]
    grind

variable {u r} in
noncomputable
def f (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) : P2 × P2 :=
  ⟨fxyz u hr p, fabc hu hr p⟩

variable {u r} in
@[simp]
theorem f_zero (hu : u ≠ 0) (hr : r ≠ 0) :
    f hu hr .zero = ⟨P2.mk ![u + r, 0, 1] (by simp), P2.mk ![1, -k u r, u + r] (by simp)⟩ := by
  simp [f]


variable {u r} in
theorem mapsTo_f (hu : u ≠ 0) (hr : r ≠ 0) : Set.MapsTo (f hu hr) Set.univ (dom u r) :=
  fun p _ ↦ ⟨outerCircle_fxyz u hr p, innerCircle_fabc hu hr p, incidence_fxyz_fabc hu hr p⟩

variable {u r} in
def o (hu : u ≠ 0) (hr : r ≠ 0) : (elliptic u r).Point :=
  .some (show (elliptic u r).Nonsingular 0 0 by simp [elliptic, hu, hr])

variable {u r} in
@[simp]
theorem fxyzRaw_o (hu : u ≠ 0) (hr : r ≠ 0) : fxyzRaw u r (o hu hr) =
    ![u ^ 2 * (u + r), 0, u ^ 2] := by
  simp [fxyzRaw, o]

variable {u r} in
@[simp]
theorem fxyz_o (hu : u ≠ 0) (hr : r ≠ 0) : fxyz u hr (o hu hr) =
    P2.mk ![(u + r), 0, 1] (by simp) := by
  suffices P2.mk ![u ^ 2 * (u + r), 0, u ^ 2] _ = P2.mk ![u + r, 0, 1] _ by
    simpa [fxyz]
  rw [P2.mk_eq_mk']
  use u ^ 2
  simp

variable {u r} in
@[simp]
theorem fabc_o (hu : u ≠ 0) (hr : r ≠ 0) :
    fabc hu hr (o hu hr) = P2.mk ![1, k u r, u + r] (by simp) := by
  by_cases hsingular : SingularAbc u r 0 0
  · obtain huv := (singularAbc_zero_iff r hu).mp hsingular
    have hreq : r = -u := (neg_eq_of_add_eq_zero_right huv).symm
    have hk : k u r ^ 2 = -1 := by simp [k_sq, huv]
    unfold fabc
    rw [P2.mk_eq_mk']
    use 4 * u ^ 2 * k u r * (u - r)
    suffices 2 * u * k u r * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u ^ 2) = 4 * u ^ 2 * k u r * (u - r) ∧
      -(u * ((u + r) ^ 2 - 2) * ((u ^ 2 - r ^ 2) ^ 2 - 4 * u ^ 2)) =
        4 * u ^ 2 * k u r * (u - r) * k u r ∧
      8 * u ^ 2 * k u r * (u ^ 2 - r ^ 2) = 4 * u ^ 2 * k u r * (u - r) * (u + r) by
      simpa [fabcRaw, o, hsingular]
    grind
  unfold fabc
  rw [P2.mk_eq_mk']
  simp [fabcRaw, o, hsingular, fabcNormal]
  grind

variable {u r} in
@[simp]
theorem f_o (hu : u ≠ 0) (hr : r ≠ 0) :
    f hu hr (o hu hr) = ⟨P2.mk ![u + r, 0, 1] (by simp), P2.mk ![1, k u r, u + r] (by simp)⟩ := by
  simp [f]

variable {u r} in
theorem eq_o_iff (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (h : (elliptic u r).Nonsingular x y) :
    .some h = o hu hr ↔ x = 0 where
  mp h0 := by
    have : x = 0 ∧ y = 0 := by simpa [o] using h0
    exact this.1
  mpr h0 := by
    suffices y = 0 by simp [this, o, h0]
    rw [nonsingular_elliptic u hr] at h
    obtain ⟨heq, hs⟩ := h
    simpa [h0, hr] using heq

variable {u r} in
theorem nonsingular_o_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (h : (elliptic u r).Nonsingular x y) :
    (elliptic u r).Nonsingular (u ^ 2 / (r ^ 2 * x)) (u ^ 2 * y / (r ^ 2 * x ^ 2)) := by
  rw [nonsingular_elliptic u hr] at ⊢ h
  grind

variable {u r} in
theorem o_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (h : (elliptic u r).Nonsingular x y)
    (ho : Point.some h ≠ o hu hr) :
    o hu hr - Point.some h = Point.some (nonsingular_o_sub hu hr h) := by
  obtain hx0 := (eq_o_iff hu hr h).ne.mp ho
  rw [nonsingular_elliptic u hr] at h
  obtain ⟨heq, hs⟩ := h
  rw [sub_eq_iff_eq_add]
  by_cases hx : u ^ 2 / (r ^ 2 * x) = x
  · have hx' : r ^ 2 * x ^ 2 = u ^ 2 := by
      rw [div_eq_iff (by simp [hr, hx0])] at hx
      rw [hx]
      ring
    have hy0 : y ≠ 0 := by grind
    have hy : u ^ 2 * y / (r ^ 2 * x ^ 2) ≠ (elliptic u r).negY x y := by
      suffices u ^ 2 * y / (r ^ 2 * x ^ 2) ≠ -y by simpa [elliptic]
      rw [hx']
      rw [mul_div_cancel_left_of_imp (by simp [hu])]
      exact self_ne_neg.mpr hy0
    rw [Point.add_of_Y_ne hy]
    obtain hslope := WeierstrassCurve.Affine.slope_of_Y_ne hx hy
    simp_rw [o, Point.some.injEq, addX, hslope]
    simp only [elliptic, zero_mul, sub_zero, negY, sub_neg_eq_add, add_zero, addY, negAddY, addX,
      neg_add_rev]
    constructor
    · field_simp
      grind
    · rw [mul_comm, ← eq_div_iff_mul_eq (by simpa using hr), ← div_pow] at hx'
      obtain hx' | hx' := eq_or_eq_neg_of_sq_eq_sq _ _ hx'
      all_goals
      rw [hx']
      field_simp
      grind
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  have : u ^ 2 - r ^ 2 * x ^ 2 ≠ 0 := by grind
  simp only [elliptic, o, addX, ne_eq, hx, not_false_eq_true, slope_of_X_ne, zero_mul, add_zero,
    addY, negY, negAddY, neg_add_rev, sub_zero, Point.some.injEq]
  constructor
  · field_simp
    grind
  · field_simp
    grind

variable {u r} in
theorem nonsingular_w (hu : u ≠ 0) (hr : r ≠ 0) :
    (elliptic u r).Nonsingular (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 3) := by
  rw [nonsingular_elliptic u hr]
  refine ⟨?_, Or.inr (by simp [hu, hr])⟩
  field

variable {u r} in
noncomputable
def w (hu : u ≠ 0) (hr : r ≠ 0) : (elliptic u r).Point := .some (nonsingular_w hu hr)


variable {u r} in
theorem slope_w (hu : u ≠ 0) (hr : r ≠ 0) :
    (elliptic u r).slope (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 3) (u ^ 2 / r ^ 3) =
    (2 + u ^ 2 - r ^ 2) / (2 * r) := by
  unfold elliptic
  rw [slope_of_Y_ne rfl (by simp [self_eq_neg, hu, hr])]
  simp
  field

variable {u r} in
theorem addX_w_w (hu : u ≠ 0) (hr : r ≠ 0) :
    (elliptic u r).addX (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 2)
      ((elliptic u r).slope (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 3) (u ^ 2 / r ^ 3))
      = (r ^ 2 - u ^ 2) ^ 2 / (4 * r ^ 2) := by
  rw [slope_w hu hr]
  unfold addX elliptic
  simp
  field

variable {u r} in
theorem addY_w_w (hu : u ≠ 0) (hr : r ≠ 0) :
    (elliptic u r).addY (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 3)
      ((elliptic u r).slope (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 3) (u ^ 2 / r ^ 3))
      = (r ^ 2 - u ^ 2) * ((r ^ 2 - u ^ 2) ^ 2 - 2 * (r ^ 2 + u ^ 2)) / (8 * r ^ 3) := by
  rw [slope_w hu hr]
  unfold addY elliptic
  simp
  field

variable {u r} in
theorem nonsingular_2w (hu : u ≠ 0) (hr : r ≠ 0) :
    (elliptic u r).Nonsingular ((r ^ 2 - u ^ 2) ^ 2 / (4 * r ^ 2))
    ((r ^ 2 - u ^ 2) * ((r ^ 2 - u ^ 2) ^ 2 - 2 * (r ^ 2 + u ^ 2)) / (8 * r ^ 3)) := by
  rw [← addX_w_w hu hr, ← addY_w_w hu hr]
  apply nonsingular_add (nonsingular_w hu hr) (nonsingular_w hu hr)
  simp [elliptic, self_eq_neg, hu, hr]


variable {u r} in
theorem two_w (hu : u ≠ 0) (hr : r ≠ 0) :
    w hu hr + w hu hr = .some (nonsingular_2w hu hr) := by
  unfold w
  rw [Point.add_self_of_Y_ne (by simp [elliptic, self_eq_neg, hu, hr])]
  congr
  · apply addX_w_w hu hr
  · apply addY_w_w hu hr

variable {u r} in
theorem slope_w_sub (hu : u ≠ 0) (hr : r ≠ 0) {x : ℂ} (hx : x ≠ u ^ 2 / r ^ 2)
    (y : ℂ) : (elliptic u r).slope (u ^ 2 / r ^ 2) x (u ^ 2 / r ^ 3) (-y) =
    (u ^ 2 + r ^ 3 * y) / (u ^ 2 * r - r ^ 3 * x) := by
  rw [slope_of_X_ne hx.symm]
  have : u ^ 2 - r ^ 2 * x ≠ 0 := by grind
  field

variable {u r} in
theorem addX_w_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (hxy : (elliptic u r).Nonsingular x y)
    (hx : x ≠ u ^ 2 / r ^ 2) :
    (elliptic u r).addX (u ^ 2 / r ^ 2) x
      ((elliptic u r).slope (u ^ 2 / r ^ 2) x (u ^ 2 / r ^ 3) (-y)) =
    u ^ 2 * (r ^ 2 * x ^ 2 + (2 - r ^ 2 - u ^ 2) * x + u ^ 2 + 2 * r * y)
      / (r ^ 2 * x - u ^ 2) ^ 2 := by
  have : r ^ 2 * x - u ^ 2 ≠ 0 := by grind
  have : u ^ 2 - r ^ 2 * x ≠ 0 := by grind
  rw [slope_w_sub hu hr hx]
  simp only [addX, elliptic, zero_mul, add_zero]
  rw [nonsingular_elliptic u hr] at hxy
  obtain ⟨heq, hnonsingular⟩ := hxy
  field_simp
  linear_combination  r ^ 4 * (r ^ 2 * x - u ^ 2) ^ 2 * heq

variable {u r} in
theorem addY_w_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (hxy : (elliptic u r).Nonsingular x y)
    (hx : x ≠ u ^ 2 / r ^ 2) :
    (elliptic u r).addY (u ^ 2 / r ^ 2) x (u ^ 2 / r ^ 3)
      ((elliptic u r).slope (u ^ 2 / r ^ 2) x (u ^ 2 / r ^ 3) (-y)) =
      u ^ 2 *
        (r ^ 4 * x ^ 3 + r ^ 2 * (2 + u ^ 2 - 2 * r ^ 2) * x ^ 2
          + u ^ 2 * (2 - 2 * u ^ 2 + r ^ 2) * x + u ^ 4
          + (r ^ 2 * (2 + u ^ 2 - r ^ 2) * x + u ^ 2 * (2 - u ^ 2 + r ^ 2)) * r * y)
      / (r * (r ^ 2 * x - u ^ 2) ^ 3) := by
  have : r ^ 2 * x - u ^ 2 ≠ 0 := by grind
  have : u ^ 2 - r ^ 2 * x ≠ 0 := by grind
  rw [addY, negAddY, addX_w_sub hu hr hxy hx]
  rw [slope_w_sub hu hr hx]
  simp only [negY, neg_add_rev, elliptic, zero_mul, sub_zero]
  rw [nonsingular_elliptic u hr] at hxy
  obtain ⟨heq, hnonsingular⟩ := hxy
  field_simp
  linear_combination (-2) * r^4 * (r^2*x - u^2) * heq

variable {u r} in
theorem nonsingular_w_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (hxy : (elliptic u r).Nonsingular x y)
    (hx : x ≠ u ^ 2 / r ^ 2) :
    (elliptic u r).Nonsingular
      (u ^ 2 * (r ^ 2 * x ^ 2 + (2 - r ^ 2 - u ^ 2) * x + u ^ 2 + 2 * r * y)
      / (r ^ 2 * x - u ^ 2) ^ 2)
    (u ^ 2 *
        (r ^ 4 * x ^ 3 + r ^ 2 * (2 + u ^ 2 - 2 * r ^ 2) * x ^ 2
          + u ^ 2 * (2 - 2 * u ^ 2 + r ^ 2) * x + u ^ 4
          + (r ^ 2 * (2 + u ^ 2 - r ^ 2) * x + u ^ 2 * (2 - u ^ 2 + r ^ 2)) * r * y)
      / (r * (r ^ 2 * x - u ^ 2) ^ 3)) := by
  have hnegy : (elliptic u r).negY x y = -y := by simp [elliptic]
  have : ¬(u ^ 2 / r ^ 2 = x ∧
      u ^ 2 / r ^ 3 = (elliptic u r).negY x ((elliptic u r).negY x y)) := by
    simp [hx.symm]
  convert (elliptic u r).nonsingular_add (nonsingular_w hu hr) ((nonsingular_neg _ _).mpr hxy) this
      using 1
  · simp_rw [hnegy]
    rw [addX_w_sub hu hr hxy hx]
  · simp_rw [hnegy]
    rw [addY_w_sub hu hr hxy hx]

variable {u r} in
theorem w_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (hxy : (elliptic u r).Nonsingular x y)
    (hx : x ≠ u ^ 2 / r ^ 2) :
    w hu hr - .some hxy = .some (nonsingular_w_sub hu hr hxy hx) := by
  have hxy' : (elliptic u r).Nonsingular x (-y) := by
    simpa [elliptic] using (WeierstrassCurve.Affine.nonsingular_neg _ _).mpr hxy
  have hneg : - Point.some hxy = .some hxy' := by simp [elliptic]
  rw [sub_eq_add_neg, hneg]
  unfold w
  rw [Point.add_of_X_ne hx.symm]
  rw [Point.some.injEq]
  rw [addX_w_sub hu hr hxy hx]
  rw [addY_w_sub hu hr hxy hx]
  simp

variable {u r} in
theorem nonsingular_neg_w (hu : u ≠ 0) (hr : r ≠ 0) :
    (elliptic u r).Nonsingular (u ^ 2 / r ^ 2) (-u ^ 2 / r ^ 3)  := by
  convert (WeierstrassCurve.Affine.nonsingular_neg _ _).mpr (nonsingular_w hu hr) using 1
  simp [elliptic, neg_div]

variable {u r} in
theorem neg_w (hu : u ≠ 0) (hr : r ≠ 0) :
    -w hu hr = .some (nonsingular_neg_w hu hr) := by
  simp [w, elliptic, neg_div]


variable {u r} in
theorem x_not_at_w (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (hxy : (elliptic u r).Nonsingular x y)
    (hpw : .some hxy ≠ w hu hr) (hpnw : .some hxy ≠ -w hu hr) :
    x ≠ u ^ 2 / r ^ 2 := by
  obtain ⟨heq, hnonsingular⟩ := (nonsingular_elliptic u hr _ _).mp hxy
  unfold w at hpw hpnw
  by_contra! h
  have h1 : y ≠ u ^ 2 / r ^ 3 := by simpa [h] using hpw
  have h2 : y ≠ -(u ^ 2 / r ^ 3) := by simpa [elliptic, h] using hpnw
  simp_rw [h] at heq
  field_simp at heq
  have hy : (r ^ 3 * y) ^ 2 = (u ^ 2) ^ 2 := by linear_combination heq
  obtain hy | hy := eq_or_eq_neg_of_sq_eq_sq _ _ hy
  · contrapose! h1
    field_simp
    linear_combination hy
  · contrapose! h2
    field_simp
    linear_combination hy
/-
def placeholder : ℂ := sorry

variable {u r} in
theorem SingularAbc.wx_eq (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ}
    (h : SingularAbc u r x y)
    (hxy : (elliptic u r).Nonsingular x y)
    (hx : x ≠ u ^ 2 / r ^ 2) :
    u ^ 2 * (r ^ 2 * x ^ 2 + (2 - r ^ 2 - u ^ 2) * x + u ^ 2 + 2 * r * y)
      / (r ^ 2 * x - u ^ 2) ^ 2 = placeholder := by
  have : r ^ 2 * x - u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  field_simp
  obtain hx := h.c_factor_eq_zero u hr hxy
  have h1 : (r ^ 2 * (u + r) ^ 2 * x +
    4 * u * r - 2 * u * r * (u + r) ^ 2 + u ^ 2 * (u + r) ^ 2) ≠ 0 := by sorry
  rw [← mul_right_inj' h1, ← mul_right_inj' h1]
  have h2 : r * (u + r)  ≠ 0 := by sorry
  rw [← mul_right_inj' h2]

  suffices
    (r ^ 2 * (u + r) ^ 2 * x + 4 * u * r - 2 * u * r * (u + r) ^ 2 + u ^ 2 * (u + r) ^ 2) ^ 2 *
    ((u ^ 2 * (r * (u + r) * x * (r ^ 2 * x + (2 - r ^ 2 - u ^ 2)) + r * (u + r) * u ^ 2 -
      -2 * r ^ 2 * (u + r) * y))) =
    ((r ^ 2 * (u + r) ^ 2 * x + 4 * u * r - 2 * u * r * (u + r) ^ 2 + u ^ 2 * (u + r) ^ 2)
      * (r ^ 2 * x - u ^ 2)) ^ 2 *
    r * (u + r) * (placeholder) by
    linear_combination this

  have : (r ^ 2 * (u + r) ^ 2 * x + 4 * u * r - 2 * u * r * (u + r) ^ 2 + u ^ 2 * (u + r) ^ 2)
      * (r ^ 2 * x - u ^ 2) = - u ^ 2 * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r) := by
    linear_combination r ^ 2 * hx
  rw [this]
  rw [h.xy_linear hu hr hxy]

  suffices (u + r) * u^4 * (
    -2 * (u - r) * r * x * (u + r)^3 * ((u ^ 2 - r ^ 2) ^ 2 - 2 * (u ^ 2 + r ^ 2))
       + u * ((u ^ 2 - r ^ 2) ^ 2 - 4 * r ^ 2)
       * ((u - r) * (u + 3 * r) * (u + r) ^ 2 + 4 * r ^ 2))
    = (-u ^ 2 * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r)) ^ 2 * r * (u + r) * placeholder by
    linear_combination this - (- u^2 * x^2 * (u + r)^3 * r^5 * hx
      - (-2) * u^3 * (u + r) * x * r^3 * (u^2*r + 2*u*r^2 + r^3 - 2*u - 4*r) * hx
      - (-1) * u^3 * r * (3*u^6 + 4*u^5*r - 6*u^4*r^2 - 11*u^3*r^3 - 2*u^2*r^4 +
      3*u*r^5 + r^6 - 8*u^4 + 16*u^2*r^2 + 8*u*r^3 - 16*u*r) * hx)

  sorry-/

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
