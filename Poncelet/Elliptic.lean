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
theorem SingularAbc.c_factor_eq_zero (hr : r ≠ 0) {x y : ℂ} (h : SingularAbc u r x y)
    (hxy : ((elliptic u r)).Nonsingular x y) :
    (r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x = 0 := by
  suffices r * x + u ≠ 0 by
    simpa [fabcNormal, this] using congr($h 2)
  obtain ha := h.a_eq_zero
  rw [nonsingular_elliptic u hr] at hxy
  obtain ⟨heq, hs⟩ := hxy
  grind

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

variable {r} in
theorem fabcNormal_o_sub (hr : r ≠ 0) (x y : ℂ) (hx : x ≠ 0) :
    fabcNormal u r (u ^ 2 / (r ^ 2 * x)) (u ^ 2 * y / (r ^ 2 * x ^ 2)) = (u ^ 3 / (r ^ 3 * x ^ 3)) •
    ![2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y +
      (r * x + u) * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2),
    -k u r * (2 * r ^ 2 * (r * x + u) * y -
      (r * x - u) * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2)),
    (r * x + u) * ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x)] := by
  unfold fabcNormal
  simp only [Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty]
  congrm ![?_, ?_, ?_]
  · field
  · field
  · field


variable {u r} in
theorem fxyz_o_sub (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) :
    fxyz u hr (o hu hr - p) = fxyz u hr p := by
  have hp0 : fxyz u hr (o hu hr) = fxyz u hr 0 := by
    suffices P2.mk ![u ^ 2 * (u + r), 0, u ^ 2] _ = P2.mk ![u + r, 0, 1] _ by
      simpa [o, fxyz, fxyzRaw]
    rw [P2.mk_eq_mk]
    use u ^ 2
    simpa using hu
  cases p with
  | zero =>
    change fxyz u hr (o hu hr - 0) = fxyz u hr 0
    simp
  | @some x y hxy =>
    rw [nonsingular_elliptic u hr] at hxy
    obtain ⟨heq, hs⟩ := hxy
    by_cases hx0 : x = 0
    · rw [(eq_o_iff hu hr hxy).mpr hx0]
      simp
    have hxo : Point.some hxy ≠ o hu hr := (eq_o_iff hu hr hxy).ne.mpr hx0
    unfold fxyz
    rw [P2.mk_eq_mk]
    use u ^ 2 / (r ^ 2 * x ^ 2)
    refine ⟨by simp [hr, hu, hx0], ?_⟩
    rw [o_sub hu hr hxy hxo]
    simp only [fxyzRaw, smul_eq_mul, Matrix.smul_cons, Matrix.smul_empty,
      Matrix.vecCons_inj, and_true]
    refine ⟨?_, ?_, ?_⟩
    · field
    · field
    · field

variable {u} in
theorem f_o_sub_1 (hu : u ≠ 0) (i : ℂ) :
    P2.mk' ![1, i * k u r, u + r] =
    P2.mk' (rChord' u r ![u + r, 0, 1] ![1, -i * k u r, u + r]) := by
  by_cases hur : u + r = 0
  · have hur' : r ^ 2 - u ^ 2 = 0 := by grind
    simp [rChord', hur, hur']
  have hur' : 2 * u * (u + r) + r ^ 2 - u ^ 2 ≠ 0 := by grind
  symm
  apply P2.mk'_eq_mk' hur'
  suffices 2 * (u + r) * (u + r) - (2 * u * (u + r) + r ^ 2 - u ^ 2) =
      2 * u * (u + r) + r ^ 2 - u ^ 2 by
    simpa [rChord', hur']
  ring

variable {u r} in
theorem SingularAbc.fabc_o_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ}
    (h : SingularAbc u r x y) (hxy : (elliptic u r).Nonsingular x y)
    (ho : Point.some hxy ≠ o hu hr) :
    fabc hu hr (o hu hr - .some hxy) = P2.mk ![8 * u ^ 3 * k u r,
      4 * (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * u ^ 2, 0]
      (by simp [hu, h.k_ne_zero u hr hxy]) := by
  have hx0 : x ≠ 0 := (eq_o_iff hu hr hxy).ne.mp ho
  rw [o_sub hu hr _ ho]
  by_cases hs : SingularAbc u r (u ^ 2 / (r ^ 2 * x)) (u ^ 2 * y / (r ^ 2 * x ^ 2))
  · obtain hy := h.y_eq
    obtain hy' := congr(r ^ 3 * x ^ 3 / u ^ 3 * $hs.y_eq)
    have hy' : -2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y =
        (r * x + u) * (r ^ 2 * (u + r) * x ^ 2 +
        2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2) := by
      convert hy' using 1
      · field
      · field
    have hy0 : 4 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y = 0 := by
      linear_combination hy - hy'
    obtain hx := h.c_factor_eq_zero u hr hxy
    have hrxu : r * x - u ≠ 0 := by grind
    rw [nonsingular_elliptic u hr] at hxy
    obtain ⟨heq, hnonsingular⟩ := hxy
    have hy0 : y = 0 := by
      obtain hur1 | hy0 : (u + r) ^ 2 - 1 = 0 ∨ y = 0 := by simpa [hrxu, hr] using hy0
      · have hur1' : (u + r) ^ 2 = 1 := sub_eq_zero.mp hur1
        rw [hur1'] at hx
        have hrxu : (r * x + u) ^ 2 = 0 := by linear_combination hx
        have hrxu : -(r * x) = u := by simpa [neg_eq_iff_add_eq_zero] using hrxu
        have hrxu : x = -u / r := by simp [← hrxu, hr]
        have hrxu' : x * (r ^ 2 * x ^ 2 + (1 - u ^ 2 - r ^ 2) * x + u ^ 2) = 0 := by
          suffices r ^ 2 * (-u / r) ^ 2 + (1 - u ^ 2 - r ^ 2) * (-u / r) + u ^ 2 = 0
            by simpa [hrxu, hr, hu]
          field_simp
          convert congr(u * $hur1) using 1
          · ring
          · ring
        simpa [hrxu', hr] using heq
      exact hy0
    have hx : r ^ 2 * x ^ 2 + (1 - u ^ 2 - r ^ 2) * x + u ^ 2 = 0 := by
      simpa [hy0, hx0] using heq
    obtain hrxu | hrxu : r * x + u = 0 ∨
        r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2 = 0 := by
      simpa [hy0] using hy
    · grind
    have hurx : (u - r) * ((u + r) ^ 2 - 1) * x = 0 := by
      linear_combination hrxu - hx * (u + r)
    obtain hur | hur : u - r = 0 ∨ (u + r) ^ 2 - 1 = 0 := by simpa [hx0] using hurx
    · have hu : u = r := sub_eq_zero.mp hur
      have hs : SingularAbc r r (r ^ 2 / (r ^ 2 * x)) (r ^ 2 * y / (r ^ 2 * x ^ 2)) := by
        simpa [hu] using hs
      suffices P2.mk ![2 * r * k r r * (4 * r ^ 2),
        -((r * (r + r) ^ 2 * (r ^ 2 / (r ^ 2 * x)) - r * ((r + r) ^ 2 - 2)) * (4 * r ^ 2)), 0] _ =
        P2.mk ![8 * r ^ 3 * k r r,
        4 * (r * (r + r) ^ 2 * x - r * ((r + r) ^ 2 - 2)) * r ^ 2, 0] _ by
        simpa [fabc, fabcRaw, hs, hu]
      congrm P2.mk ![$(by ring), ?_, 0] _
      apply eq_of_sub_eq_zero
      rw [← mul_left_inj' hx0]
      convert congr(-16 * r ^ 3 * $hx) using 1
      · simp_rw [hu]
        field
      · simp
    have hur : (u + r) ^ 2 = 1 := sub_eq_zero.mp hur
    have hk : k u r = 0 := by simpa [hur] using k_sq u r
    suffices P2.mk ![0,
        (r * (u ^ 2 / (r ^ 2 * x)) - u * (1 - 2)) * ((u ^ 2 - r ^ 2) ^ 2 - 4 * u ^ 2), 0] _ =
        P2.mk ![0, 4 * (r * x - u * (1 - 2)) * u ^ 2, 0] _ by
      simpa [fabc, fabcRaw, hs, hk, hur]
    rw [P2.mk_eq_mk']
    grind
  simp only [fabc, fabcRaw, hs, ↓reduceIte]
  simp_rw [← P2.mk'_eq]
  rw [fabcNormal_o_sub u hr x y hx0]
  rw [P2.mk'_smul (by simp [hu, hr, hx0])]
  rw [h.c_factor_eq_zero u hr hxy, mul_zero]
  rw [← h.y_eq, ← two_mul]
  rw [mul_sub (-k u r)]
  simp_rw [neg_mul]
  rw [← h.y_eq', ← neg_add', ← two_mul]
  have : y ≠ 0 ∧ (u + r) ^ 2 - 1 ≠ 0 ∧ r * x - u ≠ 0 := by
    contrapose! hs
    apply SingularAbc.mk u hr (nonsingular_o_sub hu hr hxy)
    · have : -2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y = 0 := by
        simp only [mul_eq_zero]
        grind
      obtain ha := h.a_eq_zero u r
      rw [this] at ha
      field_simp
      convert congr(u ^ 3 * $ha) using 1
      · congrm (_ * ?_)
        grind
      · simp
    · field_simp
      grind [h.c_factor_eq_zero u hr hxy]
  obtain ⟨hy, hur, huxr⟩ := this
  have hk : k u r ≠ 0 := by
    rw [← sq_eq_zero_iff.ne]
    simpa [k_sq] using hur
  have : r ^ 2 * k u r * (r * x - u) * y / (2 * u ^ 3) ≠ 0 := by
    simp [hr, hk, hy, hu, huxr]
  apply P2.mk'_eq_mk' this
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.smul_cons, smul_eq_mul, mul_zero,
    Matrix.smul_empty, Matrix.vecCons_inj, and_true]
  constructor
  · field_simp
    rw [k_sq]
    ring
  · field_simp
    apply eq_of_sub_eq_zero
    linear_combination -4 * (h.c_factor_eq_zero u hr hxy)

variable {u r} in
theorem SingularAbc.f_o_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ}
    (hsxy : SingularAbc u r x y) (hxy : (elliptic u r).Nonsingular x y)
    (ho : Point.some hxy ≠ o hu hr) :
    f hu hr (o hu hr - .some hxy) = rChord u r (f hu hr (.some hxy)) := by
  suffices fabc hu hr (o hu hr - Point.some hxy) =
      P2.lift₂ (fun p q hp hq ↦ P2.mk' (rChord' u r p q)) _
      (fxyz u hr (.some hxy)) (fabc hu hr (.some hxy)) by
    simpa [rChord, f, fxyz_o_sub hu hr]
  rw [hsxy.fabc_o_sub hu hr hxy ho, hsxy.fxyz_eq hu hr, hsxy.fabc_eq hu hr]
  obtain hk := hsxy.k_ne_zero u hr hxy
  have h0 : 2 * u * (2 * u * k u r * (u ^ 2 - r ^ 2)) + r ^ 2 * (4 * u ^ 2 * k u r) -
      u ^ 2 * (4 * u ^ 2 * k u r) = 0 := by
    ring
  by_cases hur2 : u ^ 2 - r ^ 2 = 0
  · have h0' : r ^ 2 * (4 * u ^ 2 * k u r) - u ^ 2 * (4 * u ^ 2 * k u r) = 0 := by
      simpa [hur2] using h0
    suffices P2.mk ![8 * u ^ 3 * k u r,
        4 * (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * u ^ 2, 0] _ =
      P2.mk ![2 * u * k u r * (4 * u ^ 2),
        (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * (4 * u ^ 2), 0] _ by
      simpa [rChord', h0', hk, hu, hur2]
    congrm P2.mk ![?_, ?_, _] _
    · ring
    · ring
  suffices P2.mk ![8 * u ^ 3 * k u r,
      4 * (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * u ^ 2, 0] _ =
    P2.mk ![(r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * (u ^ 2 - r ^ 2),
      -(2 * u * k u r * (u ^ 2 - r ^ 2)), 0] _ by
    simpa [rChord', h0, hur2, hu, hk]
  rw [P2.mk_eq_mk']
  use 8 * u ^ 3 * k u r / ((r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * (u ^ 2 - r ^ 2))
  simp only [Matrix.smul_cons, smul_eq_mul, mul_neg, mul_zero, Matrix.smul_empty,
    Matrix.vecCons_inj, and_true]
  have h0 : r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2) ≠ 0 := by
    rw [← sq_eq_zero_iff.ne, ← hsxy.x_relation u hr hxy]
    simp [hu, hk]
  constructor
  · field
  · field_simp
    rw [← hsxy.x_relation u hr hxy]
    ring

variable {u r} in
theorem f_o_sub (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) :
    f hu hr (o hu hr - p) = rChord u r (f hu hr p) := by
  -- check case when p = 0
  cases p with
  | zero =>
    rw [show o hu hr - Point.zero = o hu hr by rfl]
    suffices P2.mk ![1, k u r, u + r] _ =
      P2.mk' (rChord' u r ![u + r, 0, 1] ![1, -k u r, u + r]) by simpa [rChord, f, fxyz_o_sub hu hr]
    rw [← P2.mk'_eq]
    simpa using f_o_sub_1 r hu 1
  | @some x y hxy =>
  -- check case when p = o
  by_cases ho : .some hxy = o hu hr
  · suffices P2.mk ![1, -k u r, u + r] _ =
        P2.mk' (rChord' u r ![u + r, 0, 1] ![1, k u r, u + r]) by
      simpa [rChord, f, fxyz_o_sub hu hr, ho]
    rw [← P2.mk'_eq]
    simpa using f_o_sub_1 r hu (-1)
  have hx0 : x ≠ 0 := (eq_o_iff hu hr hxy).ne.mp ho
  -- check case when p is SingularAbc
  by_cases hsxy : SingularAbc u r x y
  · exact hsxy.f_o_sub hu hr hxy ho
  -- check case when o - p is SingularAbc
  have : ∃ (ox oy : ℂ) (hoxy : (elliptic u r).Nonsingular ox oy),
      o hu hr - .some hxy = .some hoxy := by
    cases h : o hu hr - .some hxy with
    | zero =>
      rw [Eq.comm, ← sub_eq_zero.not, h] at ho
      absurd ho
      rfl
    | @some ox oy hoxy =>
      exact ⟨ox, oy, hoxy, rfl⟩
  obtain ⟨ox, oy, hoxy, hoxyeq⟩ := this
  have hoo : .some hoxy ≠ o hu hr := by
    by_contra!
    simp [this] at hoxyeq
  by_cases hosxy : SingularAbc u r ox oy
  · rw [hoxyeq]
    have hoxyeq' : Point.some hxy = o hu hr - Point.some hoxy := by
      simp [← hoxyeq]
    rw [hoxyeq']
    rw [← (rChord_bijOn u r hu).injOn.eq_iff (mapsTo_f hu hr (by simp))
      (mapsTo_rChord u r hu (mapsTo_f hu hr (by simp)))]
    rw [rChord_rChord u r hu (mapsTo_f hu hr (by simp))]
    exact (hosxy.f_o_sub hu hr hoxy hoo).symm
  -- non-singular case
  suffices fabc hu hr (o hu hr - Point.some hxy) =
      P2.lift₂ (fun p q hp hq ↦ P2.mk' (rChord' u r p q)) _
      (fxyz u hr (Point.some hxy)) (fabc hu hr (Point.some hxy)) by
    simpa [rChord, f, fxyz_o_sub hu hr]
  rw [hoxyeq]
  suffices P2.mk (fabcNormal u r ox oy) _ =
      P2.mk' (rChord' u r (fxyzRaw u r (Point.some hxy)) (fabcNormal u r x y)) by
    simpa [fabc, fxyz, fabcRaw, hsxy, hosxy]
  rw [o_sub hu hr hxy ho, Point.some.injEq] at hoxyeq
  have hdeno : (r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x ≠ 0 := by
    by_contra! h
    obtain ha | ha := eq_or_eq_neg_of_sq_eq_sq _ _ <| presingular u hr hxy h
    · contrapose! hsxy
      refine SingularAbc.mk u hr hxy ?_ (by simp [h])
      linear_combination -ha
    · contrapose! hosxy
      rw [← hoxyeq.1, ← hoxyeq.2]
      refine SingularAbc.mk u hr (nonsingular_o_sub hu hr hxy) ?_ ?_
      · field_simp
        linear_combination u ^3 * ha
      · field_simp
        linear_combination u ^ 3 * (u + r * x) * h
  have hne : 2 * u * fxyzRaw u r (Point.some hxy) 0 + r ^ 2 * fxyzRaw u r (Point.some hxy) 2 -
      u ^ 2 * fxyzRaw u r (Point.some hxy) 2 ≠ 0 := by
    suffices 2 * u * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r ^ 2 - r * u) * x + u ^ 2 * (u + r))
        + r ^ 2 * (r * x + u) ^ 2 - u ^ 2 * (r * x + u) ^ 2 ≠ 0 by
      simpa [fxyzRaw]
    contrapose! hdeno
    linear_combination hdeno
  rw [← P2.mk'_eq]
  rw [← hoxyeq.1, ← hoxyeq.2]
  have hl : (r ^ 3 * x ^ 3 * ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x)) / u ^ 3 ≠ 0 := by
    simp [hu, hr, hx0, hdeno]
  symm
  apply P2.mk'_eq_mk' hl
  simp only [rChord', Fin.isValue, hne, ↓reduceIte]
  simp only [fxyzRaw, neg_mul, Fin.isValue, Matrix.cons_val_zero, fabcNormal, Matrix.cons_val,
    Matrix.cons_val_one, mul_neg, sub_neg_eq_add, Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty,
    Matrix.vecCons_inj, and_true]
  exact ⟨by field, by field, by field⟩

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
/-
variable {u r} in
theorem addX_w_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (hxy : (elliptic u r).Nonsingular x y)
    (hx : x ≠ u ^ 2 / r ^ 2) (hx0 : x ≠ 0) :
    (elliptic u r).addX (u ^ 2 / r ^ 2) x
      ((elliptic u r).slope (u ^ 2 / r ^ 2) x (u ^ 2 / r ^ 3) (-y)) =
    u ^ 2 * (x + r * y) ^ 2 / (x * (r ^ 2 * x - u ^ 2) ^ 2) := by
  have : r ^ 2 * x - u ^ 2 ≠ 0 := by grind
  have : u ^ 2 - r ^ 2 * x ≠ 0 := by grind
  rw [slope_w_sub hu hr hx]
  simp only [addX, elliptic, zero_mul, add_zero]
  rw [nonsingular_elliptic u hr] at hxy
  obtain ⟨heq, hnonsingular⟩ := hxy
  field_simp
  linear_combination r^2 * (r ^ 2 * x - u ^ 2) ^ 3 * heq-/

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
/-
variable {u r} in
theorem addY_w_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (hxy : (elliptic u r).Nonsingular x y)
    (hx : x ≠ u ^ 2 / r ^ 2) (hx0 : x ≠ 0) :
    (elliptic u r).addY (u ^ 2 / r ^ 2) x (u ^ 2 / r ^ 3)
      ((elliptic u r).slope (u ^ 2 / r ^ 2) x (u ^ 2 / r ^ 3) (-y)) =
      u ^ 2 * (x + r * y) *
      (r^2 * (1 + u^2 -r^2) * x^2 + u^2 * (1 - u^2 + r^2) * x + r * y * (r^2 * x + u^2))
      / (r * x * (r ^ 2 * x - u ^ 2) ^ 3) := by
  have : r ^ 2 * x - u ^ 2 ≠ 0 := by grind
  have : u ^ 2 - r ^ 2 * x ≠ 0 := by grind
  rw [addY, negAddY, addX_w_sub hu hr hxy hx hx0]
  rw [slope_w_sub hu hr hx]
  simp only [negY, neg_add_rev, elliptic, zero_mul, sub_zero]
  rw [nonsingular_elliptic u hr] at hxy
  obtain ⟨heq, hnonsingular⟩ := hxy
  field_simp
  linear_combination r ^ 4 * (u ^ 2 - r ^ 2 * x) * (r * y + x) * heq-/

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
theorem fabcNormal_w (hu : u ≠ 0) (hr : r ≠ 0) :
    fabcNormal u r (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 3) = ![
    u ^ 3 * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r) / r ^ 3,
    -k u r * u ^ 3 * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r) / r ^ 3,
    (u + r) * u ^ 3 * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r) / r ^ 3] := by
  unfold fabcNormal
  congrm ![$(by field), $(by field), $(by field)]

variable {u r} in
@[simp]
theorem fabc_w (hu : u ≠ 0) (hr : r ≠ 0) :
    fabc hu hr (w hu hr) = P2.mk ![1, -k u r, u + r] (by simp) := by
  unfold fabc
  rw [P2.mk_eq_mk']
  by_cases hs : SingularAbc u r (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 3)
  · obtain h := hs.c_factor_eq_zero u hr (nonsingular_w hu hr)
    have h : (u ^ 2 - r ^ 2) ^ 2 = -4 * u * r := by
      field_simp at h
      grind
    suffices (r * (u + r) ^ 2 * (u ^ 2 / r ^ 2) - u * ((u + r) ^ 2 - 2)) *
        (-(4 * u * r) - 4 * u ^ 2) = -(2 * u * k u r * (-(4 * u * r) + 4 * u ^ 2) * k u r) ∧
        8 * u ^ 2 * k u r * (u ^ 2 - r ^ 2) =
        2 * u * k u r * (-(4 * u * r) + 4 * u ^ 2) * (u + r) by
      simpa [fabcRaw, w, hs, h]
    constructor
    · have : -(2 * u * k u r * (-(4 * u * r) + 4 * u ^ 2) * k u r) =
        -(2 * u * (-(4 * u * r) + 4 * u ^ 2) * (k u r ^ 2)) := by ring
      rw [this, k_sq]
      field_simp
      linear_combination -h
    · ring
  simp [fabcRaw, w, hs, fabcNormal_w hu hr]
  grind

variable {u r} in
theorem fabcNormal_neg_w (hu : u ≠ 0) (hr : r ≠ 0) :
    fabcNormal u r (u ^ 2 / r ^ 2) (-u ^ 2 / r ^ 3) = ![
    u ^ 3 * ((u - r) * (u + r) ^ 2 * (u + 3 * r) + 4 * r ^ 2) / r ^ 3,
    -k u r * u ^ 3 * ((u ^ 2 - r ^ 2) ^ 2 - 4 * r ^ 2) / r ^ 3,
    u ^ 3 * (u + r) * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r) / r ^ 3] := by
  unfold fabcNormal
  congrm ![$(by field), $(by field), $(by field)]


variable {u r} in
theorem not_singularAbc_neg_w (hu : u ≠ 0) (hr : r ≠ 0) :
    ¬ SingularAbc u r (u ^ 2 / r ^ 2) (-u ^ 2 / r ^ 3) := by
  by_contra! h
  obtain ha := h.a_eq_zero
  obtain hc := h.c_factor_eq_zero u hr (nonsingular_neg_w hu hr)
  field_simp at ha hc
  grind

variable {u r} in
theorem fabc_neg_w_ne_zero (hu : u ≠ 0) (hr : r ≠ 0) :
    ![(u - r) * (u + r) ^ 2 * (u + 3 * r) + 4 * r ^ 2,
      -k u r * ((u ^ 2 - r ^ 2) ^ 2 - 4 * r ^ 2),
      (u + r) * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r)] ≠ 0 := by
  obtain h := not_singularAbc_neg_w hu hr
  contrapose! h
  unfold SingularAbc fabcNormal
  obtain h := congr((u ^ 3 / r ^ 3) • $h)
  simp_rw [Matrix.smul_vec3, smul_zero, smul_eq_mul] at h
  refine Eq.trans ?_ h
  congrm ![$(by field), $(by field), $(by field)]

variable {u r} in
theorem fabc_neg_w (hu : u ≠ 0) (hr : r ≠ 0) :
    fabc hu hr (-w hu hr) = P2.mk ![
      (u - r) * (u + r) ^ 2 * (u + 3 * r) + 4 * r ^ 2,
      -k u r * ((u ^ 2 - r ^ 2) ^ 2 - 4 * r ^ 2),
      (u + r) * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r)] (fabc_neg_w_ne_zero hu hr) := by
  rw [neg_w]
  simp only [fabc, fabcRaw, not_singularAbc_neg_w hu hr, ↓reduceIte, fabcNormal_neg_w hu hr]
  rw [P2.mk_eq_mk']
  use u ^ 3 / r ^ 3
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![?_, ?_, ?_]
  · ring
  · ring
  · ring

variable {r} in
theorem fabcNormal_2w (hr : r ≠ 0) :
    fabcNormal u r ((r ^ 2 - u ^ 2) ^ 2 / (4 * r ^ 2))
    ((r ^ 2 - u ^ 2) * ((r ^ 2 - u ^ 2) ^ 2 - 2 * (r ^ 2 + u ^ 2)) / (8 * r ^ 3)) =
    ![(u + r) * ((u - r) * (u + r) ^ 2 * (u + 3 * r) + 4 * r ^ 2) *
      (((u ^ 2 - r ^ 2) ^ 2 - 4 * u * r) ^ 2 + 16 * u * r * (u - r) ^ 2) /
      (64 * r ^ 3),
    -k u r * (u + r) * ((u ^ 2 - r ^ 2) ^ 2 - 4 * r ^ 2) *
      (((u ^ 2 - r ^ 2) ^ 2 - 4 * u * r) ^ 2 + 16 * u * r * (u - r) ^ 2) /
      (64 * r ^ 3),
    (u + r) ^ 2 * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r) *
      (((u ^ 2 - r ^ 2) ^ 2 - 4 * u * r) ^ 2 + 16 * u * r * (u - r) ^ 2) /
      (64 * r ^ 3)] := by
  unfold fabcNormal
  congrm ![$(by field), $(by field), $(by field)]

variable {u r} in
theorem fabc_2w (hu : u ≠ 0) (hr : r ≠ 0) :
    fabc hu hr (w hu hr + w hu hr) = P2.mk ![
      (u - r) * (u + r) ^ 2 * (u + 3 * r) + 4 * r ^ 2,
      -k u r * ((u ^ 2 - r ^ 2) ^ 2 - 4 * r ^ 2),
      (u + r) * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r)] (fabc_neg_w_ne_zero hu hr) := by
  rw [two_w]
  by_cases hsxy : SingularAbc u r ((r ^ 2 - u ^ 2) ^ 2 / (4 * r ^ 2))
      ((r ^ 2 - u ^ 2) * ((r ^ 2 - u ^ 2) ^ 2 - 2 * (r ^ 2 + u ^ 2)) / (8 * r ^ 3))
  · obtain hc := hsxy.c_factor_eq_zero u hr (nonsingular_2w hu hr)
    field_simp at hc
    have hc : (u + r) ^ 2 *
        (((u ^ 2 - r ^ 2) ^ 2 - 4 * u * r) ^ 2 + 16 * u * r * (u - r) ^ 2) = 0 := by
      linear_combination hc
    obtain hc | hc : u + r = 0 ∨
      ((u ^ 2 - r ^ 2) ^ 2 - 4 * u * r) ^ 2 + 16 * u * r * (u - r) ^ 2 = 0 := by simpa using hc
    · have hr : r = -u := (neg_eq_of_add_eq_zero_right hc).symm
      simp only [fabc, fabcRaw, hsxy, ↓reduceIte]
      suffices P2.mk ![2 * u * k u (-u) * (4 * u ^ 2), -(u * 2 * (4 * u ^ 2)), 0] _ =
          P2.mk ![4 * u ^ 2, k u (-u) * (4 * u ^ 2), 0] _ by
        simpa [hr]
      symm
      rw [P2.mk_eq_mk']
      use -k u (-u) / (2 * u)
      simp_rw [Matrix.smul_vec3, smul_eq_mul, mul_zero]
      congrm ![?_ ,?_, 0]
      · field_simp
        simp [k_sq]
      · field_simp
    have hk : k u r ≠ 0 := by
      grind
    have hur : u - r ≠ 0 := by
      grind
    suffices P2.mk
      ![2 * u * k u r * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u ^ 2),
        (r * (u + r) ^ 2 * ((r ^ 2 - u ^ 2) ^ 2 / (4 * r ^ 2)) - u * ((u + r) ^ 2 - 2)) *
          ((u ^ 2 - r ^ 2) ^ 2 - 4 * u ^ 2),
        8 * u ^ 2 * k u r * (u ^ 2 - r ^ 2)] _ =
      P2.mk
        ![(u - r) * (u + r) ^ 2 * (u + 3 * r) + 4 * r ^ 2,
          -(k u r * ((u ^ 2 - r ^ 2) ^ 2 - 4 * r ^ 2)),
          (u + r) * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r)] _ by
      simpa [fabc, fabcRaw, hsxy]
    symm
    rw [P2.mk_eq_mk']
    use ((u ^ 2 - r ^ 2) ^ 2 + 4 * u * r) / (8 * u ^ 2 * k u r * (u - r))
    simp_rw [Matrix.smul_vec3, smul_eq_mul]
    congrm ![?_, ?_, ?_]
    · field_simp
      grind
    · field_simp
      rw [k_sq]
      grind
    · field
  simp only [fabc, fabcRaw, hsxy, ↓reduceIte, fabcNormal_2w u hr]
  rw [P2.mk_eq_mk']
  use (u + r) * (((u ^ 2 - r ^ 2) ^ 2 - 4 * u * r) ^ 2 + 16 * u * r * (u - r) ^ 2) /
      (64 * r ^ 3)
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![?_, ?_, ?_]
  · ring
  · ring
  · ring

variable {u r} in
theorem fabc_w_sub (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) :
    fabc hu hr (w hu hr - p) = fabc hu hr p := by
  cases p with
  | zero =>
    change fabc hu hr (w hu hr - 0) = fabc hu hr Point.zero
    simp
  | @some x y hxy =>
  by_cases hpw : .some hxy = w hu hr
  · simp [hpw]
  by_cases hpnw : .some hxy = -w hu hr
  · simp_rw [hpnw, sub_neg_eq_add, fabc_2w, fabc_neg_w]


  rw [nonsingular_elliptic u hr] at hxy
  obtain ⟨heq, hnonsingular⟩ := hxy
  have hx : x ≠ u ^ 2 / r ^ 2 := by
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
  rw [w_sub hu hr hxy hx]
  --unfold fabc
 /- have hx0 : x ≠ 0 := by
    exact (eq_o_iff hu hr hxy).ne.mp
    sorry-/
  sorry

variable {u r} in
theorem f_w_sub (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) :
    f hu hr (w hu hr - p) = rPoint u r (f hu hr p) := by sorry



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
