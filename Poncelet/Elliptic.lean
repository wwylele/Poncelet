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

def SingularAbc (x y : ℂ) := fabcNormal u r x y = 0

theorem SingularAbc.a_eq_zero {x y : ℂ} (h : SingularAbc u r x y) :
    -2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y +
    (r * x + u) * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2)
    = 0
  := congr($h 0)

theorem SingularAbc.b_eq_zero {x y : ℂ} (h : SingularAbc u r x y) :
    k u r * ((2 * r ^ 2 * (r * x + u) * y +
    (r * x - u) * (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2)))
    = 0
  := by
  simpa [fabcNormal] using congr($h 1)

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

theorem SingularAbc.fxyz_eq {x y : ℂ} (h : SingularAbc u r x y)
    (hxy : ((elliptic u r)).Nonsingular x y) :
    fxyzRaw u r (.some hxy) = sorry :=
  sorry

/-variable {u r} in
theorem SingularAbc.x_eq_zero_of_casePos (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ}
    (h : SingularAbc u r x y) (hxy : ((elliptic u r)).Nonsingular x y) (huv : u + r = 0) :
    x = 0 := by
  simpa [huv, hu, hr] using h.c_factor_eq_zero u hr hxy


variable {u r} in
theorem SingularAbc.y_eq_zero_of_casePos (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ}
    (h : SingularAbc u r x y) (hxy : ((elliptic u r)).Nonsingular x y) (huv : u + r = 0) :
    y = 0 := by
  obtain hx := h.x_eq_zero_of_casePos hu hr hxy huv
  rw [nonsingular_elliptic u hr] at hxy
  obtain ⟨heq, hs⟩ := hxy
  simpa [hx, hr] using heq-/

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

variable {u r} in
noncomputable
def fabc (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) : P2 :=
    P2.mk (fabcRaw u r p) <| by
  cases p with
  | zero =>
    simp [fabcRaw]
  | @some x y hxy =>
    by_cases h0 : SingularAbc u r x y
    · obtain hk := h0.k_ne_zero u hr hxy
      by_cases hur : u ^ 2 - r ^ 2 = 0
      · suffices fabcRaw u r (Point.some hxy) 0 ≠ 0 by
          contrapose! this
          simp [this]
        simp [fabcRaw, h0, hk, hu, hur]
      · suffices fabcRaw u r (Point.some hxy) 2 ≠ 0 by
          contrapose! this
          simp [this]
        simp [fabcRaw, h0, hk, hu, hur]
    · suffices fabcNormal u r x y ≠ 0 by simpa [fabcRaw, h0]
      exact h0

variable {u r} in
theorem innerCircle_abc (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) :
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
    suffices
      (2 * r * ((u + r) ^ 2 - 1) * (u - r * x) * (r * y) +
        (r * x + u) * (r ^ 2 * (u + r) * x ^ 2 +
        2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2)) ^ 2 +
      k u r ^ 2 * ((2 * r * (r * x + u) * (r * y) +
        (r * x - u) *
        (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (r + u)) * x + (u + r) * u ^ 2))) ^ 2 =
      ((r * x + u) * ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x)) ^ 2 by
      convert this using 1
      · simp [fabcRaw, hsingular, fabcNormal]
        ring
      · simp [fabcRaw, hsingular, fabcNormal]
    rw [k_sq]
    grind


variable {u r} in
theorem incidence_xyz_abc (hu : u ≠ 0) (hr : r ≠ 0) (p : (elliptic u r).Point) :
    Incidence (fxyz u hr p) (fabc hu hr p) := by
  change fxyzRaw u r p 0 * fabcRaw u r p 0 + fxyzRaw u r p 1 * fabcRaw u r p 1 =
    fxyzRaw u r p 2 * fabcRaw u r p 2
  cases p with
  | zero =>
    simp [fabcRaw, fxyzRaw]
  | @some x y hxy =>
    by_cases hsingular : SingularAbc u r x y
    ·
      suffices (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r ^ 2 - r * u) * x + u ^ 2 * (u + r)) *
        (2 * u * k u r * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u ^ 2)) +
        -(2 * r ^ 2 * k u r * y * ((r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * ((u ^ 2 - r ^ 2) ^ 2 - 4 * u ^ 2))) =
        (r * x + u) ^ 2 * (8 * u ^ 2 * k u r * (u ^ 2 - r ^ 2)) by
        convert this using 1
        · simp [fxyzRaw, fabcRaw, hsingular]
        · simp [fxyzRaw, fabcRaw, hsingular]

      sorry
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
def o (hu : u ≠ 0) (hr : r ≠ 0) : (elliptic u r).Point :=
  .some (show (elliptic u r).Nonsingular 0 0 by simp [elliptic, hu, hr])

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
noncomputable
def w (hu : u ≠ 0) (hr : r ≠ 0) : (elliptic u r).Point :=
  .some (show (elliptic u r).Nonsingular (u ^ 2 / r ^ 2) (u ^ 2 / r ^ 3) by
  rw [nonsingular_elliptic u hr]
  refine ⟨?_, Or.inr (by simp [hu, hr])⟩
  field_simp
  ring
  )
/-
def xsorry : ℂ := sorry


(u^2 *(r^2 * x^2 + (2 - u^2 - r^2) * x + u^2 + 2 * r * y))/(r^2 * x - u^2)^2


def ysorry : ℂ := sorry

 -(u^2 ?)/(r (-u^2 + r^2 x)^3)

?= (-u^4 - 2 u^2 x + r^2 u^2 x + 2 u^4 x - 3 r^2 u^2 x^2 + r^4 x^3 - 2 r^2 * ( x * (r ^ 2 * x ^ 2 + (1 - u ^ 2 - r ^ 2) * x + u ^ 2)))  - 2 r u^2 y - r^3 u^2 y + r u^4 y - 2 r^3 x y + r^5 x y - r^3 u^2 x y


variable {u r} in
theorem nonsingular_w_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ}
    (h : (elliptic u r).Nonsingular x y) :
    (elliptic u r).Nonsingular xsorry ysorry := by sorry


theorem w_sub (hu : u ≠ 0) (hr : r ≠ 0) {x y : ℂ} (h : (elliptic u r).Nonsingular x y)
    (hw : Point.some h ≠ o hu hr) (hwneg : Point.some h ≠ -o hu hr) :
    w hu hr - Point.some h = Point.some (nonsingular_w_sub hu hr h) := by
  rw [nonsingular_elliptic u hr] at h
  obtain ⟨heq, hs⟩ := h
  rw [sub_eq_iff_eq_add]
  have hx : xsorry ≠ x := by sorry
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  obtain hslope := WeierstrassCurve.Affine.slope_of_X_ne hx
  simp [w, hx, elliptic]
  sorry-/

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
    simpa using hp0
  | @some x y hxy =>
    rw [nonsingular_elliptic u hr] at hxy
    obtain ⟨heq, hs⟩ := hxy
    by_cases hx0 : x = 0
    · rw [(eq_o_iff hu hr hxy).mpr hx0]
      simpa using hp0.symm
    have hxo : Point.some hxy ≠ o hu hr := (eq_o_iff hu hr hxy).ne.mpr hx0
    unfold fxyz
    rw [P2.mk_eq_mk]
    use u ^ 2 / (r ^ 2 * x ^ 2)
    refine ⟨by simp [hr, hu, hx0], ?_⟩
    rw [o_sub hu hr hxy hxo]
    simp only [fxyzRaw, smul_eq_mul, Matrix.smul_cons, Matrix.smul_empty,
      Matrix.vecCons_inj, and_true]
    refine ⟨?_, ?_, ?_⟩
    · field_simp
      ring
    · field_simp
    · field_simp
      ring



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
