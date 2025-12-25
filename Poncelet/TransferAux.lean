import Mathlib
import Poncelet.Elliptic

open WeierstrassCurve.Affine

variable {u r} in
theorem fabc_w_sub_c_eq_zero (hu : u ≠ 0) (hr : r ≠ 0) {x y wx wy : ℂ}
    (hxy : (elliptic u r).Nonsingular x y) (hwxy : (elliptic u r).Nonsingular wx wy)
    (hpw : .some hxy ≠ w hu hr) (hpnw : .some hxy ≠ -w hu hr)
    (hwxyeq : w hu hr - .some hxy = .some hwxy)
    (hsxy : ¬ SingularAbc u r x y) (hwsxy : ¬ SingularAbc u r wx wy)
    (hc : (r * x + u) * ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x) = 0) :
    fabc hu hr (.some hwxy) = fabc hu hr (.some hxy) := by
  obtain hx := x_not_at_w hu hr hxy hpw hpnw
  have : r ^ 2 * x - u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  have : u ^ 2 - r ^ 2 * x ≠ 0 := by
    contrapose! this
    linear_combination -this
  suffices P2.mk (fabcNormal u r wx wy) _ = P2.mk (fabcNormal u r x y) _ by
    simpa [fabc, fabcRaw, hsxy, hwsxy]
  rw [P2.mk_eq_mk']
  rw [w_sub hu hr hxy hx, Point.some.injEq] at hwxyeq
  rw [← hwxyeq.1, ← hwxyeq.2]
  unfold fabcNormal
  have hdeno : -2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y +
      (r * x + u) *
      (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2) ≠ 0 := by
    contrapose! hsxy with hdeno
    apply SingularAbc.mk u hr hxy hdeno hc
  set deno := -2 * r ^ 2 * ((u + r) ^ 2 - 1) * (r * x - u) * y +
      (r * x + u) *
      (r ^ 2 * (u + r) * x ^ 2 + 2 * r * (1 - r * (u + r)) * x + (u + r) * u ^ 2)
  use (-2 * r ^ 2 * ((u + r) ^ 2 - 1) *
      (r * (u ^ 2 * (r ^ 2 * x ^ 2 + (2 - r ^ 2 - u ^ 2) * x + u ^ 2 + 2 * r * y) /
      (r ^ 2 * x - u ^ 2) ^ 2) - u) *
      (u ^ 2 *
      (r ^ 4 * x ^ 3 + r ^ 2 * (2 + u ^ 2 - 2 * r ^ 2) * x ^ 2 +
      u ^ 2 * (2 - 2 * u ^ 2 + r ^ 2) * x + u ^ 4 +
      (r ^ 2 * (2 + u ^ 2 - r ^ 2) * x + u ^ 2 * (2 - u ^ 2 + r ^ 2)) * r * y) /
      (r * (r ^ 2 * x - u ^ 2) ^ 3)) +
      (r * (u ^ 2 * (r ^ 2 * x ^ 2 + (2 - r ^ 2 - u ^ 2) * x + u ^ 2 + 2 * r * y) /
      (r ^ 2 * x - u ^ 2) ^ 2) + u) *
      (r ^ 2 * (u + r) *
      (u ^ 2 * (r ^ 2 * x ^ 2 + (2 - r ^ 2 - u ^ 2) * x + u ^ 2 + 2 * r * y) /
      (r ^ 2 * x - u ^ 2) ^ 2) ^ 2 +
      2 * r * (1 - r * (u + r)) *
      (u ^ 2 * (r ^ 2 * x ^ 2 + (2 - r ^ 2 - u ^ 2) * x + u ^ 2 + 2 * r * y) /
      (r ^ 2 * x - u ^ 2) ^ 2) +
      (u + r) * u ^ 2)) /
      deno
  obtain ⟨heq, hnonsingular⟩ := (nonsingular_elliptic u hr _ _).mp hxy
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![?_, ?_, ?_]
  · field_simp
  · field_simp
    linear_combination -8 * k u r * u * r ^3 * (
      -x^5*u^5*r^6 - 2*x^5*u^4*r^7 + 2*x^5*u^2*r^9 + x^5*u*r^10 + 2*x^4*u^7*r^4
      + 4*x^4*u^6*r^5 + 3*x^4*u^5*r^6 + 2*x^4*u^4*r^7 - 2*x^4*u^3*r^8 - 6*x^4*u^2*r^9
      - 3*x^4*u*r^10 - x^3*u^9*r^2 - 2*x^3*u^8*r^3 - 7*x^3*u^7*r^4 - 3*x^3*y*u^5*r^5
      - 12*x^3*u^6*r^5 - 8*x^3*y*u^4*r^6 - x^3*u^5*r^6 - 3*x^5*u^2*r^7
      - 4*x^3*y*u^3*r^7 + 10*x^3*u^4*r^7 - 4*x^5*u*r^8 + 6*x^3*y*u^2*r^8
      + 7*x^3*u^3*r^8 - x^5*r^9 + 7*x^3*y*u*r^9 + 4*x^3*u^2*r^9 + 2*x^3*y*r^10
      + 2*x^3*u*r^10 + 5*x^2*u^9*r^2 + 3*x^2*y*u^7*r^3 + 10*x^2*u^8*r^3
      - 3*x^4*u^5*r^4 + 10*x^2*y*u^6*r^4 + 5*x^2*u^7*r^4 - 2*x^4*u^4*r^5
      + 12*x^2*y*u^5*r^5 + 5*x^4*u^3*r^6 + 2*x^2*y*u^4*r^6 - 5*x^2*u^5*r^6
      + 16*x^4*u^2*r^7 - 11*x^2*y*u^3*r^7 - 10*x^2*u^4*r^7 + 14*x^4*u*r^8
      - 12*x^2*y*u^2*r^8 - 5*x^2*u^3*r^8 + 2*x^4*r^9 - 4*x^2*y*u*r^9
      - x*u^11 - 2*x*u^10*r + 3*x^3*u^7*r^2 - 2*x*y*u^8*r^2 - 4*x*u^9*r^2
      + 7*x^3*u^6*r^3 - 9*x*y*u^7*r^3 - 6*x*u^8*r^3 + 8*x^3*u^5*r^4
      - 2*x*y^2*u^5*r^4 - 10*x*y*u^6*r^4 + x*u^7*r^4 - 12*x^3*u^4*r^5
      - 6*x*y^2*u^4*r^5 + 4*x*y*u^5*r^5 + 8*x*u^6*r^5 - 4*x^3*y*u^2*r^6
      - 25*x^3*u^3*r^6 - 6*x*y^2*u^3*r^6 + 12*x*y*u^4*r^6 + 4*x*u^5*r^6
      - 6*x^3*y*u*r^7 - 19*x^3*u^2*r^7 - 2*x*y^2*u^2*r^7 + 5*x*y*u^3*r^7
      - 2*x^3*y*r^8 - 10*x^3*u*r^8 + u^11 - 2*x^2*u^8*r + y*u^9*r + 2*u^10*r
      - 12*x^2*u^7*r^2 + 2*y*u^8*r^2 - 4*x^2*y*u^5*r^3 - 8*x^2*u^6*r^3
      + 2*y^2*u^6*r^3 - 2*u^8*r^3 - 12*x^2*y*u^4*r^4 + 10*x^2*u^5*r^4
      + 6*y^2*u^5*r^4 - 2*y*u^6*r^4 - u^7*r^4 - 4*x^4*u^2*r^5 - 6*x^2*y*u^3*r^5
      + 26*x^2*u^4*r^5 + 6*y^2*u^4*r^5 - y*u^5*r^5 - 10*x^4*u*r^6
      + 14*x^2*y*u^2*r^6 + 18*x^2*u^3*r^6 + 2*y^2*u^3*r^6 - 2*x^4*r^7
      + 12*x^2*y*u*r^7 + 3*x*u^9 + 5*x*u^8*r - 2*x^3*u^5*r^2
      + 8*x*y*u^6*r^2 + 2*x*u^7*r^2 - 6*x^3*u^4*r^3 + 14*x*y*u^5*r^3
      - 9*x*u^6*r^3 + 8*x^3*u^3*r^4 - 2*x*y*u^4*r^4 - 9*x*u^5*r^4
      + 16*x^3*u^2*r^5 - 8*x*y*u^3*r^5 + 16*x^3*u*r^6 - u^9 + 6*x^2*u^6*r
      - 2*y*u^7*r + 4*x^2*u^5*r^2 - 2*y*u^6*r^2 + u^7*r^2 - 8*x^2*u^4*r^3
      - 4*y^2*u^4*r^3 - 18*x^2*u^3*r^4 - 4*y^2*u^3*r^4 - 8*x^2*y*u*r^5
      - 2*x*u^7 - 2*x*u^6*r - 8*x*y*u^4*r^2 + 4*x*u^5*r^2 - 8*x^3*u*r^4
      - 4*x^2*u^4*r + 4*x^2*u^3*r^2) * heq
  · field_simp
    linear_combination 8 * (u + r - 1) * (u + r + 1) * u^2 * r^3 *
      (-x^5*u^3*r^6 - x^5*u^2*r^7 + x^5*u*r^8 + x^5*r^9 + 2*x^4*u^5*r^4
      + 2*x^4*u^4*r^5 - x^4*u^3*r^6 - x^4*u^2*r^7 - x^4*u*r^8 - x^4*r^9
      - x^3*u^7*r^2 - x^3*u^6*r^3 - 3*x^3*y*u^3*r^5 - 5*x^3*y*u^2*r^6
      + x^3*u^3*r^6 - 2*x^5*r^7 - x^3*y*u*r^7 + x^3*u^2*r^7 + x^3*y*r^8
      - x^2*u^7*r^2 + 3*x^2*y*u^5*r^3 - x^2*u^6*r^3 - 3*x^4*u^3*r^4
      + 7*x^2*y*u^4*r^4 - x^4*u^2*r^5 + 7*x^2*y*u^3*r^5 + x^4*u*r^6
      + 5*x^2*y*u^2*r^6 + x^2*u^3*r^6 + 5*x^4*r^7 + 2*x^2*y*u*r^7
      + x^2*u^2*r^7 + x*u^9 + x*u^8*r + 3*x^3*u^5*r^2 - 2*x*y*u^6*r^2
      + x*u^7*r^2 + 5*x^3*u^4*r^3 - 5*x*y*u^5*r^3 + x*u^6*r^3 - x^3*u^3*r^4
      - 2*x*y^2*u^3*r^4 - 7*x*y*u^4*r^4 - 2*x*u^5*r^4 - 5*x^3*u^2*r^5
      - 4*x*y^2*u^2*r^5 - 7*x*y*u^3*r^5 - 2*x*u^4*r^5 - 4*x^3*y*r^6
      + 2*x^3*u*r^6 - 2*x*y^2*u*r^6 - 3*x*y*u^2*r^6 - u^9 - 2*x^2*u^6*r
      - y*u^7*r - u^8*r + 5*x^2*u^5*r^2 + y*u^6*r^2 + u^7*r^2 - 4*x^2*y*u^3*r^3
      + x^2*u^4*r^3 + 2*y^2*u^4*r^3 + 5*y*u^5*r^3 + u^6*r^3 - 4*x^2*y*u^2*r^4
      - 5*x^2*u^3*r^4 + 4*y^2*u^3*r^4 + 3*y*u^4*r^4 - 4*x^4*r^5 - 4*x^2*y*u*r^5
      - 3*x^2*u^2*r^5 + 2*y^2*u^2*r^5 - 5*x*u^7 - x*u^6*r - 2*x^3*u^3*r^2
      + 4*x*y*u^4*r^2 + x*u^5*r^2 + 4*x*y*u^3*r^3 + 3*x*u^4*r^3 - 2*x^3*u*r^4
      + 4*x*y*u^2*r^4 + 2*u^7 + 2*x^2*u^4*r + 4*y*u^5*r + 2*x^2*u^2*r^3 + 4*x*u^5)* heq

variable {u r} in
theorem fabc_w_sub_c_ne_zero (hu : u ≠ 0) (hr : r ≠ 0) {x y wx wy : ℂ}
    (hxy : (elliptic u r).Nonsingular x y) (hwxy : (elliptic u r).Nonsingular wx wy)
    (hpw : .some hxy ≠ w hu hr) (hpnw : .some hxy ≠ -w hu hr)
    (hwxyeq : w hu hr - .some hxy = .some hwxy)
    (hsxy : ¬ SingularAbc u r x y) (hwsxy : ¬ SingularAbc u r wx wy)
    (hc : (r * x + u) * ((r * x - u) ^ 2 * (u + r) ^ 2 + 4 * u * r * x) ≠ 0) :
    fabc hu hr (.some hwxy) = fabc hu hr (.some hxy) := by
  obtain hx := x_not_at_w hu hr hxy hpw hpnw
  have : r ^ 2 * x - u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  have : u ^ 2 - r ^ 2 * x ≠ 0 := by
    contrapose! this
    linear_combination -this
  have hinf1' : r * x + u ≠ 0 := by
    contrapose! hc
    simp [hc]
  have hinf2' : (u + r) ^ 2 * (r * x - u) ^ 2 + r * u * x * 4 ≠ 0 := by
    contrapose! hc
    linear_combination (r * x + u) * hc
  set inf2 := (u + r) ^ 2 * (r * x - u) ^ 2 + r * u * x * 4
  obtain ⟨heq, hnonsingular⟩ := (nonsingular_elliptic u hr _ _).mp hxy
  suffices P2.mk (fabcNormal u r wx wy) _ = P2.mk (fabcNormal u r x y) _ by
    simpa [fabc, fabcRaw, hsxy, hwsxy]
  rw [P2.mk_eq_mk']
  rw [w_sub hu hr hxy hx, Point.some.injEq] at hwxyeq
  rw [← hwxyeq.1, ← hwxyeq.2]
  unfold fabcNormal
  use (u ^ 3 * (r * u * (x * (r ^ 2 * x + (2 - r ^ 2 - u ^ 2)) + u ^ 2 + r * 2 * y) +
    (r ^ 2 * x - u ^ 2) ^ 2) *
    ((r * u * (x * (r ^ 2 * x + (2 - r ^ 2 - u ^ 2)) + u ^ 2 + r * 2 * y) -
    (r ^ 2 * x - u ^ 2) ^ 2) ^ 2 * (u + r) ^ 2 +
      r * u * (x * (r ^ 2 * x + (2 - r ^ 2 - u ^ 2)) + u ^ 2 + r * 2 * y) *
      (r ^ 2 * x - u ^ 2) ^ 2 * 4))  /
      ((r ^ 2 * x - u ^ 2) ^ 6  * (r * x + u) * inf2)
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![?_, ?_, ?_]
  · field_simp
    linear_combination  (-8) * (u + r - 1) * (u + r + 1) * u^2 * r^3 *
      (-x^5*u^3*r^6 - x^5*u^2*r^7 + x^5*u*r^8 + x^5*r^9 + 2*x^4*u^5*r^4 +
      2*x^4*u^4*r^5 - x^4*u^3*r^6 - x^4*u^2*r^7 - x^4*u*r^8 - x^4*r^9 -
      x^3*u^7*r^2 - x^3*u^6*r^3 - 3*x^3*y*u^3*r^5 - 5*x^3*y*u^2*r^6 +
      x^3*u^3*r^6 - 2*x^5*r^7 - x^3*y*u*r^7 + x^3*u^2*r^7 + x^3*y*r^8 -
      x^2*u^7*r^2 + 3*x^2*y*u^5*r^3 - x^2*u^6*r^3 - 3*x^4*u^3*r^4 +
      7*x^2*y*u^4*r^4 - x^4*u^2*r^5 + 7*x^2*y*u^3*r^5 + x^4*u*r^6 +
      5*x^2*y*u^2*r^6 + x^2*u^3*r^6 + 5*x^4*r^7 + 2*x^2*y*u*r^7 +
      x^2*u^2*r^7 + x*u^9 + x*u^8*r + 3*x^3*u^5*r^2 - 2*x*y*u^6*r^2 +
      x*u^7*r^2 + 5*x^3*u^4*r^3 - 5*x*y*u^5*r^3 + x*u^6*r^3 - x^3*u^3*r^4 -
      2*x*y^2*u^3*r^4 - 7*x*y*u^4*r^4 - 2*x*u^5*r^4 - 5*x^3*u^2*r^5 -
      4*x*y^2*u^2*r^5 - 7*x*y*u^3*r^5 - 2*x*u^4*r^5 - 4*x^3*y*r^6 +
      2*x^3*u*r^6 - 2*x*y^2*u*r^6 - 3*x*y*u^2*r^6 - u^9 - 2*x^2*u^6*r -
      y*u^7*r - u^8*r + 5*x^2*u^5*r^2 + y*u^6*r^2 + u^7*r^2 - 4*x^2*y*u^3*r^3 +
      x^2*u^4*r^3 + 2*y^2*u^4*r^3 + 5*y*u^5*r^3 + u^6*r^3 - 4*x^2*y*u^2*r^4 -
      5*x^2*u^3*r^4 + 4*y^2*u^3*r^4 + 3*y*u^4*r^4 - 4*x^4*r^5 - 4*x^2*y*u*r^5 -
      3*x^2*u^2*r^5 + 2*y^2*u^2*r^5 - 5*x*u^7 - x*u^6*r - 2*x^3*u^3*r^2 +
      4*x*y*u^4*r^2 + x*u^5*r^2 + 4*x*y*u^3*r^3 + 3*x*u^4*r^3 - 2*x^3*u*r^4 +
      4*x*y*u^2*r^4 + 2*u^7 + 2*x^2*u^4*r + 4*y*u^5*r + 2*x^2*u^2*r^3 + 4*x*u^5) * heq
  · field_simp
    linear_combination 8 * k u r * u * r ^ 3 *
      (x^5*u^4*r^6 + 2*x^5*u^3*r^7 + 2*x^5*u^2*r^8 + 2*x^5*u*r^9 + x^5*r^10 -
      2*x^4*u^6*r^4 - 4*x^4*u^5*r^5 - 10*x^4*u^4*r^6 - 16*x^4*u^3*r^7 -
      8*x^4*u^2*r^8 + x^3*u^8*r^2 + 2*x^3*u^7*r^3 + 17*x^3*u^6*r^4 + 3*x^3*y*u^4*r^5 +
      32*x^3*u^5*r^5 + 5*x^3*y*u^3*r^6 + 19*x^3*u^4*r^6 + 2*x^5*u*r^7 + x^3*y*u^2*r^7 +
      6*x^3*u^3*r^7 - x^3*y*u*r^8 + 3*x^3*u^2*r^8 - 12*x^2*u^8*r^2 - 3*x^2*y*u^6*r^3 -
      24*x^2*u^7*r^3 + 3*x^4*u^4*r^4 - 3*x^2*y*u^5*r^4 - 20*x^2*u^6*r^4 + x^4*u^3*r^5 -
      3*x^2*y*u^4*r^5 - 16*x^2*u^5*r^5 + 7*x^4*u^2*r^6 - 9*x^2*y*u^3*r^6 - 8*x^2*u^4*r^6 -
      x^4*u*r^7 - 6*x^2*y*u^2*r^7 + 3*x*u^10 + 6*x*u^9*r - 3*x^3*u^6*r^2 - 2*x*y*u^7*r^2 +
      10*x*u^8*r^2 - x^3*u^5*r^3 + 5*x*y*u^6*r^3 + 14*x*u^7*r^3 - 19*x^3*u^4*r^4 +
      2*x*y^2*u^4*r^4 + 15*x*y*u^5*r^4 + 7*x*u^6*r^4 - 11*x^3*u^3*r^5 + 4*x*y^2*u^3*r^5 +
      7*x*y*u^4*r^5 + 4*x^3*y*u*r^6 - 10*x^3*u^2*r^6 + 2*x*y^2*u^2*r^6 - x*y*u^3*r^6 -
      2*u^10 - 2*x^2*u^7*r - 3*y*u^8*r - 4*u^9*r + 19*x^2*u^6*r^2 - 5*y*u^7*r^2 -
      2*u^8*r^2 + 4*x^2*y*u^4*r^3 + 19*x^2*u^5*r^3 + 2*y^2*u^5*r^3 - y*u^6*r^3 +
      4*x^2*y*u^3*r^4 + 17*x^2*u^4*r^4 + 4*y^2*u^4*r^4 + y*u^5*r^4 + 4*x^4*u*r^5 +
      12*x^2*y*u^2*r^5 - x^2*u^3*r^5 + 2*y^2*u^3*r^5 - 7*x*u^8 - 7*x*u^7*r +
      2*x^3*u^4*r^2 + 4*x*y*u^5*r^2 - 9*x*u^6*r^2 - 4*x*y*u^4*r^3 + x*u^5*r^3 +
      10*x^3*u^2*r^4 + 4*x*y*u^3*r^4 + 2*u^8 + 2*x^2*u^5*r + 4*y*u^6*r - 8*x^2*u^4*r^2 +
      2*x^2*u^3*r^3 + 4*x*u^6) * heq
  · field_simp
    ring
