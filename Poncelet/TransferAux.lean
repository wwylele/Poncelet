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

variable {u r} in
theorem fabc_w_sub_singularAbc_not_singularAbc (hu : u ≠ 0) (hr : r ≠ 0) {x y wx wy : ℂ}
    (hxy : (elliptic u r).Nonsingular x y) (hwxy : (elliptic u r).Nonsingular wx wy)
    (hpw : .some hxy ≠ w hu hr) (hpnw : .some hxy ≠ -w hu hr)
    (hwxyeq : w hu hr - .some hxy = .some hwxy)
    (hsxy : SingularAbc u r x y) (hwsxy : ¬ SingularAbc u r wx wy) (hur : u ^ 2 - r ^ 2 ≠ 0) :
    fabc hu hr (.some hwxy) = fabc hu hr (.some hxy) := by
  obtain hx := x_not_at_w hu hr hxy hpw hpnw
  have hk : k u r ≠ 0 := hsxy.k_ne_zero u hr hxy
  have : r ^ 2 * x - u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  have : u ^ 2 - r ^ 2 * x ≠ 0 := by
    contrapose! this
    linear_combination -this
  rw [w_sub hu hr hxy hx, Point.some.injEq] at hwxyeq
  obtain ⟨hwx, hwy⟩ := hwxyeq
  have hur : u + r ≠ 0 := by
    contrapose! hur
    linear_combination (u - r) * hur
  have hy : y = (u - r) * (r * ((u + r) ^ 2 - 2) * x - u * (u + r) ^ 2) /
      (-2 * r ^ 2 * (u + r)) := by
    field_simp
    linear_combination -hsxy.xy_linear hu hr hxy
  obtain hc := hsxy.c_factor_eq_zero u hr hxy
  suffices P2.mk (fabcNormal u r wx wy) _ =
      P2.mk ![2 * u * k u r * ((u ^ 2 - r ^ 2) ^ 2 + 4 * u ^ 2),
      (r * (u + r) ^ 2 * x - u * ((u + r) ^ 2 - 2)) * ((u ^ 2 - r ^ 2) ^ 2 - 4 * u ^ 2),
      8 * u ^ 2 * k u r * (u ^ 2 - r ^ 2)] _ by
    simpa [fabc, fabcRaw, hsxy, hwsxy]
  rw [P2.mk_eq_mk']
  use fabcNormal u r wx wy 2 / (8 * u ^ 2 * k u r * (u ^ 2 - r ^ 2))
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  rw [← hwx, ← hwy]
  unfold fabcNormal
  simp_rw [hy]
  simp only [Matrix.cons_val]
  congrm ![?_, ?_, ?_]
  · field_simp
    linear_combination -2 * ((x^4*u^9*r^7 + x^4*u^8*r^8 - 4*x^4*u^7*r^9
    - 4*x^4*u^6*r^10 + 6*x^4*u^5*r^11 + 6*x^4*u^4*r^12 - 4*x^4*u^3*r^13
    - 4*x^4*u^2*r^14 + x^4*u*r^15 + x^4*r^16 - 6*x^3*u^11*r^5 - 8*x^3*u^10*r^6
    + 22*x^3*u^9*r^7 + 32*x^3*u^8*r^8 - 28*x^3*u^7*r^9 - 48*x^3*u^6*r^10
    + 12*x^3*u^5*r^11 + 32*x^3*u^4*r^12 + 2*x^3*u^3*r^13 - 8*x^3*u^2*r^14
    - 2*x^3*u*r^15 + 12*x^2*u^13*r^3 + 18*x^2*u^12*r^4 - 42*x^2*u^11*r^5
    - 72*x^2*u^10*r^6 + 48*x^2*u^9*r^7 + 8*x^4*u^6*r^8 + 108*x^2*u^8*r^8
    + 8*x^4*u^5*r^9 - 12*x^2*u^7*r^9 - 16*x^4*u^4*r^10 - 72*x^2*u^6*r^10
    - 16*x^4*u^3*r^11 - 12*x^2*u^5*r^11 + 8*x^4*u^2*r^12 + 18*x^2*u^4*r^12
    + 8*x^4*u*r^13 + 6*x^2*u^3*r^13 - 8*x*u^15*r - 12*x*u^14*r^2 + 26*x*u^13*r^3
    + 44*x*u^12*r^4 + 12*x^3*u^9*r^5 - 26*x*u^11*r^5 - 12*x^3*u^8*r^6
    - 56*x*u^10*r^6 - 52*x^3*u^7*r^7 + 4*x*u^9*r^7 + 20*x^3*u^6*r^8 + 24*x*u^8*r^8
    + 68*x^3*u^5*r^9 + 4*x*u^7*r^9 - 4*x^3*u^4*r^10 + 4*x*u^6*r^10 - 28*x^3*u^3*r^11
    + 2*x*u^5*r^11 - 4*x^3*u^2*r^12 - 4*x*u^4*r^12 - 2*x*u^3*r^13 + 4*u^15*r
    + 6*u^14*r^2 - 48*x^2*u^11*r^3 - 15*u^13*r^3 - 44*x^2*u^10*r^4 - 25*u^12*r^4
    + 124*x^2*u^9*r^5 + 20*u^11*r^5 + 132*x^2*u^8*r^6 + 40*u^10*r^6 - 84*x^2*u^7*r^7
    - 10*u^9*r^7 - 132*x^2*u^6*r^8 - 30*u^8*r^8 + 16*x^4*u^3*r^9 - 12*x^2*u^5*r^9
    + 16*x^4*u^2*r^10 + 44*x^2*u^4*r^10 + 10*u^6*r^10 + 20*x^2*u^3*r^11 + u^5*r^11
    - u^4*r^12 + 48*x*u^13*r + 68*x*u^12*r^2 - 104*x*u^11*r^3 - 196*x*u^10*r^4
    + 36*x*u^9*r^5 + 48*x^3*u^6*r^6 + 196*x*u^8*r^6 - 16*x^3*u^5*r^7 + 52*x*u^7*r^7
    - 112*x^3*u^4*r^8 - 76*x*u^6*r^8 - 48*x^3*u^3*r^9 - 36*x*u^5*r^9 + 8*x*u^4*r^10
    + 4*x*u^3*r^11 - 8*u^14 - 24*u^13*r + 12*u^12*r^2 + 48*x^2*u^9*r^3 + 68*u^11*r^3
    - 32*x^2*u^8*r^4 + 4*u^10*r^4 - 48*x^2*u^7*r^5 - 68*u^9*r^5 + 144*x^2*u^6*r^6
    - 12*u^8*r^6 + 128*x^2*u^5*r^7 + 28*u^7*r^7 - 16*x^2*u^4*r^8 + 4*u^6*r^8
    - 32*x^2*u^3*r^9 - 4*u^5*r^9 - 96*x*u^11*r - 80*x*u^10*r^2 + 112*x*u^9*r^3
    + 48*x*u^8*r^4 - 112*x*u^7*r^5 - 32*x*u^6*r^6 + 64*x^3*u^3*r^7 + 32*x*u^5*r^7
    + 16*u^12 + 32*u^11*r - 16*u^9*r^3 + 64*x^2*u^6*r^4 - 64*x^2*u^5*r^5 + 64*x*u^9*r)) * hc
  · field_simp
    rw [k_sq]
    linear_combination -(x^5*u^11*r^8 + 3*x^5*u^10*r^9 - x^5*u^9*r^10
    - 11*x^5*u^8*r^11 - 6*x^5*u^7*r^12 + 14*x^5*u^6*r^13 + 14*x^5*u^5*r^14
    - 6*x^5*u^4*r^15 - 11*x^5*u^3*r^16 - x^5*u^2*r^17 + 3*x^5*u*r^18 + x^5*r^19
    - 6*x^4*u^13*r^6 - 17*x^4*u^12*r^7 + 9*x^4*u^11*r^8 + 65*x^4*u^10*r^9
    + 25*x^4*u^9*r^10 - 90*x^4*u^8*r^11 - 70*x^4*u^7*r^12 + 50*x^4*u^6*r^13
    + 60*x^4*u^5*r^14 - 5*x^4*u^4*r^15 - 19*x^4*u^3*r^16 - 3*x^4*u^2*r^17
    + x^4*u*r^18 + 12*x^3*u^15*r^4 + 32*x^3*u^14*r^5 - 22*x^3*u^13*r^6
    - 122*x^3*u^12*r^7 - 4*x^5*u^9*r^8 - 30*x^3*u^11*r^8 - 8*x^5*u^8*r^9
    + 170*x^3*u^10*r^9 + 8*x^5*u^7*r^10 + 100*x^3*u^9*r^10 + 24*x^5*u^6*r^11
    - 100*x^3*u^8*r^11 - 80*x^3*u^7*r^12 - 24*x^5*u^4*r^13 + 20*x^3*u^6*r^13
    - 8*x^5*u^3*r^14 + 18*x^3*u^5*r^14 + 8*x^5*u^2*r^15 - 2*x^3*u^4*r^15
    + 4*x^5*u*r^16 + 2*x^3*u^3*r^16 + 2*x^3*u^2*r^17 - 8*x^2*u^17*r^2
    - 20*x^2*u^16*r^3 + 12*x^2*u^15*r^4 + 62*x^2*u^14*r^5 + 36*x^4*u^11*r^6
    + 18*x^2*u^13*r^6 + 78*x^4*u^10*r^7 - 50*x^2*u^12*r^7 - 58*x^4*u^9*r^8
    - 30*x^2*u^11*r^8 - 224*x^4*u^8*r^9 - 20*x^2*u^10*r^9 - 40*x^4*u^7*r^10
    - 20*x^2*u^9*r^10 + 204*x^4*u^6*r^11 + 40*x^2*u^8*r^11 + 108*x^4*u^5*r^12
    + 48*x^2*u^7*r^12 - 48*x^4*u^4*r^13 - 10*x^2*u^6*r^13 - 44*x^4*u^3*r^14
    - 22*x^2*u^5*r^14 - 10*x^4*u^2*r^15 - 2*x^2*u^4*r^15 - 2*x^4*u*r^16
    + 2*x^2*u^3*r^16 + 8*x*u^17*r^2 + 20*x*u^16*r^3 - 96*x^3*u^13*r^4
    - 19*x*u^15*r^4 - 212*x^3*u^12*r^5 - 81*x*u^14*r^5 + 144*x^3*u^11*r^6
    - 5*x*u^13*r^6 + 604*x^3*u^10*r^7 + 125*x*u^12*r^7 + 144*x^3*u^9*r^8
    + 50*x*u^11*r^8 - 16*x^5*u^6*r^9 - 536*x^3*u^8*r^9 - 90*x*u^10*r^9
    - 48*x^5*u^5*r^10 - 336*x^3*u^7*r^10 - 50*x*u^9*r^10 - 48*x^5*u^4*r^11
    + 104*x^3*u^6*r^11 + 30*x*u^8*r^11 - 16*x^5*u^3*r^12 + 144*x^3*u^5*r^12
    + 17*x*u^7*r^12 + 44*x^3*u^4*r^13 - 5*x*u^6*r^13 - x*u^5*r^14 - 4*x^3*u^2*r^15
    + x*u^4*r^15 + 80*x^2*u^15*r^2 - 2*u^17*r^2 + 184*x^2*u^14*r^3 - 5*u^16*r^3
    - 68*x^2*u^13*r^4 + 5*u^15*r^4 - 452*x^2*u^12*r^5 + 21*u^14*r^5
    - 48*x^4*u^9*r^6 - 256*x^2*u^11*r^6 + u^13*r^6 + 16*x^4*u^8*r^7
    + 240*x^2*u^10*r^7 - 34*u^12*r^7 + 320*x^4*u^7*r^8 + 376*x^2*u^9*r^8
    - 14*u^11*r^8 + 352*x^4*u^6*r^9 + 152*x^2*u^8*r^9 + 26*u^10*r^9
    + 32*x^4*u^5*r^10 - 112*x^2*u^7*r^10 + 16*u^9*r^10 - 64*x^4*u^4*r^11
    - 136*x^2*u^6*r^11 - 9*u^8*r^11 + 16*x^4*u^3*r^12 - 20*x^2*u^5*r^12
    - 7*u^7*r^12 + 16*x^4*u^2*r^13 + 12*x^2*u^4*r^13 + u^6*r^13 + u^5*r^14
    - 16*x*u^16*r - 108*x*u^15*r^2 - 112*x*u^14*r^3 + 240*x^3*u^11*r^4
    + 272*x*u^13*r^4 + 216*x^3*u^10*r^5 + 464*x*u^12*r^5 - 808*x^3*u^9*r^6
    - 144*x*u^11*r^6 - 1160*x^3*u^8*r^7 - 552*x*u^10*r^7 - 104*x^3*u^7*r^8
    - 120*x*u^9*r^8 + 360*x^3*u^6*r^9 + 232*x*u^8*r^9 + 40*x^3*u^5*r^10
    + 124*x*u^7*r^10 - 56*x^3*u^4*r^11 - 8*x*u^6*r^11 - 8*x^3*u^3*r^12
    - 24*x*u^5*r^12 - 8*x*u^4*r^13 + 8*u^17 + 28*u^16*r - 288*x^2*u^13*r^2
    + 12*u^15*r^2 - 368*x^2*u^12*r^3 - 78*u^14*r^3 + 728*x^2*u^11*r^4
    - 106*u^13*r^4 + 1464*x^2*u^10*r^5 + 56*u^12*r^5 + 504*x^2*u^9*r^6
    + 168*u^11*r^6 - 128*x^4*u^6*r^7 - 520*x^2*u^8*r^7 + 20*u^10*r^7
    - 192*x^4*u^5*r^8 - 472*x^2*u^7*r^8 - 108*u^9*r^8 - 32*x^4*u^4*r^9
    + 8*x^2*u^6*r^9 - 36*u^8*r^9 + 32*x^4*u^3*r^10 + 168*x^2*u^5*r^10
    + 28*u^7*r^10 + 56*x^2*u^4*r^11 + 10*u^6*r^11 - 2*u^5*r^12 + 32*x*u^14*r
    + 120*x*u^13*r^2 - 240*x*u^12*r^3 - 192*x^3*u^9*r^4 - 856*x*u^11*r^4
    + 256*x^3*u^8*r^5 - 296*x*u^10*r^5 + 800*x^3*u^7*r^6 + 616*x*u^9*r^6
    + 96*x^3*u^6*r^7 + 280*x*u^8*r^7 - 352*x^3*u^5*r^8 - 216*x*u^7*r^8
    - 96*x^3*u^4*r^9 - 104*x*u^6*r^9 + 16*x*u^5*r^10 + 8*x*u^4*r^11
    + 16*u^14*r + 448*x^2*u^11*r^2 + 56*u^13*r^2 + 32*x^2*u^10*r^3
    + 88*u^12*r^3 - 1152*x^2*u^9*r^4 + 40*u^11*r^4 - 608*x^2*u^8*r^5
    - 56*u^10*r^5 + 416*x^2*u^7*r^6 - 40*u^9*r^6 + 320*x^2*u^6*r^7
    + 24*u^8*r^7 - 32*x^2*u^5*r^8 + 8*u^7*r^8 - 64*x^2*u^4*r^9 - 8*u^6*r^9
    + 64*x*u^12*r + 96*x*u^11*r^2 + 288*x*u^10*r^3 + 224*x*u^9*r^4
    - 256*x^3*u^6*r^5 - 160*x*u^8*r^5 - 64*x*u^7*r^6 + 128*x^3*u^4*r^7
    + 64*x*u^6*r^7 - 32*u^13 - 64*u^12*r - 256*x^2*u^9*r^2 + 256*x^2*u^8*r^3
    + 32*u^10*r^3 + 128*x^2*u^7*r^4 - 128*x^2*u^6*r^5 - 128*x*u^10*r) * hc
  · field_simp
