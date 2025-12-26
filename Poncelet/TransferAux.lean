import Mathlib
import Poncelet.Elliptic

set_option linter.style.longLine false

open WeierstrassCurve.Affine

variable (cf : Config)

theorem fabc_w_sub_c_eq_zero {x y wx wy : ℂ}
    (hxy : (elliptic cf).Nonsingular x y) (hwxy : (elliptic cf).Nonsingular wx wy)
    (hpw : .some hxy ≠ w cf) (hpnw : .some hxy ≠ -w cf)
    (hwxyeq : w cf - .some hxy = .some hwxy)
    (hsxy : ¬ SingularAbc cf x y) (hwsxy : ¬ SingularAbc cf wx wy)
    (hc : (cf.r * x + cf.u) * ((cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x) = 0) :
    fabc cf (.some hwxy) = fabc cf (.some hxy) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  obtain hx := x_not_at_w cf hxy hpw hpnw
  have : cf.r ^ 2 * x - cf.u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  have : cf.u ^ 2 - cf.r ^ 2 * x ≠ 0 := by
    contrapose! this
    linear_combination -this
  suffices P2.mk (fabcNormal cf wx wy) _ = P2.mk (fabcNormal cf x y) _ by
    simpa [fabc, fabcRaw, hsxy, hwsxy]
  rw [P2.mk_eq_mk']
  rw [w_sub cf hxy hx, Point.some.injEq] at hwxyeq
  rw [← hwxyeq.1, ← hwxyeq.2]
  unfold fabcNormal
  have hdeno : -2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u) * y +
      (cf.r * x + cf.u) *
      (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 + 2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2) ≠ 0 := by
    contrapose! hsxy with hdeno
    apply SingularAbc.mk cf hxy hdeno hc
  set deno := -2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u) * y +
      (cf.r * x + cf.u) *
      (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 + 2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2)
  use (-2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) *
      (cf.r * (cf.u ^ 2 * (cf.r ^ 2 * x ^ 2 + (2 - cf.r ^ 2 - cf.u ^ 2) * x + cf.u ^ 2 + 2 * cf.r * y) /
      (cf.r ^ 2 * x - cf.u ^ 2) ^ 2) - cf.u) *
      (cf.u ^ 2 *
      (cf.r ^ 4 * x ^ 3 + cf.r ^ 2 * (2 + cf.u ^ 2 - 2 * cf.r ^ 2) * x ^ 2 +
      cf.u ^ 2 * (2 - 2 * cf.u ^ 2 + cf.r ^ 2) * x + cf.u ^ 4 +
      (cf.r ^ 2 * (2 + cf.u ^ 2 - cf.r ^ 2) * x + cf.u ^ 2 * (2 - cf.u ^ 2 + cf.r ^ 2)) * cf.r * y) /
      (cf.r * (cf.r ^ 2 * x - cf.u ^ 2) ^ 3)) +
      (cf.r * (cf.u ^ 2 * (cf.r ^ 2 * x ^ 2 + (2 - cf.r ^ 2 - cf.u ^ 2) * x + cf.u ^ 2 + 2 * cf.r * y) /
      (cf.r ^ 2 * x - cf.u ^ 2) ^ 2) + cf.u) *
      (cf.r ^ 2 * (cf.u + cf.r) *
      (cf.u ^ 2 * (cf.r ^ 2 * x ^ 2 + (2 - cf.r ^ 2 - cf.u ^ 2) * x + cf.u ^ 2 + 2 * cf.r * y) /
      (cf.r ^ 2 * x - cf.u ^ 2) ^ 2) ^ 2 +
      2 * cf.r * (1 - cf.r * (cf.u + cf.r)) *
      (cf.u ^ 2 * (cf.r ^ 2 * x ^ 2 + (2 - cf.r ^ 2 - cf.u ^ 2) * x + cf.u ^ 2 + 2 * cf.r * y) /
      (cf.r ^ 2 * x - cf.u ^ 2) ^ 2) +
      (cf.u + cf.r) * cf.u ^ 2)) /
      deno
  obtain ⟨heq, hnonsingular⟩ := (nonsingular_elliptic cf _ _).mp hxy
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![?_, ?_, ?_]
  · field_simp
  · field_simp
    linear_combination -8 * cf.k * cf.u * cf.r ^3 * (
      -x^5*cf.u^5*cf.r^6 - 2*x^5*cf.u^4*cf.r^7 + 2*x^5*cf.u^2*cf.r^9 + x^5*cf.u*cf.r^10 + 2*x^4*cf.u^7*cf.r^4
      + 4*x^4*cf.u^6*cf.r^5 + 3*x^4*cf.u^5*cf.r^6 + 2*x^4*cf.u^4*cf.r^7 - 2*x^4*cf.u^3*cf.r^8 - 6*x^4*cf.u^2*cf.r^9
      - 3*x^4*cf.u*cf.r^10 - x^3*cf.u^9*cf.r^2 - 2*x^3*cf.u^8*cf.r^3 - 7*x^3*cf.u^7*cf.r^4 - 3*x^3*y*cf.u^5*cf.r^5
      - 12*x^3*cf.u^6*cf.r^5 - 8*x^3*y*cf.u^4*cf.r^6 - x^3*cf.u^5*cf.r^6 - 3*x^5*cf.u^2*cf.r^7
      - 4*x^3*y*cf.u^3*cf.r^7 + 10*x^3*cf.u^4*cf.r^7 - 4*x^5*cf.u*cf.r^8 + 6*x^3*y*cf.u^2*cf.r^8
      + 7*x^3*cf.u^3*cf.r^8 - x^5*cf.r^9 + 7*x^3*y*cf.u*cf.r^9 + 4*x^3*cf.u^2*cf.r^9 + 2*x^3*y*cf.r^10
      + 2*x^3*cf.u*cf.r^10 + 5*x^2*cf.u^9*cf.r^2 + 3*x^2*y*cf.u^7*cf.r^3 + 10*x^2*cf.u^8*cf.r^3
      - 3*x^4*cf.u^5*cf.r^4 + 10*x^2*y*cf.u^6*cf.r^4 + 5*x^2*cf.u^7*cf.r^4 - 2*x^4*cf.u^4*cf.r^5
      + 12*x^2*y*cf.u^5*cf.r^5 + 5*x^4*cf.u^3*cf.r^6 + 2*x^2*y*cf.u^4*cf.r^6 - 5*x^2*cf.u^5*cf.r^6
      + 16*x^4*cf.u^2*cf.r^7 - 11*x^2*y*cf.u^3*cf.r^7 - 10*x^2*cf.u^4*cf.r^7 + 14*x^4*cf.u*cf.r^8
      - 12*x^2*y*cf.u^2*cf.r^8 - 5*x^2*cf.u^3*cf.r^8 + 2*x^4*cf.r^9 - 4*x^2*y*cf.u*cf.r^9
      - x*cf.u^11 - 2*x*cf.u^10*cf.r + 3*x^3*cf.u^7*cf.r^2 - 2*x*y*cf.u^8*cf.r^2 - 4*x*cf.u^9*cf.r^2
      + 7*x^3*cf.u^6*cf.r^3 - 9*x*y*cf.u^7*cf.r^3 - 6*x*cf.u^8*cf.r^3 + 8*x^3*cf.u^5*cf.r^4
      - 2*x*y^2*cf.u^5*cf.r^4 - 10*x*y*cf.u^6*cf.r^4 + x*cf.u^7*cf.r^4 - 12*x^3*cf.u^4*cf.r^5
      - 6*x*y^2*cf.u^4*cf.r^5 + 4*x*y*cf.u^5*cf.r^5 + 8*x*cf.u^6*cf.r^5 - 4*x^3*y*cf.u^2*cf.r^6
      - 25*x^3*cf.u^3*cf.r^6 - 6*x*y^2*cf.u^3*cf.r^6 + 12*x*y*cf.u^4*cf.r^6 + 4*x*cf.u^5*cf.r^6
      - 6*x^3*y*cf.u*cf.r^7 - 19*x^3*cf.u^2*cf.r^7 - 2*x*y^2*cf.u^2*cf.r^7 + 5*x*y*cf.u^3*cf.r^7
      - 2*x^3*y*cf.r^8 - 10*x^3*cf.u*cf.r^8 + cf.u^11 - 2*x^2*cf.u^8*cf.r + y*cf.u^9*cf.r + 2*cf.u^10*cf.r
      - 12*x^2*cf.u^7*cf.r^2 + 2*y*cf.u^8*cf.r^2 - 4*x^2*y*cf.u^5*cf.r^3 - 8*x^2*cf.u^6*cf.r^3
      + 2*y^2*cf.u^6*cf.r^3 - 2*cf.u^8*cf.r^3 - 12*x^2*y*cf.u^4*cf.r^4 + 10*x^2*cf.u^5*cf.r^4
      + 6*y^2*cf.u^5*cf.r^4 - 2*y*cf.u^6*cf.r^4 - cf.u^7*cf.r^4 - 4*x^4*cf.u^2*cf.r^5 - 6*x^2*y*cf.u^3*cf.r^5
      + 26*x^2*cf.u^4*cf.r^5 + 6*y^2*cf.u^4*cf.r^5 - y*cf.u^5*cf.r^5 - 10*x^4*cf.u*cf.r^6
      + 14*x^2*y*cf.u^2*cf.r^6 + 18*x^2*cf.u^3*cf.r^6 + 2*y^2*cf.u^3*cf.r^6 - 2*x^4*cf.r^7
      + 12*x^2*y*cf.u*cf.r^7 + 3*x*cf.u^9 + 5*x*cf.u^8*cf.r - 2*x^3*cf.u^5*cf.r^2
      + 8*x*y*cf.u^6*cf.r^2 + 2*x*cf.u^7*cf.r^2 - 6*x^3*cf.u^4*cf.r^3 + 14*x*y*cf.u^5*cf.r^3
      - 9*x*cf.u^6*cf.r^3 + 8*x^3*cf.u^3*cf.r^4 - 2*x*y*cf.u^4*cf.r^4 - 9*x*cf.u^5*cf.r^4
      + 16*x^3*cf.u^2*cf.r^5 - 8*x*y*cf.u^3*cf.r^5 + 16*x^3*cf.u*cf.r^6 - cf.u^9 + 6*x^2*cf.u^6*cf.r
      - 2*y*cf.u^7*cf.r + 4*x^2*cf.u^5*cf.r^2 - 2*y*cf.u^6*cf.r^2 + cf.u^7*cf.r^2 - 8*x^2*cf.u^4*cf.r^3
      - 4*y^2*cf.u^4*cf.r^3 - 18*x^2*cf.u^3*cf.r^4 - 4*y^2*cf.u^3*cf.r^4 - 8*x^2*y*cf.u*cf.r^5
      - 2*x*cf.u^7 - 2*x*cf.u^6*cf.r - 8*x*y*cf.u^4*cf.r^2 + 4*x*cf.u^5*cf.r^2 - 8*x^3*cf.u*cf.r^4
      - 4*x^2*cf.u^4*cf.r + 4*x^2*cf.u^3*cf.r^2) * heq
  · field_simp
    linear_combination 8 * (cf.u + cf.r - 1) * (cf.u + cf.r + 1) * cf.u^2 * cf.r^3 *
      (-x^5*cf.u^3*cf.r^6 - x^5*cf.u^2*cf.r^7 + x^5*cf.u*cf.r^8 + x^5*cf.r^9 + 2*x^4*cf.u^5*cf.r^4
      + 2*x^4*cf.u^4*cf.r^5 - x^4*cf.u^3*cf.r^6 - x^4*cf.u^2*cf.r^7 - x^4*cf.u*cf.r^8 - x^4*cf.r^9
      - x^3*cf.u^7*cf.r^2 - x^3*cf.u^6*cf.r^3 - 3*x^3*y*cf.u^3*cf.r^5 - 5*x^3*y*cf.u^2*cf.r^6
      + x^3*cf.u^3*cf.r^6 - 2*x^5*cf.r^7 - x^3*y*cf.u*cf.r^7 + x^3*cf.u^2*cf.r^7 + x^3*y*cf.r^8
      - x^2*cf.u^7*cf.r^2 + 3*x^2*y*cf.u^5*cf.r^3 - x^2*cf.u^6*cf.r^3 - 3*x^4*cf.u^3*cf.r^4
      + 7*x^2*y*cf.u^4*cf.r^4 - x^4*cf.u^2*cf.r^5 + 7*x^2*y*cf.u^3*cf.r^5 + x^4*cf.u*cf.r^6
      + 5*x^2*y*cf.u^2*cf.r^6 + x^2*cf.u^3*cf.r^6 + 5*x^4*cf.r^7 + 2*x^2*y*cf.u*cf.r^7
      + x^2*cf.u^2*cf.r^7 + x*cf.u^9 + x*cf.u^8*cf.r + 3*x^3*cf.u^5*cf.r^2 - 2*x*y*cf.u^6*cf.r^2
      + x*cf.u^7*cf.r^2 + 5*x^3*cf.u^4*cf.r^3 - 5*x*y*cf.u^5*cf.r^3 + x*cf.u^6*cf.r^3 - x^3*cf.u^3*cf.r^4
      - 2*x*y^2*cf.u^3*cf.r^4 - 7*x*y*cf.u^4*cf.r^4 - 2*x*cf.u^5*cf.r^4 - 5*x^3*cf.u^2*cf.r^5
      - 4*x*y^2*cf.u^2*cf.r^5 - 7*x*y*cf.u^3*cf.r^5 - 2*x*cf.u^4*cf.r^5 - 4*x^3*y*cf.r^6
      + 2*x^3*cf.u*cf.r^6 - 2*x*y^2*cf.u*cf.r^6 - 3*x*y*cf.u^2*cf.r^6 - cf.u^9 - 2*x^2*cf.u^6*cf.r
      - y*cf.u^7*cf.r - cf.u^8*cf.r + 5*x^2*cf.u^5*cf.r^2 + y*cf.u^6*cf.r^2 + cf.u^7*cf.r^2 - 4*x^2*y*cf.u^3*cf.r^3
      + x^2*cf.u^4*cf.r^3 + 2*y^2*cf.u^4*cf.r^3 + 5*y*cf.u^5*cf.r^3 + cf.u^6*cf.r^3 - 4*x^2*y*cf.u^2*cf.r^4
      - 5*x^2*cf.u^3*cf.r^4 + 4*y^2*cf.u^3*cf.r^4 + 3*y*cf.u^4*cf.r^4 - 4*x^4*cf.r^5 - 4*x^2*y*cf.u*cf.r^5
      - 3*x^2*cf.u^2*cf.r^5 + 2*y^2*cf.u^2*cf.r^5 - 5*x*cf.u^7 - x*cf.u^6*cf.r - 2*x^3*cf.u^3*cf.r^2
      + 4*x*y*cf.u^4*cf.r^2 + x*cf.u^5*cf.r^2 + 4*x*y*cf.u^3*cf.r^3 + 3*x*cf.u^4*cf.r^3 - 2*x^3*cf.u*cf.r^4
      + 4*x*y*cf.u^2*cf.r^4 + 2*cf.u^7 + 2*x^2*cf.u^4*cf.r + 4*y*cf.u^5*cf.r + 2*x^2*cf.u^2*cf.r^3 + 4*x*cf.u^5)* heq

theorem fabc_w_sub_c_ne_zero {x y wx wy : ℂ}
    (hxy : (elliptic cf).Nonsingular x y) (hwxy : (elliptic cf).Nonsingular wx wy)
    (hpw : .some hxy ≠ w cf) (hpnw : .some hxy ≠ -w cf)
    (hwxyeq : w cf - .some hxy = .some hwxy)
    (hsxy : ¬ SingularAbc cf x y) (hwsxy : ¬ SingularAbc cf wx wy)
    (hc : (cf.r * x + cf.u) * ((cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x) ≠ 0) :
    fabc cf (.some hwxy) = fabc cf (.some hxy) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  obtain hx := x_not_at_w cf hxy hpw hpnw
  have : cf.r ^ 2 * x - cf.u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  have : cf.u ^ 2 - cf.r ^ 2 * x ≠ 0 := by
    contrapose! this
    linear_combination -this
  have hinf1' : cf.r * x + cf.u ≠ 0 := by
    contrapose! hc
    simp [hc]
  have hinf2' : (cf.u + cf.r) ^ 2 * (cf.r * x - cf.u) ^ 2 + cf.r * cf.u * x * 4 ≠ 0 := by
    contrapose! hc
    linear_combination (cf.r * x + cf.u) * hc
  set inf2 := (cf.u + cf.r) ^ 2 * (cf.r * x - cf.u) ^ 2 + cf.r * cf.u * x * 4
  obtain ⟨heq, hnonsingular⟩ := (nonsingular_elliptic cf _ _).mp hxy
  suffices P2.mk (fabcNormal cf wx wy) _ = P2.mk (fabcNormal cf x y) _ by
    simpa [fabc, fabcRaw, hsxy, hwsxy]
  rw [P2.mk_eq_mk']
  rw [w_sub cf hxy hx, Point.some.injEq] at hwxyeq
  rw [← hwxyeq.1, ← hwxyeq.2]
  unfold fabcNormal
  use (cf.u ^ 3 * (cf.r * cf.u * (x * (cf.r ^ 2 * x + (2 - cf.r ^ 2 - cf.u ^ 2)) + cf.u ^ 2 + cf.r * 2 * y) +
    (cf.r ^ 2 * x - cf.u ^ 2) ^ 2) *
    ((cf.r * cf.u * (x * (cf.r ^ 2 * x + (2 - cf.r ^ 2 - cf.u ^ 2)) + cf.u ^ 2 + cf.r * 2 * y) -
    (cf.r ^ 2 * x - cf.u ^ 2) ^ 2) ^ 2 * (cf.u + cf.r) ^ 2 +
      cf.r * cf.u * (x * (cf.r ^ 2 * x + (2 - cf.r ^ 2 - cf.u ^ 2)) + cf.u ^ 2 + cf.r * 2 * y) *
      (cf.r ^ 2 * x - cf.u ^ 2) ^ 2 * 4))  /
      ((cf.r ^ 2 * x - cf.u ^ 2) ^ 6  * (cf.r * x + cf.u) * inf2)
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  congrm ![?_, ?_, ?_]
  · field_simp
    linear_combination  (-8) * (cf.u + cf.r - 1) * (cf.u + cf.r + 1) * cf.u^2 * cf.r^3 *
      (-x^5*cf.u^3*cf.r^6 - x^5*cf.u^2*cf.r^7 + x^5*cf.u*cf.r^8 + x^5*cf.r^9 + 2*x^4*cf.u^5*cf.r^4 +
      2*x^4*cf.u^4*cf.r^5 - x^4*cf.u^3*cf.r^6 - x^4*cf.u^2*cf.r^7 - x^4*cf.u*cf.r^8 - x^4*cf.r^9 -
      x^3*cf.u^7*cf.r^2 - x^3*cf.u^6*cf.r^3 - 3*x^3*y*cf.u^3*cf.r^5 - 5*x^3*y*cf.u^2*cf.r^6 +
      x^3*cf.u^3*cf.r^6 - 2*x^5*cf.r^7 - x^3*y*cf.u*cf.r^7 + x^3*cf.u^2*cf.r^7 + x^3*y*cf.r^8 -
      x^2*cf.u^7*cf.r^2 + 3*x^2*y*cf.u^5*cf.r^3 - x^2*cf.u^6*cf.r^3 - 3*x^4*cf.u^3*cf.r^4 +
      7*x^2*y*cf.u^4*cf.r^4 - x^4*cf.u^2*cf.r^5 + 7*x^2*y*cf.u^3*cf.r^5 + x^4*cf.u*cf.r^6 +
      5*x^2*y*cf.u^2*cf.r^6 + x^2*cf.u^3*cf.r^6 + 5*x^4*cf.r^7 + 2*x^2*y*cf.u*cf.r^7 +
      x^2*cf.u^2*cf.r^7 + x*cf.u^9 + x*cf.u^8*cf.r + 3*x^3*cf.u^5*cf.r^2 - 2*x*y*cf.u^6*cf.r^2 +
      x*cf.u^7*cf.r^2 + 5*x^3*cf.u^4*cf.r^3 - 5*x*y*cf.u^5*cf.r^3 + x*cf.u^6*cf.r^3 - x^3*cf.u^3*cf.r^4 -
      2*x*y^2*cf.u^3*cf.r^4 - 7*x*y*cf.u^4*cf.r^4 - 2*x*cf.u^5*cf.r^4 - 5*x^3*cf.u^2*cf.r^5 -
      4*x*y^2*cf.u^2*cf.r^5 - 7*x*y*cf.u^3*cf.r^5 - 2*x*cf.u^4*cf.r^5 - 4*x^3*y*cf.r^6 +
      2*x^3*cf.u*cf.r^6 - 2*x*y^2*cf.u*cf.r^6 - 3*x*y*cf.u^2*cf.r^6 - cf.u^9 - 2*x^2*cf.u^6*cf.r -
      y*cf.u^7*cf.r - cf.u^8*cf.r + 5*x^2*cf.u^5*cf.r^2 + y*cf.u^6*cf.r^2 + cf.u^7*cf.r^2 - 4*x^2*y*cf.u^3*cf.r^3 +
      x^2*cf.u^4*cf.r^3 + 2*y^2*cf.u^4*cf.r^3 + 5*y*cf.u^5*cf.r^3 + cf.u^6*cf.r^3 - 4*x^2*y*cf.u^2*cf.r^4 -
      5*x^2*cf.u^3*cf.r^4 + 4*y^2*cf.u^3*cf.r^4 + 3*y*cf.u^4*cf.r^4 - 4*x^4*cf.r^5 - 4*x^2*y*cf.u*cf.r^5 -
      3*x^2*cf.u^2*cf.r^5 + 2*y^2*cf.u^2*cf.r^5 - 5*x*cf.u^7 - x*cf.u^6*cf.r - 2*x^3*cf.u^3*cf.r^2 +
      4*x*y*cf.u^4*cf.r^2 + x*cf.u^5*cf.r^2 + 4*x*y*cf.u^3*cf.r^3 + 3*x*cf.u^4*cf.r^3 - 2*x^3*cf.u*cf.r^4 +
      4*x*y*cf.u^2*cf.r^4 + 2*cf.u^7 + 2*x^2*cf.u^4*cf.r + 4*y*cf.u^5*cf.r + 2*x^2*cf.u^2*cf.r^3 + 4*x*cf.u^5) * heq
  · field_simp
    linear_combination 8 * cf.k * cf.u * cf.r ^ 3 *
      (x^5*cf.u^4*cf.r^6 + 2*x^5*cf.u^3*cf.r^7 + 2*x^5*cf.u^2*cf.r^8 + 2*x^5*cf.u*cf.r^9 + x^5*cf.r^10 -
      2*x^4*cf.u^6*cf.r^4 - 4*x^4*cf.u^5*cf.r^5 - 10*x^4*cf.u^4*cf.r^6 - 16*x^4*cf.u^3*cf.r^7 -
      8*x^4*cf.u^2*cf.r^8 + x^3*cf.u^8*cf.r^2 + 2*x^3*cf.u^7*cf.r^3 + 17*x^3*cf.u^6*cf.r^4 + 3*x^3*y*cf.u^4*cf.r^5 +
      32*x^3*cf.u^5*cf.r^5 + 5*x^3*y*cf.u^3*cf.r^6 + 19*x^3*cf.u^4*cf.r^6 + 2*x^5*cf.u*cf.r^7 + x^3*y*cf.u^2*cf.r^7 +
      6*x^3*cf.u^3*cf.r^7 - x^3*y*cf.u*cf.r^8 + 3*x^3*cf.u^2*cf.r^8 - 12*x^2*cf.u^8*cf.r^2 - 3*x^2*y*cf.u^6*cf.r^3 -
      24*x^2*cf.u^7*cf.r^3 + 3*x^4*cf.u^4*cf.r^4 - 3*x^2*y*cf.u^5*cf.r^4 - 20*x^2*cf.u^6*cf.r^4 + x^4*cf.u^3*cf.r^5 -
      3*x^2*y*cf.u^4*cf.r^5 - 16*x^2*cf.u^5*cf.r^5 + 7*x^4*cf.u^2*cf.r^6 - 9*x^2*y*cf.u^3*cf.r^6 - 8*x^2*cf.u^4*cf.r^6 -
      x^4*cf.u*cf.r^7 - 6*x^2*y*cf.u^2*cf.r^7 + 3*x*cf.u^10 + 6*x*cf.u^9*cf.r - 3*x^3*cf.u^6*cf.r^2 - 2*x*y*cf.u^7*cf.r^2 +
      10*x*cf.u^8*cf.r^2 - x^3*cf.u^5*cf.r^3 + 5*x*y*cf.u^6*cf.r^3 + 14*x*cf.u^7*cf.r^3 - 19*x^3*cf.u^4*cf.r^4 +
      2*x*y^2*cf.u^4*cf.r^4 + 15*x*y*cf.u^5*cf.r^4 + 7*x*cf.u^6*cf.r^4 - 11*x^3*cf.u^3*cf.r^5 + 4*x*y^2*cf.u^3*cf.r^5 +
      7*x*y*cf.u^4*cf.r^5 + 4*x^3*y*cf.u*cf.r^6 - 10*x^3*cf.u^2*cf.r^6 + 2*x*y^2*cf.u^2*cf.r^6 - x*y*cf.u^3*cf.r^6 -
      2*cf.u^10 - 2*x^2*cf.u^7*cf.r - 3*y*cf.u^8*cf.r - 4*cf.u^9*cf.r + 19*x^2*cf.u^6*cf.r^2 - 5*y*cf.u^7*cf.r^2 -
      2*cf.u^8*cf.r^2 + 4*x^2*y*cf.u^4*cf.r^3 + 19*x^2*cf.u^5*cf.r^3 + 2*y^2*cf.u^5*cf.r^3 - y*cf.u^6*cf.r^3 +
      4*x^2*y*cf.u^3*cf.r^4 + 17*x^2*cf.u^4*cf.r^4 + 4*y^2*cf.u^4*cf.r^4 + y*cf.u^5*cf.r^4 + 4*x^4*cf.u*cf.r^5 +
      12*x^2*y*cf.u^2*cf.r^5 - x^2*cf.u^3*cf.r^5 + 2*y^2*cf.u^3*cf.r^5 - 7*x*cf.u^8 - 7*x*cf.u^7*cf.r +
      2*x^3*cf.u^4*cf.r^2 + 4*x*y*cf.u^5*cf.r^2 - 9*x*cf.u^6*cf.r^2 - 4*x*y*cf.u^4*cf.r^3 + x*cf.u^5*cf.r^3 +
      10*x^3*cf.u^2*cf.r^4 + 4*x*y*cf.u^3*cf.r^4 + 2*cf.u^8 + 2*x^2*cf.u^5*cf.r + 4*y*cf.u^6*cf.r - 8*x^2*cf.u^4*cf.r^2 +
      2*x^2*cf.u^3*cf.r^3 + 4*x*cf.u^6) * heq
  · field_simp
    ring

theorem fabc_w_sub_singularAbc_not_singularAbc {x y wx wy : ℂ}
    (hxy : (elliptic cf).Nonsingular x y) (hwxy : (elliptic cf).Nonsingular wx wy)
    (hpw : .some hxy ≠ w cf) (hpnw : .some hxy ≠ -w cf)
    (hwxyeq : w cf - .some hxy = .some hwxy)
    (hsxy : SingularAbc cf x y) (hwsxy : ¬ SingularAbc cf wx wy) (hur : cf.u ^ 2 - cf.r ^ 2 ≠ 0) :
    fabc cf (.some hwxy) = fabc cf (.some hxy) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  obtain hx := x_not_at_w cf hxy hpw hpnw
  have hk : cf.k ≠ 0 := hsxy.k_ne_zero cf hxy
  have : cf.r ^ 2 * x - cf.u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  have : cf.u ^ 2 - cf.r ^ 2 * x ≠ 0 := by
    contrapose! this
    linear_combination -this
  rw [w_sub cf hxy hx, Point.some.injEq] at hwxyeq
  obtain ⟨hwx, hwy⟩ := hwxyeq
  have hur : cf.u + cf.r ≠ 0 := by
    contrapose! hur
    linear_combination (cf.u - cf.r) * hur
  have hy : y = (cf.u - cf.r) * (cf.r * ((cf.u + cf.r) ^ 2 - 2) * x - cf.u * (cf.u + cf.r) ^ 2) /
      (-2 * cf.r ^ 2 * (cf.u + cf.r)) := by
    field_simp
    linear_combination -hsxy.xy_linear cf hxy
  obtain hc := hsxy.c_factor_eq_zero cf hxy
  suffices P2.mk (fabcNormal cf wx wy) _ =
      P2.mk ![2 * cf.u * cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2),
      (cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2),
      8 * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2)] _ by
    simpa [fabc, fabcRaw, hsxy, hwsxy]
  rw [P2.mk_eq_mk']
  use fabcNormal cf wx wy 2 / (8 * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2))
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  rw [← hwx, ← hwy]
  unfold fabcNormal
  simp_rw [hy]
  simp only [Matrix.cons_val]
  congrm ![?_, ?_, ?_]
  · field_simp
    linear_combination -2 * ((x^4*cf.u^9*cf.r^7 + x^4*cf.u^8*cf.r^8 - 4*x^4*cf.u^7*cf.r^9
    - 4*x^4*cf.u^6*cf.r^10 + 6*x^4*cf.u^5*cf.r^11 + 6*x^4*cf.u^4*cf.r^12 - 4*x^4*cf.u^3*cf.r^13
    - 4*x^4*cf.u^2*cf.r^14 + x^4*cf.u*cf.r^15 + x^4*cf.r^16 - 6*x^3*cf.u^11*cf.r^5 - 8*x^3*cf.u^10*cf.r^6
    + 22*x^3*cf.u^9*cf.r^7 + 32*x^3*cf.u^8*cf.r^8 - 28*x^3*cf.u^7*cf.r^9 - 48*x^3*cf.u^6*cf.r^10
    + 12*x^3*cf.u^5*cf.r^11 + 32*x^3*cf.u^4*cf.r^12 + 2*x^3*cf.u^3*cf.r^13 - 8*x^3*cf.u^2*cf.r^14
    - 2*x^3*cf.u*cf.r^15 + 12*x^2*cf.u^13*cf.r^3 + 18*x^2*cf.u^12*cf.r^4 - 42*x^2*cf.u^11*cf.r^5
    - 72*x^2*cf.u^10*cf.r^6 + 48*x^2*cf.u^9*cf.r^7 + 8*x^4*cf.u^6*cf.r^8 + 108*x^2*cf.u^8*cf.r^8
    + 8*x^4*cf.u^5*cf.r^9 - 12*x^2*cf.u^7*cf.r^9 - 16*x^4*cf.u^4*cf.r^10 - 72*x^2*cf.u^6*cf.r^10
    - 16*x^4*cf.u^3*cf.r^11 - 12*x^2*cf.u^5*cf.r^11 + 8*x^4*cf.u^2*cf.r^12 + 18*x^2*cf.u^4*cf.r^12
    + 8*x^4*cf.u*cf.r^13 + 6*x^2*cf.u^3*cf.r^13 - 8*x*cf.u^15*cf.r - 12*x*cf.u^14*cf.r^2 + 26*x*cf.u^13*cf.r^3
    + 44*x*cf.u^12*cf.r^4 + 12*x^3*cf.u^9*cf.r^5 - 26*x*cf.u^11*cf.r^5 - 12*x^3*cf.u^8*cf.r^6
    - 56*x*cf.u^10*cf.r^6 - 52*x^3*cf.u^7*cf.r^7 + 4*x*cf.u^9*cf.r^7 + 20*x^3*cf.u^6*cf.r^8 + 24*x*cf.u^8*cf.r^8
    + 68*x^3*cf.u^5*cf.r^9 + 4*x*cf.u^7*cf.r^9 - 4*x^3*cf.u^4*cf.r^10 + 4*x*cf.u^6*cf.r^10 - 28*x^3*cf.u^3*cf.r^11
    + 2*x*cf.u^5*cf.r^11 - 4*x^3*cf.u^2*cf.r^12 - 4*x*cf.u^4*cf.r^12 - 2*x*cf.u^3*cf.r^13 + 4*cf.u^15*cf.r
    + 6*cf.u^14*cf.r^2 - 48*x^2*cf.u^11*cf.r^3 - 15*cf.u^13*cf.r^3 - 44*x^2*cf.u^10*cf.r^4 - 25*cf.u^12*cf.r^4
    + 124*x^2*cf.u^9*cf.r^5 + 20*cf.u^11*cf.r^5 + 132*x^2*cf.u^8*cf.r^6 + 40*cf.u^10*cf.r^6 - 84*x^2*cf.u^7*cf.r^7
    - 10*cf.u^9*cf.r^7 - 132*x^2*cf.u^6*cf.r^8 - 30*cf.u^8*cf.r^8 + 16*x^4*cf.u^3*cf.r^9 - 12*x^2*cf.u^5*cf.r^9
    + 16*x^4*cf.u^2*cf.r^10 + 44*x^2*cf.u^4*cf.r^10 + 10*cf.u^6*cf.r^10 + 20*x^2*cf.u^3*cf.r^11 + cf.u^5*cf.r^11
    - cf.u^4*cf.r^12 + 48*x*cf.u^13*cf.r + 68*x*cf.u^12*cf.r^2 - 104*x*cf.u^11*cf.r^3 - 196*x*cf.u^10*cf.r^4
    + 36*x*cf.u^9*cf.r^5 + 48*x^3*cf.u^6*cf.r^6 + 196*x*cf.u^8*cf.r^6 - 16*x^3*cf.u^5*cf.r^7 + 52*x*cf.u^7*cf.r^7
    - 112*x^3*cf.u^4*cf.r^8 - 76*x*cf.u^6*cf.r^8 - 48*x^3*cf.u^3*cf.r^9 - 36*x*cf.u^5*cf.r^9 + 8*x*cf.u^4*cf.r^10
    + 4*x*cf.u^3*cf.r^11 - 8*cf.u^14 - 24*cf.u^13*cf.r + 12*cf.u^12*cf.r^2 + 48*x^2*cf.u^9*cf.r^3 + 68*cf.u^11*cf.r^3
    - 32*x^2*cf.u^8*cf.r^4 + 4*cf.u^10*cf.r^4 - 48*x^2*cf.u^7*cf.r^5 - 68*cf.u^9*cf.r^5 + 144*x^2*cf.u^6*cf.r^6
    - 12*cf.u^8*cf.r^6 + 128*x^2*cf.u^5*cf.r^7 + 28*cf.u^7*cf.r^7 - 16*x^2*cf.u^4*cf.r^8 + 4*cf.u^6*cf.r^8
    - 32*x^2*cf.u^3*cf.r^9 - 4*cf.u^5*cf.r^9 - 96*x*cf.u^11*cf.r - 80*x*cf.u^10*cf.r^2 + 112*x*cf.u^9*cf.r^3
    + 48*x*cf.u^8*cf.r^4 - 112*x*cf.u^7*cf.r^5 - 32*x*cf.u^6*cf.r^6 + 64*x^3*cf.u^3*cf.r^7 + 32*x*cf.u^5*cf.r^7
    + 16*cf.u^12 + 32*cf.u^11*cf.r - 16*cf.u^9*cf.r^3 + 64*x^2*cf.u^6*cf.r^4 - 64*x^2*cf.u^5*cf.r^5 + 64*x*cf.u^9*cf.r)) * hc
  · field_simp
    rw [cf.k_sq]
    linear_combination -(x^5*cf.u^11*cf.r^8 + 3*x^5*cf.u^10*cf.r^9 - x^5*cf.u^9*cf.r^10
    - 11*x^5*cf.u^8*cf.r^11 - 6*x^5*cf.u^7*cf.r^12 + 14*x^5*cf.u^6*cf.r^13 + 14*x^5*cf.u^5*cf.r^14
    - 6*x^5*cf.u^4*cf.r^15 - 11*x^5*cf.u^3*cf.r^16 - x^5*cf.u^2*cf.r^17 + 3*x^5*cf.u*cf.r^18 + x^5*cf.r^19
    - 6*x^4*cf.u^13*cf.r^6 - 17*x^4*cf.u^12*cf.r^7 + 9*x^4*cf.u^11*cf.r^8 + 65*x^4*cf.u^10*cf.r^9
    + 25*x^4*cf.u^9*cf.r^10 - 90*x^4*cf.u^8*cf.r^11 - 70*x^4*cf.u^7*cf.r^12 + 50*x^4*cf.u^6*cf.r^13
    + 60*x^4*cf.u^5*cf.r^14 - 5*x^4*cf.u^4*cf.r^15 - 19*x^4*cf.u^3*cf.r^16 - 3*x^4*cf.u^2*cf.r^17
    + x^4*cf.u*cf.r^18 + 12*x^3*cf.u^15*cf.r^4 + 32*x^3*cf.u^14*cf.r^5 - 22*x^3*cf.u^13*cf.r^6
    - 122*x^3*cf.u^12*cf.r^7 - 4*x^5*cf.u^9*cf.r^8 - 30*x^3*cf.u^11*cf.r^8 - 8*x^5*cf.u^8*cf.r^9
    + 170*x^3*cf.u^10*cf.r^9 + 8*x^5*cf.u^7*cf.r^10 + 100*x^3*cf.u^9*cf.r^10 + 24*x^5*cf.u^6*cf.r^11
    - 100*x^3*cf.u^8*cf.r^11 - 80*x^3*cf.u^7*cf.r^12 - 24*x^5*cf.u^4*cf.r^13 + 20*x^3*cf.u^6*cf.r^13
    - 8*x^5*cf.u^3*cf.r^14 + 18*x^3*cf.u^5*cf.r^14 + 8*x^5*cf.u^2*cf.r^15 - 2*x^3*cf.u^4*cf.r^15
    + 4*x^5*cf.u*cf.r^16 + 2*x^3*cf.u^3*cf.r^16 + 2*x^3*cf.u^2*cf.r^17 - 8*x^2*cf.u^17*cf.r^2
    - 20*x^2*cf.u^16*cf.r^3 + 12*x^2*cf.u^15*cf.r^4 + 62*x^2*cf.u^14*cf.r^5 + 36*x^4*cf.u^11*cf.r^6
    + 18*x^2*cf.u^13*cf.r^6 + 78*x^4*cf.u^10*cf.r^7 - 50*x^2*cf.u^12*cf.r^7 - 58*x^4*cf.u^9*cf.r^8
    - 30*x^2*cf.u^11*cf.r^8 - 224*x^4*cf.u^8*cf.r^9 - 20*x^2*cf.u^10*cf.r^9 - 40*x^4*cf.u^7*cf.r^10
    - 20*x^2*cf.u^9*cf.r^10 + 204*x^4*cf.u^6*cf.r^11 + 40*x^2*cf.u^8*cf.r^11 + 108*x^4*cf.u^5*cf.r^12
    + 48*x^2*cf.u^7*cf.r^12 - 48*x^4*cf.u^4*cf.r^13 - 10*x^2*cf.u^6*cf.r^13 - 44*x^4*cf.u^3*cf.r^14
    - 22*x^2*cf.u^5*cf.r^14 - 10*x^4*cf.u^2*cf.r^15 - 2*x^2*cf.u^4*cf.r^15 - 2*x^4*cf.u*cf.r^16
    + 2*x^2*cf.u^3*cf.r^16 + 8*x*cf.u^17*cf.r^2 + 20*x*cf.u^16*cf.r^3 - 96*x^3*cf.u^13*cf.r^4
    - 19*x*cf.u^15*cf.r^4 - 212*x^3*cf.u^12*cf.r^5 - 81*x*cf.u^14*cf.r^5 + 144*x^3*cf.u^11*cf.r^6
    - 5*x*cf.u^13*cf.r^6 + 604*x^3*cf.u^10*cf.r^7 + 125*x*cf.u^12*cf.r^7 + 144*x^3*cf.u^9*cf.r^8
    + 50*x*cf.u^11*cf.r^8 - 16*x^5*cf.u^6*cf.r^9 - 536*x^3*cf.u^8*cf.r^9 - 90*x*cf.u^10*cf.r^9
    - 48*x^5*cf.u^5*cf.r^10 - 336*x^3*cf.u^7*cf.r^10 - 50*x*cf.u^9*cf.r^10 - 48*x^5*cf.u^4*cf.r^11
    + 104*x^3*cf.u^6*cf.r^11 + 30*x*cf.u^8*cf.r^11 - 16*x^5*cf.u^3*cf.r^12 + 144*x^3*cf.u^5*cf.r^12
    + 17*x*cf.u^7*cf.r^12 + 44*x^3*cf.u^4*cf.r^13 - 5*x*cf.u^6*cf.r^13 - x*cf.u^5*cf.r^14 - 4*x^3*cf.u^2*cf.r^15
    + x*cf.u^4*cf.r^15 + 80*x^2*cf.u^15*cf.r^2 - 2*cf.u^17*cf.r^2 + 184*x^2*cf.u^14*cf.r^3 - 5*cf.u^16*cf.r^3
    - 68*x^2*cf.u^13*cf.r^4 + 5*cf.u^15*cf.r^4 - 452*x^2*cf.u^12*cf.r^5 + 21*cf.u^14*cf.r^5
    - 48*x^4*cf.u^9*cf.r^6 - 256*x^2*cf.u^11*cf.r^6 + cf.u^13*cf.r^6 + 16*x^4*cf.u^8*cf.r^7
    + 240*x^2*cf.u^10*cf.r^7 - 34*cf.u^12*cf.r^7 + 320*x^4*cf.u^7*cf.r^8 + 376*x^2*cf.u^9*cf.r^8
    - 14*cf.u^11*cf.r^8 + 352*x^4*cf.u^6*cf.r^9 + 152*x^2*cf.u^8*cf.r^9 + 26*cf.u^10*cf.r^9
    + 32*x^4*cf.u^5*cf.r^10 - 112*x^2*cf.u^7*cf.r^10 + 16*cf.u^9*cf.r^10 - 64*x^4*cf.u^4*cf.r^11
    - 136*x^2*cf.u^6*cf.r^11 - 9*cf.u^8*cf.r^11 + 16*x^4*cf.u^3*cf.r^12 - 20*x^2*cf.u^5*cf.r^12
    - 7*cf.u^7*cf.r^12 + 16*x^4*cf.u^2*cf.r^13 + 12*x^2*cf.u^4*cf.r^13 + cf.u^6*cf.r^13 + cf.u^5*cf.r^14
    - 16*x*cf.u^16*cf.r - 108*x*cf.u^15*cf.r^2 - 112*x*cf.u^14*cf.r^3 + 240*x^3*cf.u^11*cf.r^4
    + 272*x*cf.u^13*cf.r^4 + 216*x^3*cf.u^10*cf.r^5 + 464*x*cf.u^12*cf.r^5 - 808*x^3*cf.u^9*cf.r^6
    - 144*x*cf.u^11*cf.r^6 - 1160*x^3*cf.u^8*cf.r^7 - 552*x*cf.u^10*cf.r^7 - 104*x^3*cf.u^7*cf.r^8
    - 120*x*cf.u^9*cf.r^8 + 360*x^3*cf.u^6*cf.r^9 + 232*x*cf.u^8*cf.r^9 + 40*x^3*cf.u^5*cf.r^10
    + 124*x*cf.u^7*cf.r^10 - 56*x^3*cf.u^4*cf.r^11 - 8*x*cf.u^6*cf.r^11 - 8*x^3*cf.u^3*cf.r^12
    - 24*x*cf.u^5*cf.r^12 - 8*x*cf.u^4*cf.r^13 + 8*cf.u^17 + 28*cf.u^16*cf.r - 288*x^2*cf.u^13*cf.r^2
    + 12*cf.u^15*cf.r^2 - 368*x^2*cf.u^12*cf.r^3 - 78*cf.u^14*cf.r^3 + 728*x^2*cf.u^11*cf.r^4
    - 106*cf.u^13*cf.r^4 + 1464*x^2*cf.u^10*cf.r^5 + 56*cf.u^12*cf.r^5 + 504*x^2*cf.u^9*cf.r^6
    + 168*cf.u^11*cf.r^6 - 128*x^4*cf.u^6*cf.r^7 - 520*x^2*cf.u^8*cf.r^7 + 20*cf.u^10*cf.r^7
    - 192*x^4*cf.u^5*cf.r^8 - 472*x^2*cf.u^7*cf.r^8 - 108*cf.u^9*cf.r^8 - 32*x^4*cf.u^4*cf.r^9
    + 8*x^2*cf.u^6*cf.r^9 - 36*cf.u^8*cf.r^9 + 32*x^4*cf.u^3*cf.r^10 + 168*x^2*cf.u^5*cf.r^10
    + 28*cf.u^7*cf.r^10 + 56*x^2*cf.u^4*cf.r^11 + 10*cf.u^6*cf.r^11 - 2*cf.u^5*cf.r^12 + 32*x*cf.u^14*cf.r
    + 120*x*cf.u^13*cf.r^2 - 240*x*cf.u^12*cf.r^3 - 192*x^3*cf.u^9*cf.r^4 - 856*x*cf.u^11*cf.r^4
    + 256*x^3*cf.u^8*cf.r^5 - 296*x*cf.u^10*cf.r^5 + 800*x^3*cf.u^7*cf.r^6 + 616*x*cf.u^9*cf.r^6
    + 96*x^3*cf.u^6*cf.r^7 + 280*x*cf.u^8*cf.r^7 - 352*x^3*cf.u^5*cf.r^8 - 216*x*cf.u^7*cf.r^8
    - 96*x^3*cf.u^4*cf.r^9 - 104*x*cf.u^6*cf.r^9 + 16*x*cf.u^5*cf.r^10 + 8*x*cf.u^4*cf.r^11
    + 16*cf.u^14*cf.r + 448*x^2*cf.u^11*cf.r^2 + 56*cf.u^13*cf.r^2 + 32*x^2*cf.u^10*cf.r^3
    + 88*cf.u^12*cf.r^3 - 1152*x^2*cf.u^9*cf.r^4 + 40*cf.u^11*cf.r^4 - 608*x^2*cf.u^8*cf.r^5
    - 56*cf.u^10*cf.r^5 + 416*x^2*cf.u^7*cf.r^6 - 40*cf.u^9*cf.r^6 + 320*x^2*cf.u^6*cf.r^7
    + 24*cf.u^8*cf.r^7 - 32*x^2*cf.u^5*cf.r^8 + 8*cf.u^7*cf.r^8 - 64*x^2*cf.u^4*cf.r^9 - 8*cf.u^6*cf.r^9
    + 64*x*cf.u^12*cf.r + 96*x*cf.u^11*cf.r^2 + 288*x*cf.u^10*cf.r^3 + 224*x*cf.u^9*cf.r^4
    - 256*x^3*cf.u^6*cf.r^5 - 160*x*cf.u^8*cf.r^5 - 64*x*cf.u^7*cf.r^6 + 128*x^3*cf.u^4*cf.r^7
    + 64*x*cf.u^6*cf.r^7 - 32*cf.u^13 - 64*cf.u^12*cf.r - 256*x^2*cf.u^9*cf.r^2 + 256*x^2*cf.u^8*cf.r^3
    + 32*cf.u^10*cf.r^3 + 128*x^2*cf.u^7*cf.r^4 - 128*x^2*cf.u^6*cf.r^5 - 128*x*cf.u^10*cf.r) * hc
  · field_simp

theorem fabc_w_sub_singularAbc_not_singularAbc_u_eq_r {x y wx wy : ℂ}
    (hxy : (elliptic cf).Nonsingular x y) (hwxy : (elliptic cf).Nonsingular wx wy)
    (hpw : .some hxy ≠ w cf) (hpnw : .some hxy ≠ -w cf)
    (hwxyeq : w cf - .some hxy = .some hwxy)
    (hsxy : SingularAbc cf x y) (hwsxy : ¬ SingularAbc cf wx wy) (hur : cf.u = cf.r) :
    fabc cf (.some hwxy) = fabc cf (.some hxy) := by
  obtain _ := cf.hr
  obtain _ := cf.hu
  obtain hx := x_not_at_w cf hxy hpw hpnw
  have hk : cf.k ≠ 0 := hsxy.k_ne_zero cf hxy
  have : cf.r ^ 2 * x - cf.u ^ 2 ≠ 0 := by
    contrapose! hx
    field_simp
    linear_combination hx
  have : cf.u ^ 2 - cf.r ^ 2 * x ≠ 0 := by
    contrapose! this
    linear_combination -this
  rw [w_sub cf hxy hx, Point.some.injEq] at hwxyeq
  obtain ⟨hwx, hwy⟩ := hwxyeq
  have hur2 : cf.u + cf.r ≠ 0 := by
    rw [hur]
    simpa using cf.hr
  have hy : y = (cf.u - cf.r) * (cf.r * ((cf.u + cf.r) ^ 2 - 2) * x - cf.u * (cf.u + cf.r) ^ 2) /
      (-2 * cf.r ^ 2 * (cf.u + cf.r)) := by
    field_simp
    linear_combination -hsxy.xy_linear cf hxy
  have hy : y = 0 := by simpa [hur] using hy
  have hdeno : (cf.u ^ 2 - cf.r ^ 2) ^ 2 + cf.u ^ 2 * 4 ≠ 0 := by
    simpa [hur] using cf.hr
  obtain hc := hsxy.c_factor_eq_zero cf hxy
  simp_rw [hur] at hc
  suffices P2.mk (fabcNormal cf wx wy) _ =
      P2.mk ![2 * cf.u * cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2),
      (cf.r * (cf.u + cf.r) ^ 2 * x - cf.u * ((cf.u + cf.r) ^ 2 - 2)) * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 - 4 * cf.u ^ 2),
      8 * cf.u ^ 2 * cf.k * (cf.u ^ 2 - cf.r ^ 2)] _ by
    simpa [fabc, fabcRaw, hsxy, hwsxy]
  rw [P2.mk_eq_mk']
  use fabcNormal cf wx wy 0 / (2 * cf.u * cf.k * ((cf.u ^ 2 - cf.r ^ 2) ^ 2 + 4 * cf.u ^ 2))
  simp_rw [Matrix.smul_vec3, smul_eq_mul]
  rw [← hwx, ← hwy]
  unfold fabcNormal
  simp_rw [hy]
  simp only [Matrix.cons_val]
  congrm ![?_, ?_, ?_]
  · field_simp
  · field_simp
    rw [cf.k_sq]
    simp_rw [hur]
    linear_combination 16 * cf.r ^ 8 *
      (x^5*cf.r^4 - 11*x^4*cf.r^4 + 18*x^3*cf.r^4 + 4*x^4*cf.r^2 -
      6*x^2*cf.r^4 - 18*x^3*cf.r^2 - 3*x*cf.r^4 + 4*x^2*cf.r^2 + cf.r^4 + 4*x^3 + 2*x*cf.r^2) * hc
  · field_simp
    simp_rw [hur]
    linear_combination 16 * cf.r ^ 8 *
      (x^4*cf.r^2 - 4*x^3*cf.r^2 + 6*x^2*cf.r^2 + 2*x^3 - 4*x*cf.r^2 + cf.r^2 + 2*x) * hc
