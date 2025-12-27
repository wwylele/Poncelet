import Mathlib
import Poncelet.Elliptic

set_option linter.style.longLine false

open WeierstrassCurve.Affine

variable (cf : Config)

set_option maxHeartbeats 400000 in
-- Long Expression
theorem fabc_w_sub_c_eq_zero {x y wx wy : cf.K}
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
    unfold deno
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

theorem fabc_w_sub_c_ne_zero {x y wx wy : cf.K}
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

set_option maxHeartbeats 400000 in
-- Long Expression
theorem fabc_w_sub_singularAbc_not_singularAbc {x y wx wy : cf.K}
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

theorem fabc_w_sub_singularAbc_not_singularAbc_u_eq_r {x y wx wy : cf.K}
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

set_option maxHeartbeats 800000 in
-- Long Expression
theorem f_w_sub_singularAbc {x y : cf.K} (hxy : (elliptic cf).Nonsingular x y)
    (hsxy : SingularAbc cf x y) (hpw : Point.some hxy ≠ w cf)
    (hpnw : Point.some hxy ≠ -w cf) (hur : cf.u ^ 2 - cf.r ^ 2 ≠ 0)
    (habc : fabc cf (w cf - .some hxy) = fabc cf (.some hxy)) :
    f cf (w cf - .some hxy) = rPoint cf (f cf (.some hxy)) := by
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
  suffices fxyz cf (w cf - Point.some hxy) =
      P2.lift₂ (fun p q hp hq ↦ P2.mk' (rPoint' cf p q)) _
      (fxyz cf (Point.some hxy)) (fabc cf (Point.some hxy)) by
    simpa [f, rPoint, habc]
  have hk : cf.k ≠ 0 := hsxy.k_ne_zero cf hxy
  rw [w_sub cf hxy hx]
  simp only [fxyz, fxyzRaw, neg_mul, ne_eq, rPoint', Fin.isValue, neg_sub, fabc, fabcRaw, hsxy,
    ↓reduceIte, P2.lift₂_mk, Matrix.cons_val, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
    pow_eq_zero_iff, cf.hu, or_self, hk, hur, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_neg_eq_add]
  have huradd : cf.u + cf.r ≠ 0 := by
    contrapose! hur
    linear_combination (cf.u - cf.r) * hur
  obtain hy := hsxy.xy_linear cf hxy
  have hy : y = -(cf.u - cf.r) * (cf.r * ((cf.u + cf.r) ^ 2 - 2) * x - cf.u * (cf.u + cf.r) ^ 2) /
      (2 * cf.r ^ 2 * (cf.u + cf.r)) := by
    field_simp
    linear_combination -hy
  apply P2.mk_eq_mk'_of_l _ (
    (cf.u^3 * (cf.u + cf.r)^2 * (2* cf.u - cf.r) - 2*cf.u^3*cf.r *
      ((cf.u + cf.r)^2-2) * x + cf.u *cf.r^3 *(cf.u + cf.r)^2 * x^2)^2 /
    (64 * cf.k ^ 2 * cf.u ^4 * (cf.u + cf.r)^2 * (cf.r^2 * x - cf.u ^ 2)^4 *
    (cf.r * x + cf.u) ^ 2 * (cf.u ^ 2 - cf.r ^ 2) ^ 2))
  simp_rw [hy, Matrix.smul_vec3, smul_eq_mul]
  obtain hrxu := hsxy.rx_add_u_ne_zero cf hxy
  obtain hc := hsxy.c_factor_eq_zero cf hxy
  congrm ![?_, ?_, ?_]
  · field_simp
    rw [cf.k_sq]
    linear_combination -2 *
    (x^6*cf.u^14*cf.r^8 + 6*x^6*cf.u^13*cf.r^9 + 11*x^6*cf.u^12*cf.r^10
    - 4*x^6*cf.u^11*cf.r^11 - 39*x^6*cf.u^10*cf.r^12 - 38*x^6*cf.u^9*cf.r^13
    + 27*x^6*cf.u^8*cf.r^14 + 72*x^6*cf.u^7*cf.r^15 + 27*x^6*cf.u^6*cf.r^16
    - 38*x^6*cf.u^5*cf.r^17 - 39*x^6*cf.u^4*cf.r^18 - 4*x^6*cf.u^3*cf.r^19
    + 11*x^6*cf.u^2*cf.r^20 + 6*x^6*cf.u*cf.r^21 + x^6*cf.r^22 - 4*x^5*cf.u^16*cf.r^6
    - 22*x^5*cf.u^15*cf.r^7 - 32*x^5*cf.u^14*cf.r^8 + 38*x^5*cf.u^13*cf.r^9
    + 148*x^5*cf.u^12*cf.r^10 + 74*x^5*cf.u^11*cf.r^11 - 184*x^5*cf.u^10*cf.r^12
    - 234*x^5*cf.u^9*cf.r^13 + 36*x^5*cf.u^8*cf.r^14 + 206*x^5*cf.u^7*cf.r^15
    + 80*x^5*cf.u^6*cf.r^16 - 62*x^5*cf.u^5*cf.r^17 - 52*x^5*cf.u^4*cf.r^18
    - 2*x^5*cf.u^3*cf.r^19 + 8*x^5*cf.u^2*cf.r^20 + 2*x^5*cf.u*cf.r^21
    + 4*x^4*cf.u^18*cf.r^4 + 20*x^4*cf.u^17*cf.r^5 + 19*x^4*cf.u^16*cf.r^6
    - 66*x^4*cf.u^15*cf.r^7 - 8*x^6*cf.u^12*cf.r^8 - 151*x^4*cf.u^14*cf.r^8
    - 48*x^6*cf.u^11*cf.r^9 + 8*x^4*cf.u^13*cf.r^9 - 104*x^6*cf.u^10*cf.r^10
    + 299*x^4*cf.u^12*cf.r^10 - 64*x^6*cf.u^9*cf.r^11 + 218*x^4*cf.u^11*cf.r^11
    + 112*x^6*cf.u^8*cf.r^12 - 207*x^4*cf.u^10*cf.r^12 + 224*x^6*cf.u^7*cf.r^13
    - 332*x^4*cf.u^9*cf.r^13 + 112*x^6*cf.u^6*cf.r^14 - 31*x^4*cf.u^8*cf.r^14
    - 64*x^6*cf.u^5*cf.r^15 + 178*x^4*cf.u^7*cf.r^15 - 104*x^6*cf.u^4*cf.r^16
    + 99*x^4*cf.u^6*cf.r^16 - 48*x^6*cf.u^3*cf.r^17 - 16*x^4*cf.u^5*cf.r^17
    - 8*x^6*cf.u^2*cf.r^18 - 31*x^4*cf.u^4*cf.r^18 - 10*x^4*cf.u^3*cf.r^19
    - x^4*cf.u^2*cf.r^20 + 8*x^3*cf.u^18*cf.r^4 + 44*x^3*cf.u^17*cf.r^5
    + 40*x^5*cf.u^14*cf.r^6 + 64*x^3*cf.u^16*cf.r^6 + 208*x^5*cf.u^13*cf.r^7
    - 76*x^3*cf.u^15*cf.r^7 + 336*x^5*cf.u^12*cf.r^8 - 296*x^3*cf.u^14*cf.r^8
    - 48*x^5*cf.u^11*cf.r^9 - 148*x^3*cf.u^13*cf.r^9 - 712*x^5*cf.u^10*cf.r^10
    + 368*x^3*cf.u^12*cf.r^10 - 608*x^5*cf.u^9*cf.r^11 + 468*x^3*cf.u^11*cf.r^11
    + 224*x^5*cf.u^8*cf.r^12 - 72*x^3*cf.u^10*cf.r^12 + 544*x^5*cf.u^7*cf.r^13
    - 412*x^3*cf.u^9*cf.r^13 + 152*x^5*cf.u^6*cf.r^14 - 160*x^3*cf.u^8*cf.r^14
    - 112*x^5*cf.u^5*cf.r^15 + 124*x^3*cf.u^7*cf.r^15 - 48*x^5*cf.u^4*cf.r^16
    + 104*x^3*cf.u^6*cf.r^16 + 16*x^5*cf.u^3*cf.r^17 + 4*x^3*cf.u^5*cf.r^17
    + 8*x^5*cf.u^2*cf.r^18 - 16*x^3*cf.u^4*cf.r^18 - 4*x^3*cf.u^3*cf.r^19
    - 8*x^2*cf.u^20*cf.r^2 - 40*x^2*cf.u^19*cf.r^3 - 48*x^4*cf.u^16*cf.r^4
    - 41*x^2*cf.u^18*cf.r^4 - 208*x^4*cf.u^15*cf.r^5 + 114*x^2*cf.u^17*cf.r^5
    - 188*x^4*cf.u^14*cf.r^6 + 269*x^2*cf.u^16*cf.r^6 + 416*x^4*cf.u^13*cf.r^7
    - 4*x^2*cf.u^15*cf.r^7 + 16*x^6*cf.u^10*cf.r^8 + 880*x^4*cf.u^12*cf.r^8
    - 481*x^2*cf.u^14*cf.r^8 + 96*x^6*cf.u^9*cf.r^9 + 160*x^4*cf.u^11*cf.r^9
    - 322*x^2*cf.u^13*cf.r^9 + 240*x^6*cf.u^8*cf.r^10 - 812*x^4*cf.u^10*cf.r^10
    + 333*x^2*cf.u^12*cf.r^10 + 320*x^6*cf.u^7*cf.r^11 - 640*x^4*cf.u^9*cf.r^11
    + 448*x^2*cf.u^11*cf.r^11 + 240*x^6*cf.u^6*cf.r^12 + 16*x^4*cf.u^8*cf.r^12
    - 19*x^2*cf.u^10*cf.r^12 + 96*x^6*cf.u^5*cf.r^13 + 176*x^4*cf.u^7*cf.r^13
    - 242*x^2*cf.u^9*cf.r^13 + 16*x^6*cf.u^4*cf.r^14 + 108*x^4*cf.u^6*cf.r^14
    - 81*x^2*cf.u^8*cf.r^14 + 96*x^4*cf.u^5*cf.r^15 + 44*x^2*cf.u^7*cf.r^15
    + 48*x^4*cf.u^4*cf.r^16 + 29*x^2*cf.u^6*cf.r^16 + 2*x^2*cf.u^5*cf.r^17
    - 4*x^4*cf.u^2*cf.r^18 - x^2*cf.u^4*cf.r^18 - 4*x*cf.u^20*cf.r^2
    - 16*x^3*cf.u^17*cf.r^3 - 22*x*cf.u^19*cf.r^3 - 112*x^3*cf.u^16*cf.r^4
    - 32*x*cf.u^18*cf.r^4 - 336*x^3*cf.u^15*cf.r^5 + 38*x*cf.u^17*cf.r^5
    - 128*x^5*cf.u^12*cf.r^6 - 480*x^3*cf.u^14*cf.r^6 + 148*x*cf.u^16*cf.r^6
    - 608*x^5*cf.u^11*cf.r^7 - 48*x^3*cf.u^13*cf.r^7 + 74*x*cf.u^15*cf.r^7
    - 1024*x^5*cf.u^10*cf.r^8 + 944*x^3*cf.u^12*cf.r^8 - 184*x*cf.u^14*cf.r^8
    - 544*x^5*cf.u^9*cf.r^9 + 1296*x^3*cf.u^11*cf.r^9 - 234*x*cf.u^13*cf.r^9
    + 320*x^5*cf.u^8*cf.r^10 + 192*x^3*cf.u^10*cf.r^10 + 36*x*cf.u^12*cf.r^10
    + 352*x^5*cf.u^7*cf.r^11 - 1008*x^3*cf.u^9*cf.r^11 + 206*x*cf.u^11*cf.r^11
    - 128*x^5*cf.u^6*cf.r^12 - 784*x^3*cf.u^8*cf.r^12 + 80*x*cf.u^10*cf.r^12
    - 224*x^5*cf.u^5*cf.r^13 + 80*x^3*cf.u^7*cf.r^13 - 62*x*cf.u^9*cf.r^13
    - 64*x^5*cf.u^4*cf.r^14 + 288*x^3*cf.u^6*cf.r^14 - 52*x*cf.u^8*cf.r^14
    + 48*x^3*cf.u^5*cf.r^15 - 2*x*cf.u^7*cf.r^15 - 48*x^3*cf.u^4*cf.r^16
    + 8*x*cf.u^6*cf.r^16 - 16*x^3*cf.u^3*cf.r^17 + 2*x*cf.u^5*cf.r^17
    + 4*cf.u^22 + 20*cf.u^21*cf.r + 64*x^2*cf.u^18*cf.r^2 + 21*cf.u^20*cf.r^2
    + 352*x^2*cf.u^17*cf.r^3 - 54*cf.u^19*cf.r^3 + 208*x^4*cf.u^14*cf.r^4
    + 560*x^2*cf.u^16*cf.r^4 - 129*cf.u^18*cf.r^4 + 736*x^4*cf.u^13*cf.r^5
    - 304*x^2*cf.u^15*cf.r^5 + 500*x^4*cf.u^12*cf.r^6 - 1736*x^2*cf.u^14*cf.r^6
    + 221*cf.u^16*cf.r^6 - 984*x^4*cf.u^11*cf.r^7 - 1088*x^2*cf.u^13*cf.r^7
    + 142*cf.u^15*cf.r^7 - 1388*x^4*cf.u^10*cf.r^8 + 1448*x^2*cf.u^12*cf.r^8
    - 153*cf.u^14*cf.r^8 + 32*x^4*cf.u^9*cf.r^9 + 1888*x^2*cf.u^11*cf.r^9
    - 188*cf.u^13*cf.r^9 + 600*x^4*cf.u^8*cf.r^10 - 208*x^2*cf.u^10*cf.r^10
    + 23*cf.u^12*cf.r^10 - 112*x^4*cf.u^7*cf.r^11 - 1120*x^2*cf.u^9*cf.r^11
    + 102*cf.u^11*cf.r^11 - 344*x^4*cf.u^6*cf.r^12 - 192*x^2*cf.u^8*cf.r^12
    + 21*cf.u^10*cf.r^12 - 128*x^4*cf.u^5*cf.r^13 + 336*x^2*cf.u^7*cf.r^13
    - 24*cf.u^9*cf.r^13 - 76*x^4*cf.u^4*cf.r^14 + 88*x^2*cf.u^6*cf.r^14
    - 9*cf.u^8*cf.r^14 - 56*x^4*cf.u^3*cf.r^15 - 64*x^2*cf.u^5*cf.r^15
    + 2*cf.u^7*cf.r^15 - 12*x^4*cf.u^2*cf.r^16 - 24*x^2*cf.u^4*cf.r^16
    + cf.u^6*cf.r^16 - 16*x*cf.u^19*cf.r + 8*x*cf.u^18*cf.r^2 + 160*x^3*cf.u^15*cf.r^3
    + 288*x*cf.u^17*cf.r^3 + 720*x^3*cf.u^14*cf.r^4 + 528*x*cf.u^16*cf.r^4
    + 1312*x^3*cf.u^13*cf.r^5 - 192*x*cf.u^15*cf.r^5 + 128*x^5*cf.u^10*cf.r^6
    + 1424*x^3*cf.u^12*cf.r^6 - 1192*x*cf.u^14*cf.r^6 + 512*x^5*cf.u^9*cf.r^7
    + 1184*x^3*cf.u^11*cf.r^7 - 528*x*cf.u^13*cf.r^7 + 768*x^5*cf.u^8*cf.r^8
    + 288*x^3*cf.u^10*cf.r^8 + 864*x*cf.u^12*cf.r^8 + 512*x^5*cf.u^7*cf.r^9
    - 1152*x^3*cf.u^9*cf.r^9 + 624*x*cf.u^11*cf.r^9 + 128*x^5*cf.u^6*cf.r^10
    - 1376*x^3*cf.u^8*cf.r^10 - 328*x*cf.u^10*cf.r^10 - 96*x^3*cf.u^7*cf.r^11
    - 256*x*cf.u^9*cf.r^11 + 784*x^3*cf.u^6*cf.r^12 + 144*x*cf.u^8*cf.r^12
    + 608*x^3*cf.u^5*cf.r^13 + 96*x*cf.u^7*cf.r^13 + 208*x^3*cf.u^4*cf.r^14
    - 24*x*cf.u^6*cf.r^14 + 32*x^3*cf.u^3*cf.r^15 - 16*x*cf.u^5*cf.r^15
    - 48*cf.u^20 - 208*cf.u^19*cf.r - 224*x^2*cf.u^16*cf.r^2 - 204*cf.u^18*cf.r^2
    - 1328*x^2*cf.u^15*cf.r^3 + 320*cf.u^17*cf.r^3 - 384*x^4*cf.u^12*cf.r^4
    - 2808*x^2*cf.u^14*cf.r^4 + 672*cf.u^16*cf.r^4 - 1024*x^4*cf.u^11*cf.r^5
    - 1824*x^2*cf.u^13*cf.r^5 + 32*cf.u^15*cf.r^5 - 368*x^4*cf.u^10*cf.r^6
    + 2120*x^2*cf.u^12*cf.r^6 - 588*cf.u^14*cf.r^6 + 992*x^4*cf.u^9*cf.r^7
    + 4384*x^2*cf.u^11*cf.r^7 - 192*cf.u^13*cf.r^7 + 704*x^4*cf.u^8*cf.r^8
    + 2368*x^2*cf.u^10*cf.r^8 + 240*cf.u^12*cf.r^8 - 224*x^4*cf.u^7*cf.r^9
    - 800*x^2*cf.u^9*cf.r^9 + 48*cf.u^11*cf.r^9 - 288*x^4*cf.u^6*cf.r^10
    - 1984*x^2*cf.u^8*cf.r^10 - 100*cf.u^10*cf.r^10 - 224*x^4*cf.u^5*cf.r^11
    - 1200*x^2*cf.u^7*cf.r^11 - 192*x^4*cf.u^4*cf.r^12 - 72*x^2*cf.u^6*cf.r^12
    + 32*cf.u^8*cf.r^12 - 32*x^4*cf.u^3*cf.r^13 + 256*x^2*cf.u^5*cf.r^13
    + 16*x^4*cf.u^2*cf.r^14 + 88*x^2*cf.u^4*cf.r^14 - 4*cf.u^6*cf.r^14
    + 160*x*cf.u^17*cf.r + 560*x*cf.u^16*cf.r^2 - 512*x^3*cf.u^13*cf.r^3
    + 448*x*cf.u^15*cf.r^3 - 1696*x^3*cf.u^12*cf.r^4 - 784*x*cf.u^14*cf.r^4
    - 1680*x^3*cf.u^11*cf.r^5 - 2240*x*cf.u^13*cf.r^5 - 128*x^3*cf.u^10*cf.r^6
    - 2400*x*cf.u^12*cf.r^6 + 704*x^3*cf.u^9*cf.r^7 - 480*x*cf.u^11*cf.r^7
    + 832*x^3*cf.u^8*cf.r^8 + 1760*x*cf.u^10*cf.r^8 + 544*x^3*cf.u^7*cf.r^9
    + 1536*x*cf.u^9*cf.r^9 - 640*x^3*cf.u^6*cf.r^10 - 80*x*cf.u^8*cf.r^10
    - 1088*x^3*cf.u^5*cf.r^11 - 480*x*cf.u^7*cf.r^11 - 416*x^3*cf.u^4*cf.r^12
    - 80*x*cf.u^6*cf.r^12 - 16*x^3*cf.u^3*cf.r^13 + 32*x*cf.u^5*cf.r^13
    + 80*cf.u^18 + 208*cf.u^17*cf.r + 320*x^2*cf.u^14*cf.r^2 + 116*cf.u^16*cf.r^2
    + 1664*x^2*cf.u^13*cf.r^3 + 280*cf.u^15*cf.r^3 + 256*x^4*cf.u^10*cf.r^4
    + 2752*x^2*cf.u^12*cf.r^4 + 1012*cf.u^14*cf.r^4 + 512*x^4*cf.u^9*cf.r^5
    + 192*x^2*cf.u^11*cf.r^5 + 640*cf.u^13*cf.r^5 + 256*x^4*cf.u^8*cf.r^6
    - 3968*x^2*cf.u^10*cf.r^6 - 904*cf.u^12*cf.r^6 + 64*x^4*cf.u^7*cf.r^7
    - 3008*x^2*cf.u^9*cf.r^7 - 976*cf.u^11*cf.r^7 + 64*x^4*cf.u^6*cf.r^8
    + 1408*x^2*cf.u^8*cf.r^8 + 200*cf.u^10*cf.r^8 + 2368*x^2*cf.u^7*cf.r^9
    + 432*cf.u^9*cf.r^9 + 64*x^4*cf.u^4*cf.r^10 + 576*x^2*cf.u^6*cf.r^10
    + 20*cf.u^8*cf.r^10 + 64*x^4*cf.u^3*cf.r^11 - 192*x^2*cf.u^5*cf.r^11
    - 72*cf.u^7*cf.r^11 - 64*x^2*cf.u^4*cf.r^12 - 12*cf.u^6*cf.r^12 - 384*x*cf.u^15*cf.r
    - 928*x*cf.u^14*cf.r^2 + 512*x^3*cf.u^11*cf.r^3 + 368*x*cf.u^13*cf.r^3
    + 1152*x^3*cf.u^10*cf.r^4 + 2944*x*cf.u^12*cf.r^4 + 256*x^3*cf.u^9*cf.r^5
    + 2496*x*cf.u^11*cf.r^5 - 768*x^3*cf.u^8*cf.r^6 - 832*x*cf.u^10*cf.r^6
    - 512*x^3*cf.u^7*cf.r^7 - 2016*x*cf.u^9*cf.r^7 - 128*x^3*cf.u^6*cf.r^8
    - 384*x*cf.u^8*cf.r^8 + 256*x^3*cf.u^5*cf.r^9 + 576*x*cf.u^7*cf.r^9
    + 256*x^3*cf.u^4*cf.r^10 + 224*x*cf.u^6*cf.r^10 - 16*x*cf.u^5*cf.r^11
    - 64*cf.u^16 - 64*cf.u^15*cf.r - 192*x^2*cf.u^12*cf.r^2 - 112*cf.u^14*cf.r^2
    - 448*x^2*cf.u^11*cf.r^3 - 672*cf.u^13*cf.r^3 - 192*x^2*cf.u^10*cf.r^4
    - 704*cf.u^12*cf.r^4 + 704*x^2*cf.u^9*cf.r^5 + 288*cf.u^11*cf.r^5
    + 320*x^2*cf.u^8*cf.r^6 + 480*cf.u^10*cf.r^6 - 1088*x^2*cf.u^7*cf.r^7
    - 96*cf.u^9*cf.r^7 - 704*x^2*cf.u^6*cf.r^8 - 128*cf.u^8*cf.r^8
    + 64*x^2*cf.u^5*cf.r^9 + 32*cf.u^7*cf.r^9 + 16*cf.u^6*cf.r^10
    + 384*x*cf.u^13*cf.r + 512*x*cf.u^12*cf.r^2 - 896*x*cf.u^11*cf.r^3
    - 1408*x*cf.u^10*cf.r^4 + 256*x^3*cf.u^7*cf.r^5 + 128*x*cf.u^9*cf.r^5
    + 512*x*cf.u^8*cf.r^6 - 128*x*cf.u^7*cf.r^7 - 128*x*cf.u^6*cf.r^8
    + 64*cf.u^14 + 64*cf.u^13*cf.r + 256*x^2*cf.u^10*cf.r^2 + 64*cf.u^12*cf.r^2
    + 128*cf.u^11*cf.r^3 - 64*cf.u^9*cf.r^5 + 256*x^2*cf.u^6*cf.r^6 + 256*x*cf.u^9*cf.r^3) *hc
  · field_simp
    rw [cf.k_sq]
    linear_combination 4 * (cf.u + cf.r) *
    (x^5*cf.u^12*cf.r^7 + 4*x^5*cf.u^11*cf.r^8 + 2*x^5*cf.u^10*cf.r^9
    - 12*x^5*cf.u^9*cf.r^10 - 17*x^5*cf.u^8*cf.r^11 + 8*x^5*cf.u^7*cf.r^12
    + 28*x^5*cf.u^6*cf.r^13 + 8*x^5*cf.u^5*cf.r^14 - 17*x^5*cf.u^4*cf.r^15
    - 12*x^5*cf.u^3*cf.r^16 + 2*x^5*cf.u^2*cf.r^17 + 4*x^5*cf.u*cf.r^18
    + x^5*cf.r^19 - 4*x^4*cf.u^14*cf.r^5 - 13*x^4*cf.u^13*cf.r^6
    + 4*x^4*cf.u^12*cf.r^7 + 54*x^4*cf.u^11*cf.r^8 + 32*x^4*cf.u^10*cf.r^9
    - 83*x^4*cf.u^9*cf.r^10 - 88*x^4*cf.u^8*cf.r^11 + 52*x^4*cf.u^7*cf.r^12
    + 92*x^4*cf.u^6*cf.r^13 - 3*x^4*cf.u^5*cf.r^14 - 44*x^4*cf.u^4*cf.r^15
    - 10*x^4*cf.u^3*cf.r^16 + 8*x^4*cf.u^2*cf.r^17 + 3*x^4*cf.u*cf.r^18
    + 4*x^3*cf.u^16*cf.r^3 + 8*x^3*cf.u^15*cf.r^4 - 22*x^3*cf.u^14*cf.r^5
    - 56*x^3*cf.u^13*cf.r^6 - 4*x^5*cf.u^10*cf.r^7 + 32*x^3*cf.u^12*cf.r^7
    - 16*x^5*cf.u^9*cf.r^8 + 144*x^3*cf.u^11*cf.r^8 - 12*x^5*cf.u^8*cf.r^9
    + 14*x^3*cf.u^10*cf.r^9 + 32*x^5*cf.u^7*cf.r^10 - 176*x^3*cf.u^9*cf.r^10
    + 56*x^5*cf.u^6*cf.r^11 - 76*x^3*cf.u^8*cf.r^11 + 104*x^3*cf.u^7*cf.r^12
    - 56*x^5*cf.u^4*cf.r^13 + 70*x^3*cf.u^6*cf.r^13 - 32*x^5*cf.u^3*cf.r^14
    - 24*x^3*cf.u^5*cf.r^14 + 12*x^5*cf.u^2*cf.r^15 - 24*x^3*cf.u^4*cf.r^15
    + 16*x^5*cf.u*cf.r^16 + 4*x^5*cf.r^17 + 2*x^3*cf.u^2*cf.r^17 + 4*x^2*cf.u^17*cf.r^2
    + 16*x^2*cf.u^16*cf.r^3 + 6*x^2*cf.u^15*cf.r^4 + 24*x^4*cf.u^12*cf.r^5
    - 56*x^2*cf.u^14*cf.r^5 + 66*x^4*cf.u^11*cf.r^6 - 72*x^2*cf.u^13*cf.r^6
    - 28*x^4*cf.u^10*cf.r^7 + 56*x^2*cf.u^12*cf.r^7 - 222*x^4*cf.u^9*cf.r^8
    + 146*x^2*cf.u^11*cf.r^8 - 96*x^4*cf.u^8*cf.r^9 + 16*x^2*cf.u^10*cf.r^9
    + 260*x^4*cf.u^7*cf.r^10 - 124*x^2*cf.u^9*cf.r^10 + 216*x^4*cf.u^6*cf.r^11
    - 64*x^2*cf.u^8*cf.r^11 - 108*x^4*cf.u^5*cf.r^12 + 42*x^2*cf.u^7*cf.r^12
    - 152*x^4*cf.u^4*cf.r^13 + 40*x^2*cf.u^6*cf.r^13 - 6*x^4*cf.u^3*cf.r^14
    + 36*x^4*cf.u^2*cf.r^15 - 8*x^2*cf.u^4*cf.r^15 + 10*x^4*cf.u*cf.r^16
    - 2*x^2*cf.u^3*cf.r^16 - 4*x*cf.u^18*cf.r - 8*x*cf.u^17*cf.r^2
    - 32*x^3*cf.u^14*cf.r^3 + 21*x*cf.u^16*cf.r^3 - 32*x^3*cf.u^13*cf.r^4
    + 52*x*cf.u^15*cf.r^4 + 204*x^3*cf.u^12*cf.r^5 - 34*x*cf.u^14*cf.r^5
    + 296*x^3*cf.u^11*cf.r^6 - 132*x*cf.u^13*cf.r^6 - 308*x^3*cf.u^10*cf.r^7
    + 3*x*cf.u^12*cf.r^7 - 672*x^3*cf.u^9*cf.r^8 + 168*x*cf.u^11*cf.r^8
    - 16*x^5*cf.u^6*cf.r^9 + 24*x^3*cf.u^8*cf.r^9 + 48*x*cf.u^10*cf.r^9
    - 64*x^5*cf.u^5*cf.r^10 + 560*x^3*cf.u^7*cf.r^10 - 112*x*cf.u^9*cf.r^10
    - 96*x^5*cf.u^4*cf.r^11 + 216*x^3*cf.u^6*cf.r^11 - 53*x*cf.u^8*cf.r^11
    - 64*x^5*cf.u^3*cf.r^12 - 128*x^3*cf.u^5*cf.r^12 + 36*x*cf.u^7*cf.r^12
    - 16*x^5*cf.u^2*cf.r^13 - 100*x^3*cf.u^4*cf.r^13 + 22*x*cf.u^6*cf.r^13
    - 24*x^3*cf.u^3*cf.r^14 - 4*x*cf.u^5*cf.r^14 - 4*x^3*cf.u^2*cf.r^15
    - 3*x*cf.u^4*cf.r^15 - 4*cf.u^19 - 12*cf.u^18*cf.r - 56*x^2*cf.u^15*cf.r^2
    + 7*cf.u^17*cf.r^2 - 176*x^2*cf.u^14*cf.r^3 + 52*cf.u^16*cf.r^3
    - 80*x^2*cf.u^13*cf.r^4 + 18*cf.u^15*cf.r^4 - 32*x^4*cf.u^10*cf.r^5
    + 288*x^2*cf.u^12*cf.r^5 - 88*cf.u^14*cf.r^5 - 56*x^4*cf.u^9*cf.r^6
    + 424*x^2*cf.u^11*cf.r^6 - 63*cf.u^13*cf.r^6 + 112*x^4*cf.u^8*cf.r^7
    + 160*x^2*cf.u^10*cf.r^7 + 72*cf.u^12*cf.r^7 + 320*x^4*cf.u^7*cf.r^8
    - 224*x^2*cf.u^9*cf.r^8 + 72*cf.u^11*cf.r^8 + 176*x^4*cf.u^6*cf.r^9
    - 448*x^2*cf.u^8*cf.r^9 - 28*cf.u^10*cf.r^9 - 96*x^4*cf.u^5*cf.r^10
    - 232*x^2*cf.u^7*cf.r^10 - 39*cf.u^9*cf.r^10 - 112*x^4*cf.u^4*cf.r^11
    + 144*x^2*cf.u^6*cf.r^11 + 4*cf.u^8*cf.r^11 - 32*x^4*cf.u^3*cf.r^12
    + 176*x^2*cf.u^5*cf.r^12 + 10*cf.u^7*cf.r^12 - 16*x^4*cf.u^2*cf.r^13
    + 32*x^2*cf.u^4*cf.r^13 - 8*x^4*cf.u*cf.r^14 - 8*x^2*cf.u^3*cf.r^14
    - cf.u^5*cf.r^14 + 48*x*cf.u^16*cf.r + 224*x*cf.u^15*cf.r^2
    + 80*x^3*cf.u^12*cf.r^3 + 216*x*cf.u^14*cf.r^3 - 16*x^3*cf.u^11*cf.r^4
    - 472*x*cf.u^13*cf.r^4 - 520*x^3*cf.u^10*cf.r^5 - 976*x*cf.u^12*cf.r^5
    - 256*x^3*cf.u^9*cf.r^6 + 864*x^3*cf.u^8*cf.r^7 + 1136*x*cf.u^10*cf.r^7
    + 736*x^3*cf.u^7*cf.r^8 + 592*x*cf.u^9*cf.r^8 - 240*x^3*cf.u^6*cf.r^9
    - 432*x*cf.u^8*cf.r^9 - 256*x^3*cf.u^5*cf.r^10 - 416*x*cf.u^7*cf.r^10
    + 80*x^3*cf.u^4*cf.r^11 - 8*x*cf.u^6*cf.r^11 + 48*x^3*cf.u^3*cf.r^12
    + 72*x*cf.u^5*cf.r^12 - 8*x^3*cf.u^2*cf.r^13 + 16*x*cf.u^4*cf.r^13
    - 56*cf.u^17 - 168*cf.u^16*cf.r + 240*x^2*cf.u^13*cf.r^2 + 46*cf.u^15*cf.r^2
    + 448*x^2*cf.u^12*cf.r^3 + 572*cf.u^14*cf.r^3 - 480*x^2*cf.u^11*cf.r^4
    + 294*cf.u^13*cf.r^4 - 1504*x^2*cf.u^10*cf.r^5 - 704*cf.u^12*cf.r^5
    - 544*x^2*cf.u^9*cf.r^6 - 612*cf.u^11*cf.r^6 - 96*x^4*cf.u^6*cf.r^7
    + 928*x^2*cf.u^8*cf.r^7 + 360*cf.u^10*cf.r^7 - 224*x^4*cf.u^5*cf.r^8
    + 800*x^2*cf.u^7*cf.r^8 + 452*cf.u^9*cf.r^8 - 128*x^4*cf.u^4*cf.r^9
    - 32*x^2*cf.u^6*cf.r^9 - 56*cf.u^8*cf.r^9 + 32*x^4*cf.u^3*cf.r^10
    - 272*x^2*cf.u^5*cf.r^10 - 138*cf.u^7*cf.r^10 + 32*x^4*cf.u^2*cf.r^11
    - 96*x^2*cf.u^4*cf.r^11 - 4*cf.u^6*cf.r^11 + 14*cf.u^5*cf.r^12
    - 144*x*cf.u^14*cf.r - 208*x*cf.u^13*cf.r^2 - 64*x^3*cf.u^10*cf.r^3
    + 632*x*cf.u^12*cf.r^3 + 64*x^3*cf.u^9*cf.r^4 + 1024*x*cf.u^11*cf.r^4
    + 320*x^3*cf.u^8*cf.r^5 - 784*x*cf.u^10*cf.r^5 - 128*x^3*cf.u^7*cf.r^6
    - 1632*x*cf.u^9*cf.r^6 - 512*x^3*cf.u^6*cf.r^7 + 112*x*cf.u^8*cf.r^7
    - 64*x^3*cf.u^5*cf.r^8 + 832*x*cf.u^7*cf.r^8 + 128*x^3*cf.u^4*cf.r^9
    + 64*x*cf.u^6*cf.r^9 - 144*x*cf.u^5*cf.r^10 - 8*x*cf.u^4*cf.r^11
    + 80*cf.u^15 + 128*cf.u^14*cf.r - 352*x^2*cf.u^11*cf.r^2 - 120*cf.u^13*cf.r^2
    - 32*x^2*cf.u^10*cf.r^3 - 144*cf.u^12*cf.r^3 + 1184*x^2*cf.u^9*cf.r^4
    + 288*cf.u^11*cf.r^4 + 352*x^2*cf.u^8*cf.r^5 + 240*cf.u^10*cf.r^5
    - 928*x^2*cf.u^7*cf.r^6 - 160*cf.u^9*cf.r^6 - 96*x^2*cf.u^6*cf.r^7
    - 112*cf.u^8*cf.r^7 + 352*x^2*cf.u^5*cf.r^8 + 48*cf.u^7*cf.r^8
    + 32*x^2*cf.u^4*cf.r^9 + 16*cf.u^6*cf.r^9 - 8*cf.u^5*cf.r^10
    + 64*x*cf.u^12*cf.r - 128*x*cf.u^11*cf.r^2 - 320*x*cf.u^10*cf.r^3
    + 320*x*cf.u^9*cf.r^4 - 128*x^3*cf.u^6*cf.r^5 + 512*x*cf.u^8*cf.r^5
    - 128*x*cf.u^7*cf.r^6 - 128*x*cf.u^6*cf.r^7 + 64*x*cf.u^5*cf.r^8
    - 32*cf.u^13 - 32*cf.u^12*cf.r + 128*x^2*cf.u^9*cf.r^2 - 32*cf.u^11*cf.r^2
    - 256*x^2*cf.u^8*cf.r^3 - 64*cf.u^10*cf.r^3 - 256*x^2*cf.u^7*cf.r^4
    + 256*x^2*cf.u^6*cf.r^5 + 32*cf.u^8*cf.r^5 - 128*x^2*cf.u^5*cf.r^6 - 128*x*cf.u^8*cf.r^3) * hc
  · field

theorem f_w_sub_not_singularAbc_p2 {x y : cf.K} (hxy : (elliptic cf).Nonsingular x y)
    (hpw : .some hxy ≠ w cf) (hpnw : .some hxy ≠ -w cf)
    (hsxy : ¬ SingularAbc cf x y) (hp2 : fabcNormal cf x y 2 = 0)
    (huxr : cf.r * x + cf.u ≠ 0) (habc : fabc cf (w cf - .some hxy) = fabc cf (.some hxy)):
    f cf (w cf - (.some hxy)) = rPoint cf (f cf (.some hxy)) := by
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
  suffices fxyz cf (w cf - Point.some hxy) =
      P2.lift₂ (fun p q hp hq ↦ P2.mk' (rPoint' cf p q)) _
      (fxyz cf (Point.some hxy)) (fabc cf (Point.some hxy)) by
    simpa [f, rPoint, habc]
  have huxr2 : (cf.r * x - cf.u) ^ 2 * (cf.u + cf.r) ^ 2 + 4 * cf.u * cf.r * x = 0 := by
    simpa [fabcNormal, huxr] using hp2
  obtain ⟨heq, hnonsingular⟩ := (nonsingular_elliptic cf _ _).mp hxy
  have hur0 : cf.u + cf.r ≠ 0 := by
    contrapose! hsxy with hur0
    have hx0 : x = 0 := by simpa [hur0, cf.hr, cf.hu] using huxr2
    have hy0 : y = 0 := by simpa [cf.hr, hx0] using heq
    apply SingularAbc.mk cf hxy
    · simp [hx0, hur0, hy0]
    · linear_combination (cf.r * x + cf.u) * huxr2
  have hy : (2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u) * y) ^ 2 =
      ((cf.r * x + cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
      2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2)) ^ 2 := by
    trans (2 * cf.r * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u)) ^ 2 *
      (x * (cf.r ^ 2 * x ^ 2 + (1 - cf.u ^ 2 - cf.r ^ 2) * x + cf.u ^ 2))
    · rw [← heq]
      ring
    linear_combination huxr2 *
      (4*x^3*cf.u^2*cf.r^4 + 8*x^3*cf.u*cf.r^5 + 4*x^3*cf.r^6 - 4*x^2*cf.u^4*cf.r^2
      - 8*x^2*cf.u^3*cf.r^3 - x^4*cf.r^4 - 8*x^2*cf.u^2*cf.r^4 - 8*x^2*cf.u*cf.r^5
      - 4*x^2*cf.r^6 + 4*x*cf.u^4*cf.r^2 - 4*x^3*cf.u*cf.r^3 + 8*x*cf.u^3*cf.r^3
      - 4*x^3*cf.r^4 + 4*x*cf.u^2*cf.r^4 + 2*x^2*cf.u^2*cf.r^2 + 8*x^2*cf.u*cf.r^3
      + 8*x^2*cf.r^4 - 4*x*cf.u^3*cf.r - 4*x*cf.u^2*cf.r^2 - cf.u^4 - 4*x^2*cf.r^2)
  obtain hy | hy : _ ∨ _ := eq_or_eq_neg_of_sq_eq_sq _ _ hy
  · absurd hsxy
    apply SingularAbc.mk cf hxy
    · linear_combination -hy
    · linear_combination (cf.r * x + cf.u) * huxr2
  have hur1 : (cf.u + cf.r) ^ 2 - 1 ≠ 0 := by
    by_contra! hur1
    have hx: cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
        2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2 = 0 := by
      simpa [hur1, huxr] using hy
    contrapose! huxr with huxr
    have hur1 : (cf.u + cf.r) ^ 2 = 1 ^ 2 := by linear_combination hur1
    obtain hur1 | hur1 := eq_or_eq_neg_of_sq_eq_sq _ _ hur1
    · have hr : cf.r = 1 - cf.u := by linear_combination hur1
      rw [hr] at ⊢ hx
      rw [← sq_eq_zero_iff]
      linear_combination hx
    · have hr : cf.r = -1 - cf.u := by linear_combination hur1
      rw [hr] at ⊢ hx
      rw [← sq_eq_zero_iff]
      linear_combination -hx
  have hk : cf.k ≠ 0 := by
    rw [← sq_eq_zero_iff.ne, cf.k_sq]
    exact hur1
  have hrxmu : cf.r * x - cf.u ≠ 0 := by
    by_contra! hrxmu
    have : x = 0 := by simpa [hrxmu, cf.hr, cf.hu] using huxr2
    simp [this, cf.hu] at hrxmu
  have hy : y = -(cf.r * x + cf.u) * (cf.r ^ 2 * (cf.u + cf.r) * x ^ 2 +
      2 * cf.r * (1 - cf.r * (cf.u + cf.r)) * x + (cf.u + cf.r) * cf.u ^ 2) /
      (2 * cf.r ^ 2 * ((cf.u + cf.r) ^ 2 - 1) * (cf.r * x - cf.u)) := by
    field_simp
    linear_combination hy

  simp only [fxyz, fxyzRaw, w_sub cf hxy hx, neg_mul, ne_eq, rPoint', Fin.isValue, neg_sub, fabc,
    fabcRaw, hsxy, ↓reduceIte, P2.lift₂_mk, hp2, Matrix.cons_val, OfNat.ofNat_ne_zero,
    not_false_eq_true, pow_eq_zero_iff, huxr]
  simp only [fabcNormal, neg_mul, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
    neg_add_rev, neg_neg]
  refine P2.mk'_eq_mk'_of_third_zero _ ?_ ?_ ?_ ?_
  · simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    contrapose! hsxy with h1
    apply SingularAbc.mk cf hxy
    · linear_combination -h1
    · linear_combination (cf.r * x + cf.u) * huxr2
  · simp only [Fin.isValue, Matrix.cons_val, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff]
    simp_rw [hy]
    field_simp
    linear_combination cf.u * (x*cf.u*cf.r^2 + x*cf.r^3 - cf.u^3 - cf.u^2*cf.r - x*cf.r) *  huxr2
  · simp
  · simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp_rw [hy]
    field_simp
    rw [cf.k_sq]
    linear_combination - huxr2 *
    (x^2*cf.u*cf.r^2 + x^2*cf.r^3 - 2*x*cf.u*cf.r^2 - 2*x*cf.r^3 + cf.u^3
      + cf.u^2*cf.r + 2*x*cf.r) * (x^5*cf.u^5*cf.r^7 + 5*x^5*cf.u^4*cf.r^8
      + 10*x^5*cf.u^3*cf.r^9 + 10*x^5*cf.u^2*cf.r^10 + 5*x^5*cf.u*cf.r^11
      + x^5*cf.r^12 - 2*x^4*cf.u^7*cf.r^5 - 5*x^4*cf.u^6*cf.r^6 - 5*x^4*cf.u^5*cf.r^7
      - 12*x^4*cf.u^4*cf.r^8 - 28*x^4*cf.u^3*cf.r^9 - 29*x^4*cf.u^2*cf.r^10
      - 13*x^4*cf.u*cf.r^11 - 2*x^4*cf.r^12 + x^3*cf.u^9*cf.r^3 - 5*x^3*cf.u^8*cf.r^4
      - 23*x^3*cf.u^7*cf.r^5 - 4*x^5*cf.u^4*cf.r^6 - 23*x^3*cf.u^6*cf.r^6
      - 11*x^5*cf.u^3*cf.r^7 + 9*x^3*cf.u^5*cf.r^7 - 11*x^5*cf.u^2*cf.r^8
      + 37*x^3*cf.u^4*cf.r^8 - 5*x^5*cf.u*cf.r^9 + 39*x^3*cf.u^3*cf.r^9
      - x^5*cf.r^10 + 23*x^3*cf.u^2*cf.r^10 + 6*x^3*cf.u*cf.r^11 + 5*x^2*cf.u^10*cf.r^2
      + 21*x^2*cf.u^9*cf.r^3 + 4*x^4*cf.u^6*cf.r^4 + 43*x^2*cf.u^8*cf.r^4
      + 6*x^4*cf.u^5*cf.r^5 + 51*x^2*cf.u^7*cf.r^5 - 3*x^4*cf.u^4*cf.r^6
      + 19*x^2*cf.u^6*cf.r^6 + 5*x^4*cf.u^3*cf.r^7 - 29*x^2*cf.u^5*cf.r^7
      + 27*x^4*cf.u^2*cf.r^8 - 35*x^2*cf.u^4*cf.r^8 + 21*x^4*cf.u*cf.r^9
      - 11*x^2*cf.u^3*cf.r^9 + 4*x^4*cf.r^10 - 3*x*cf.u^11*cf.r - 19*x*cf.u^10*cf.r^2
      + 5*x^3*cf.u^7*cf.r^3 - 42*x*cf.u^9*cf.r^3 + 27*x^3*cf.u^6*cf.r^4
      - 38*x*cf.u^8*cf.r^4 + 2*x^5*cf.u^3*cf.r^5 + 40*x^3*cf.u^5*cf.r^5
      - 7*x*cf.u^7*cf.r^5 + 6*x^5*cf.u^2*cf.r^6 + 16*x^3*cf.u^4*cf.r^6
      + 9*x*cf.u^6*cf.r^6 + 2*x^5*cf.u*cf.r^7 - 25*x^3*cf.u^3*cf.r^7
      + 4*x*cf.u^5*cf.r^7 - 43*x^3*cf.u^2*cf.r^8 - 20*x^3*cf.u*cf.r^9
      + cf.u^12 + 5*cf.u^11*cf.r - 13*x^2*cf.u^8*cf.r^2 + 10*cf.u^10*cf.r^2
      - 51*x^2*cf.u^7*cf.r^3 + 10*cf.u^9*cf.r^3 - 2*x^4*cf.u^4*cf.r^4
      - 72*x^2*cf.u^6*cf.r^4 + 5*cf.u^8*cf.r^4 - 2*x^4*cf.u^3*cf.r^5
      - 12*x^2*cf.u^5*cf.r^5 + cf.u^7*cf.r^5 - 8*x^4*cf.u^2*cf.r^6
      + 53*x^2*cf.u^4*cf.r^6 - 8*x^4*cf.u*cf.r^7 + 31*x^2*cf.u^3*cf.r^7
      - 2*x^4*cf.r^8 + 11*x*cf.u^9*cf.r + 29*x*cf.u^8*cf.r^2 - 2*x^3*cf.u^5*cf.r^3
      + 15*x*cf.u^7*cf.r^3 - 28*x^3*cf.u^4*cf.r^4 - 13*x*cf.u^6*cf.r^4
      - 32*x^3*cf.u^3*cf.r^5 - 10*x*cf.u^5*cf.r^5 + 12*x^3*cf.u^2*cf.r^6
      + 22*x^3*cf.u*cf.r^7 + cf.u^10 + cf.u^9*cf.r + 28*x^2*cf.u^6*cf.r^2
      - cf.u^8*cf.r^2 + 36*x^2*cf.u^5*cf.r^3 - cf.u^7*cf.r^3 + 8*x^4*cf.u^2*cf.r^4
      - 16*x^2*cf.u^4*cf.r^4 - 28*x^2*cf.u^3*cf.r^5 + 2*x*cf.u^7*cf.r
      + 10*x*cf.u^6*cf.r^2 + 16*x^3*cf.u^3*cf.r^3 + 6*x*cf.u^5*cf.r^3
      + 8*x^3*cf.u^2*cf.r^4 - 8*x^3*cf.u*cf.r^5 + 2*cf.u^7*cf.r + 8*x^2*cf.u^3*cf.r^3)
