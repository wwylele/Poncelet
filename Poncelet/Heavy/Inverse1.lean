import Mathlib
import Poncelet.Grobner

namespace Detail
open CPoly

scoped notation "x" => (X 0 : CPoly 0 9)
scoped notation "y" => (X 1 : CPoly 0 9)
scoped notation "z" => (X 2 : CPoly 0 9)
scoped notation "a" => (X 3 : CPoly 0 9)
scoped notation "b" => (X 4 : CPoly 0 9)
scoped notation "c" => (X 5 : CPoly 0 9)
scoped notation "u" => (X 6 : CPoly 0 9)
scoped notation "r" => (X 7 : CPoly 0 9)
scoped notation "k" => (X 8 : CPoly 0 9)

def target : CPoly 0 9 := (r *
          ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
            (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                    (r * (u + r) - 2) * k * a * c +
                  (2 - (u + r) * (u + 2 * r)) * b * c -
                u * k * c ^ 2) *
              z) +
        r * ((u + r) * a - c) * ((u + r) * b + k * c) * z * u) ^
      4 *
    y ^ 2 -(
  r ^ 2 * 2 ^ 2 * k ^ 2 * z ^ 2 *
    (r ^ 2 *
          (((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                        (r * (u + r) - 2) * k * a * c +
                      (2 - (u + r) * (u + 2 * r)) * b * c -
                    u * k * c ^ 2) *
                  z) ^
              3 *
            (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z)) +
        (1 - u ^ 2 - r ^ 2) *
          (((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                        (r * (u + r) - 2) * k * a * c +
                      (2 - (u + r) * (u + 2 * r)) * b * c -
                    u * k * c ^ 2) *
                  z) ^
              2 *
            (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z) ^ 2) +
      u ^ 2 *
          ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
            (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                    (r * (u + r) - 2) * k * a * c +
                  (2 - (u + r) * (u + 2 * r)) * b * c -
                u * k * c ^ 2) *
              z) *
        (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z) ^ 3))

def basis : List (CPoly 0 9) := [
  x^2 - 2*x*z*u + y^2 - 2*z^2*u*r - 2*z^2*r^2 + z^2*k^2 + z^2,
  x*y*b - x*z*c - y^2*a - 2*y*z*b*u + 2*z^2*a*u*r + 2*z^2*a*r^2 - z^2*a*k^2 - z^2*a + 2*z^2*c*u,
 x*y*c^2 - x*z*b*c - y*z*a*c - 2*y*z*b^2*u + 2*z^2*a*b*u*r + 2*z^2*a*b*r^2 - z^2*a*b*k^2 - z^2*a*b + 2*z^2*b*c*u,
 x*a + y*b - z*c,
 x*b^2 - x*c^2 - y*a*b + z*a*c,
 y^2*c^2 + 2*y*z*a*b*u - 2*y*z*b*c - 2*z^2*a*c*u + 2*z^2*b^2*u*r + 2*z^2*b^2*r^2 - z^2*b^2*k^2 - z^2*b^2 - 2*z^2*c^2*u*r - 2*z^2*c^2*r^2 + z^2*c^2*k^2 + 2*z^2*c^2,
 a^2 + b^2 - c^2,
 u^2 + 2*u*r + r^2 - k^2 - 1
]

end Detail


theorem inverse1 {K : Type*} [Field K] [CharZero K] (x y z a b c u r k : K)
    (ho : (x - u * z) ^ 2 + y ^ 2 = r ^ 2 * z ^ 2)
    (hi : a ^ 2 + b ^ 2 = c ^ 2)
    (hpq : x * a + y * b = z * c)
    (hk : k ^ 2 = (u + r) ^ 2 - 1) :
    (r *
          ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
            (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                    (r * (u + r) - 2) * k * a * c +
                  (2 - (u + r) * (u + 2 * r)) * b * c -
                u * k * c ^ 2) *
              z) +
        r * ((u + r) * a - c) * ((u + r) * b + k * c) * z * u) ^
      4 *
    y ^ 2 =
  r ^ 2 * 2 ^ 2 * k ^ 2 * z ^ 2 *
    (r ^ 2 *
          (((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                        (r * (u + r) - 2) * k * a * c +
                      (2 - (u + r) * (u + 2 * r)) * b * c -
                    u * k * c ^ 2) *
                  z) ^
              3 *
            (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z)) +
        (1 - u ^ 2 - r ^ 2) *
          (((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                        (r * (u + r) - 2) * k * a * c +
                      (2 - (u + r) * (u + 2 * r)) * b * c -
                    u * k * c ^ 2) *
                  z) ^
              2 *
            (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z) ^ 2) +
      u ^ 2 *
          ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
            (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                    (r * (u + r) - 2) * k * a * c +
                  (2 - (u + r) * (u + 2 * r)) * b * c -
                u * k * c ^ 2) *
              z) *
        (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z) ^ 3) := by
  rw [← sub_eq_zero]

  have hbasis : Detail.basis.Forall (·.eval ![x,y,z,a,b,c,u,r,k] = 0) := by
    rw [List.forall_iff_forall_mem]
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
    fin_cases i
    all_goals
    · simp [Detail.basis]
      grind

  suffices Detail.target.eval ![x,y,z,a,b,c,u,r,k] = 0 by
    simpa [Detail.target]
  apply CPoly.eq_zero_of_reduceRepeat_eq_zero hbasis (fuel := 15000)
  suffices CPoly.reduceRepeat Detail.target Detail.basis 15000 = 0 by simp [this]
  native_decide
