import Mathlib
import Poncelet.Heavy.Basis1

namespace Detail
open CPoly

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
  suffices Detail.target.eval ![x,y,z,a,b,c,u,r,k] = 0 by
    simpa [Detail.target]
  apply CPoly.eq_zero_of_reduceRepeat_eq_zero
    (forall_basis1 x y z a b c u r k ho hi hpq hk) 15000
  suffices CPoly.reduceRepeat Detail.target Detail.basis1 15000 = 0 by simp [this]
  native_decide
