import Mathlib
import Poncelet.Heavy.Basis1

namespace Detail
open CPoly

def target4 : CPoly 0 9 := -((-((r *
                  ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                    (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                            (r * (u + r) - 2) * k * a * c +
                          (2 - (u + r) * (u + 2 * r)) * b * c -
                        u * k * c ^ 2) *
                      z) +
                r * ((u + r) * a - c) * ((u + r) * b + k * c)
                * z * u) ^
              3 *
            y) +
        k * z *
            (r *
                ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                  (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                          (r * (u + r) - 2) * k * a * c +
                        (2 - (u + r) * (u + 2 * r)) * b * c -
                      u * k * c ^ 2) *
                    z) -
              r * ((u + r) * a - c) * ((u + r) * b + k * c)
              * z * u) *
          (r *
                ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                  (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                          (r * (u + r) - 2) * k * a * c +
                        (2 - (u + r) * (u + 2 * r)) * b * c -
                      u * k * c ^ 2) *
                    z) *
              (r *
                    ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                      (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                              (r * (u + r) - 2) * k * a * c +
                            (2 - (u + r) * (u + 2 * r)) * b * c -
                          u * k * c ^ 2) *
                        z) *
                  (u + r) +
                2 * (r * ((u + r) * a - c) * ((u + r) * b + k
                * c) * z) *
                  (1 - r * (u + r))) +
            (r * ((u + r) * a - c) * ((u + r) * b + k * c)
            * z) ^ 2 * u ^ 2 *
              (u + r))) *
      c) -(
  (r *
            ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
              (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                      (r * (u + r) - 2) * k * a * c +
                    (2 - (u + r) * (u + 2 * r)) * b * c -
                  u * k * c ^ 2) *
                z) +
          r * ((u + r) * a - c) * ((u + r) * b + k * c) * z * u) *
        z *
      ((r *
                ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                  (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                          (r * (u + r) - 2) * k * a * c +
                        (2 - (u + r) * (u + 2 * r)) * b * c -
                      u * k * c ^ 2) *
                    z) -
              r * ((u + r) * a - c) * ((u + r) * b + k * c)
              * z * u) ^
            2 *
          (u + r) ^ 2 +
        r *
                ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                  (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                          (r * (u + r) - 2) * k * a * c +
                        (2 - (u + r) * (u + 2 * r)) * b * c -
                      u * k * c ^ 2) *
                    z) *
              (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z) *
            u *
          4) *
    b)

end Detail


theorem inverse4 {K : Type*} [Field K] [CharZero K] (x y z a b c u r k : K)
    (ho : (x - u * z) ^ 2 + y ^ 2 = r ^ 2 * z ^ 2)
    (hi : a ^ 2 + b ^ 2 = c ^ 2)
    (hpq : x * a + y * b = z * c)
    (hk : k ^ 2 = (u + r) ^ 2 - 1) :
    -((-((r *
                  ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                    (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                            (r * (u + r) - 2) * k * a * c +
                          (2 - (u + r) * (u + 2 * r)) * b * c -
                        u * k * c ^ 2) *
                      z) +
                r * ((u + r) * a - c) * ((u + r) * b + k * c)
                * z * u) ^
              3 *
            y) +
        k * z *
            (r *
                ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                  (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                          (r * (u + r) - 2) * k * a * c +
                        (2 - (u + r) * (u + 2 * r)) * b * c -
                      u * k * c ^ 2) *
                    z) -
              r * ((u + r) * a - c) * ((u + r) * b + k * c)
              * z * u) *
          (r *
                ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                  (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                          (r * (u + r) - 2) * k * a * c +
                        (2 - (u + r) * (u + 2 * r)) * b * c -
                      u * k * c ^ 2) *
                    z) *
              (r *
                    ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                      (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                              (r * (u + r) - 2) * k * a * c +
                            (2 - (u + r) * (u + 2 * r)) * b * c -
                          u * k * c ^ 2) *
                        z) *
                  (u + r) +
                2 * (r * ((u + r) * a - c) * ((u + r) * b + k
                * c) * z) *
                  (1 - r * (u + r))) +
            (r * ((u + r) * a - c) * ((u + r) * b + k * c)
            * z) ^ 2 * u ^ 2 *
              (u + r))) *
      c) =
  (r *
            ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
              (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                      (r * (u + r) - 2) * k * a * c +
                    (2 - (u + r) * (u + 2 * r)) * b * c -
                  u * k * c ^ 2) *
                z) +
          r * ((u + r) * a - c) * ((u + r) * b + k * c) * z * u) *
        z *
      ((r *
                ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                  (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                          (r * (u + r) - 2) * k * a * c +
                        (2 - (u + r) * (u + 2 * r)) * b * c -
                      u * k * c ^ 2) *
                    z) -
              r * ((u + r) * a - c) * ((u + r) * b + k * c)
              * z * u) ^
            2 *
          (u + r) ^ 2 +
        r *
                ((k * x + ((u + r) ^ 2 - 1) * y) * c ^ 2 +
                  (2 * u * k * a ^ 2 + u * ((u + r) ^ 2 - 2) * a * b +
                          (r * (u + r) - 2) * k * a * c +
                        (2 - (u + r) * (u + 2 * r)) * b * c -
                      u * k * c ^ 2) *
                    z) *
              (r * ((u + r) * a - c) * ((u + r) * b + k * c) * z) *
            u *
          4) *
    b := by
  rw [← sub_eq_zero]
  suffices Detail.target4.eval ![x,y,z,a,b,c,u,r,k] = 0 by
    simpa [Detail.target4]
  apply CPoly.eq_zero_of_reduceRepeat_eq_zero
    (forall_basis1 x y z a b c u r k ho hi hpq hk) 6000
  suffices CPoly.reduceRepeat Detail.target4 Detail.basis1 6000 = 0 by simp [this]
  native_decide
