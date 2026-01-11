import Poncelet.Inverse
import Poncelet.Transfer

variable {K : Type*} [Field K]
variable (cf : Config K)

theorem iterate_next_eq_self_of_k_ne_zero [DecidableEq K] [CharZero K]
    (hk : cf.k ≠ 0) {pq : P2 K × P2 K} (hpq : pq ∈ dom₀ cf) (n : ℕ) :
    (next cf)^[n] pq = pq ↔ n • g cf = 0 := by
  rw [← f_e cf hk hpq]
  rw [← f_add_smul_g]

  sorry
