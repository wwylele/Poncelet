import Poncelet.Inverse
import Poncelet.Transfer

variable {K : Type*} [Field K]
variable (cf : Config K)

/--
Poncelet's closure theorem, partial:
Given a circle unit circle $D$ at $(0, 0)$ and a circle $C$ with radius $r$ at $(u, 0)$,
($u ≠ 0$, $r ≠ 0$, $u + r ≠ ±1$)
if the corresponding `g` point on the elliptic curve is an `n`-torsion, then
one can draw an `n`-gon simutaneously inscribed in $C$ and circumscribed around $D$
starting from any point on $D$.
-/
theorem iterate_next_eq_self_of_n_torsion [DecidableEq K] [CharZero K]
    (hk : cf.k ≠ 0) {pq : P2 K × P2 K} (hpq : pq ∈ dom cf) {n : ℕ}
    (hg : n • g cf = 0) :
    (next cf)^[n] pq = pq := by
  by_cases hdom0 : pq ∈ dom₀ cf
  · rw [← f_e cf hk hdom0, ← f_add_smul_g, hg]
    simp
  · rw [mem_dom₀] at hdom0
    have : pq = (P2.mk ![1, 0, 1] (by simp), P2.mk ![1, 0, 1] (by simp)) ∨
        pq = (P2.mk ![-1, 0, 1] (by simp), P2.mk ![-1, 0, 1] (by simp)) := by
      simpa [hpq, Classical.or_iff_not_imp_left] using hdom0
    obtain heq := (next_eq_self' cf hpq).mpr this
    clear hg
    induction n with
    | zero => simp
    | succ n ih =>
      simp [heq, ih]

/-
[propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]-/
#print axioms iterate_next_eq_self_of_n_torsion

theorem iterate_next_eq_self_iff_of_k_ne_zero [DecidableEq K] [CharZero K]
    (hk : cf.k ≠ 0) {pq : P2 K × P2 K} (hpq : pq ∈ dom₀ cf) (n : ℕ) :
    (next cf)^[n] pq = pq ↔ n • g cf = 0 := by
  rw [← f_e cf hk hpq]
  rw [← f_add_smul_g]

  sorry
