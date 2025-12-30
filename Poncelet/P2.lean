import Mathlib

variable {K : Type*} [Field K]

variable (K) in
/-- Equivalent relation on projective plane. -/
def P2.equiv : Setoid ({p : Fin 3 → K // p ≠ 0}) where
  r p q := ∃ (l : K), l ≠ 0 ∧ p = l • q.val
  iseqv := {
    refl p := ⟨1, by simp⟩
    symm {p q} h := by
      obtain ⟨l, h0, hl⟩ := h
      exact ⟨l⁻¹, by simp [h0], by simp [hl, h0]⟩
    trans {p q r} hpq hqr := by
      obtain ⟨l, hl0, hl⟩ := hpq
      obtain ⟨m, hm0, hm⟩ := hqr
      exact ⟨l * m, by simp [hl0, hm0], by simp [← smul_smul, hl, hm]⟩
  }

variable (K) in
/-- The projective plane. -/
def P2 := Quotient (P2.equiv K)

unsafe instance [Repr K] : Repr (P2 K) where
  reprPrec p :=
    let p := p.unquot
    Repr.reprPrec (p.val 0, p.val 1, p.val 2)

namespace P2
/-- Point constructor on the projective plane. -/
def mk (p : Fin 3 → K) (hp : p ≠ 0) := Quotient.mk (equiv K) ⟨p, hp⟩

/-- Alternative constructor that doesn't require the proof of non-zero
but assign a junk value. -/
def mk' [DecidableEq K] (p : Fin 3 → K) :=
  if hp : p ≠ 0 then mk p hp else mk ![1, 0, 0] (by simp)

@[simp]
theorem mk'_eq [DecidableEq K] {p : Fin 3 → K} (hp : p ≠ 0) :
    mk' p = mk p hp := by simp [mk', hp]

theorem mk_eq_mk {p q : Fin 3 → K} (hp : p ≠ 0) (hq : q ≠ 0) :
    mk p hp = mk q hq ↔ ∃ (l : K), l ≠ 0 ∧ p = l • q := Quotient.eq

theorem mk_eq_mk' {p q : Fin 3 → K} (hp : p ≠ 0) (hq : q ≠ 0) :
    mk p hp = mk q hq ↔ ∃ (l : K), p = l • q := by
  rw [mk_eq_mk]
  refine exists_congr (fun l ↦ ?_)
  suffices p = l • q → l ≠ 0 by simpa
  intro rfl
  contrapose! hp with rfl
  simp

theorem mk'_eq_mk' [DecidableEq K] {p q : Fin 3 → K} {l : K} (hl : l ≠ 0) (h : p = l • q) :
    mk' p = mk' q := by
  by_cases! hp : p = 0
  · obtain hq := (smul_eq_zero.mp (hp ▸ h.symm)).resolve_left hl
    simp [mk', hp, hq]
  · obtain hq := (smul_ne_zero_iff.mp (h ▸ hp)).2
    simpa [mk', hp, hq, mk_eq_mk'] using ⟨l, h⟩

theorem mk_eq_mk'_of_l [DecidableEq K] {p q : Fin 3 → K} (hp : p ≠ 0) (l : K) (h : p = l • q) :
    mk p hp = mk' q := by
  have hl : l ≠ 0 := by
    contrapose! hp with hl
    simp [h, hl]
  rw [← mk'_eq]
  apply mk'_eq_mk' hl h

theorem mk'_eq_mk'_of_third_zero [DecidableEq K] {p q : Fin 3 → K} (hp : p ≠ 0)
    (hq1 : q 1 ≠ 0)
    (hp2 : p 2 = 0) (hq2 : q 2 = 0) (h : p 0 * q 1 = p 1 * q 0) :
    mk p hp = mk' q := by
  apply mk_eq_mk'_of_l hp (p 1 / q 1)
  ext n
  fin_cases n
  · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    field_simp
    exact h
  · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    field
  · simp [hp2, hq2]

theorem mk'_eq_mk'_of_third [DecidableEq K] {p q : Fin 3 → K} (hp : p ≠ 0) (hq2 : q 2 ≠ 0)
    (h0 : p 0 * q 2 = p 2 * q 0) (h1 : p 1 * q 2 = p 2 * q 1) :
    mk p hp = mk' q := by
  apply mk_eq_mk'_of_l _ (p 2 / q 2)
  ext n
  fin_cases n
  · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    field_simp
    exact h0
  · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    field_simp
    exact h1
  · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, smul_eq_mul]
    field_simp

theorem mk'_smul [DecidableEq K] {s : K} (h : s ≠ 0) (p : Fin 3 → K) :
    mk' (s • p) = mk' p := mk'_eq_mk' h rfl

/-- Lift a function on the projective plane. -/
def lift {α : Sort*} (f : (p : Fin 3 → K) → p ≠ 0 → α)
    (h : ∀ p q, (hp : p ≠ 0) → (hq : q ≠ 0) → (∃ (l : K), l ≠ 0 ∧ p = l • q) → f p hp = f q hq)
    (p : P2 K) : α :=
  Quotient.lift (fun (p : {p : Fin 3 → K // p ≠ 0}) ↦ f p.val p.prop)
    (fun p q ↦ h p.val q.val p.prop q.prop) p

@[simp]
theorem lift_mk {α : Sort*} (f : (p : Fin 3 → K) → p ≠ 0 → α)
    (h : ∀ p q, (hp : p ≠ 0) → (hq : q ≠ 0) → (∃ (l : K), l ≠ 0 ∧ p = l • q) → f p hp = f q hq)
    {p : Fin 3 → K} (hp : p ≠ 0) : lift f h (mk p hp) = f p hp := rfl

/-- Lift a function of two variables on the projective plane. -/
def lift₂ {α : Sort*} (f : (p : Fin 3 → K) → (q : Fin 3 → K) → p ≠ 0 → q ≠ 0 → α)
    (h : ∀ p q r s, (hp : p ≠ 0) → (hq : q ≠ 0) → (hr : r ≠ 0) → (hs : s ≠ 0) →
      (∃ (l : K), l ≠ 0 ∧ p = l • r) → (∃ (l : K), l ≠ 0 ∧ q = l • s) → f p q hp hq = f r s hr hs)
    (p q : P2 K) : α :=
  Quotient.lift₂ (fun (p q : {p : Fin 3 → K // p ≠ 0}) ↦ f p.val q.val p.prop q.prop)
    (fun p q r s ↦ h p.val q.val r.val s.val p.prop q.prop r.prop s.prop) p q

@[simp]
theorem lift₂_mk {α : Sort*} (f : (p : Fin 3 → K) → (q : Fin 3 → K) → p ≠ 0 → q ≠ 0 → α)
    (h : ∀ p q r s, (hp : p ≠ 0) → (hq : q ≠ 0) → (hr : r ≠ 0) → (hs : s ≠ 0) →
      (∃ (l : K), l ≠ 0 ∧ p = l • r) → (∃ (l : K), l ≠ 0 ∧ q = l • s) → f p q hp hq = f r s hr hs)
    {p q : Fin 3 → K} (hp : p ≠ 0) (hq : q ≠ 0) : lift₂ f h (mk p hp) (mk q hq) = f p q hp hq := rfl

@[elab_as_elim, induction_eliminator]
theorem ind {motive : P2 K → Prop} (mk : ∀ p, (hp : p ≠ 0) → motive (mk p hp)) (p : P2 K) :
    motive p := by
  apply Quotient.ind
  intro p
  apply mk

end P2
