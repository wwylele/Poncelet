import Mathlib

variable (u v r : ℂ)

def P2.equiv : Setoid ({p : Fin 3 → ℂ // p ≠ 0}) where
  r p q := ∃ (l : ℂ), l ≠ 0 ∧ p = l • q.val
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

def P2 := Quotient P2.equiv

namespace P2
def mk (p : Fin 3 → ℂ) (hp : p ≠ 0) := Quotient.mk equiv ⟨p, hp⟩

noncomputable def mk' (p : Fin 3 → ℂ) :=
  if hp : p ≠ 0 then mk p hp else mk ![1, 0, 0] (by simp)

@[simp]
theorem mk'_eq {p : Fin 3 → ℂ} (hp : p ≠ 0) :
    mk' p = mk p hp := by simp [mk', hp]

theorem mk_eq_mk {p q : Fin 3 → ℂ} (hp : p ≠ 0) (hq : q ≠ 0) :
    mk p hp = mk q hq ↔ ∃ (l : ℂ), l ≠ 0 ∧ p = l • q := Quotient.eq

theorem mk_eq_mk' {p q : Fin 3 → ℂ} (hp : p ≠ 0) (hq : q ≠ 0) :
    mk p hp = mk q hq ↔ ∃ (l : ℂ), p = l • q := by
  rw [mk_eq_mk]
  refine exists_congr (fun l ↦ ?_)
  suffices p = l • q → l ≠ 0 by simpa
  intro rfl
  contrapose! hp with rfl
  simp

theorem mk'_eq_mk' {p q : Fin 3 → ℂ} {l : ℂ} (hl : l ≠ 0) (h : p = l • q) :
    mk' p = mk' q := by
  by_cases! hp : p = 0
  · obtain hq := (smul_eq_zero.mp (hp ▸ h.symm)).resolve_left hl
    simp [mk', hp, hq]
  · obtain hq := (smul_ne_zero_iff.mp (h ▸ hp)).2
    simpa [mk', hp, hq, mk_eq_mk'] using ⟨l, h⟩

theorem mk'_smul {s : ℂ} (h : s ≠ 0) (p : Fin 3 → ℂ) :
    mk' (s • p) = mk' p := mk'_eq_mk' h rfl

def lift {α : Sort*} (f : (p : Fin 3 → ℂ) → p ≠ 0 → α)
    (h : ∀ p q, (hp : p ≠ 0) → (hq : q ≠ 0) → (∃ (l : ℂ), l ≠ 0 ∧ p = l • q) → f p hp = f q hq)
    (p : P2) : α :=
  Quotient.lift (fun (p : {p : Fin 3 → ℂ // p ≠ 0}) ↦ f p.val p.prop)
    (fun p q ↦ h p.val q.val p.prop q.prop) p

@[simp]
theorem lift_mk {α : Sort*} (f : (p : Fin 3 → ℂ) → p ≠ 0 → α)
    (h : ∀ p q, (hp : p ≠ 0) → (hq : q ≠ 0) → (∃ (l : ℂ), l ≠ 0 ∧ p = l • q) → f p hp = f q hq)
    {p : Fin 3 → ℂ} (hp : p ≠ 0) : lift f h (mk p hp) = f p hp := rfl

def lift₂ {α : Sort*} (f : (p : Fin 3 → ℂ) → (q : Fin 3 → ℂ) → p ≠ 0 → q ≠ 0 → α)
    (h : ∀ p q r s, (hp : p ≠ 0) → (hq : q ≠ 0) → (hr : r ≠ 0) → (hs : s ≠ 0) →
      (∃ (l : ℂ), l ≠ 0 ∧ p = l • r) → (∃ (l : ℂ), l ≠ 0 ∧ q = l • s) → f p q hp hq = f r s hr hs)
    (p q : P2) : α :=
  Quotient.lift₂ (fun (p q : {p : Fin 3 → ℂ // p ≠ 0}) ↦ f p.val q.val p.prop q.prop)
    (fun p q r s ↦ h p.val q.val r.val s.val p.prop q.prop r.prop s.prop) p q

@[simp]
theorem lift₂_mk {α : Sort*} (f : (p : Fin 3 → ℂ) → (q : Fin 3 → ℂ) → p ≠ 0 → q ≠ 0 → α)
    (h : ∀ p q r s, (hp : p ≠ 0) → (hq : q ≠ 0) → (hr : r ≠ 0) → (hs : s ≠ 0) →
      (∃ (l : ℂ), l ≠ 0 ∧ p = l • r) → (∃ (l : ℂ), l ≠ 0 ∧ q = l • s) → f p q hp hq = f r s hr hs)
    {p q : Fin 3 → ℂ} (hp : p ≠ 0) (hq : q ≠ 0) : lift₂ f h (mk p hp) (mk q hq) = f p q hp hq := rfl

@[elab_as_elim, induction_eliminator]
theorem ind {motive : P2 → Prop} (mk : ∀ p, (hp : p ≠ 0) → motive (mk p hp)) (p : P2) :
    motive p := by
  apply Quotient.ind
  intro p
  apply mk

end P2

def OuterCircle (p : P2) : Prop :=
  p.lift (fun p hp ↦ (p 0 - u * p 2) ^ 2 + p 1 ^ 2 = r ^ 2 * p 2 ^ 2) fun p q hp hq h ↦ (by
    obtain ⟨l, h0, rfl⟩ := h
    simp_rw [Pi.smul_apply, smul_eq_mul]
    conv_rhs =>
      rw [← mul_left_inj' (sq_eq_zero_iff.ne.mpr h0)]
    congrm ?_ = ?_ <;> ring
  )

def InnerCircle (p : P2) : Prop :=
  p.lift (fun p hp ↦ p 0 ^ 2 + p 1 ^ 2 = p 2 ^ 2) fun p q hp hq h ↦ by
    obtain ⟨l, h0, rfl⟩ := h
    simp_rw [Pi.smul_apply, smul_eq_mul]
    conv_rhs =>
      rw [← mul_left_inj' (sq_eq_zero_iff.ne.mpr h0)]
    congrm ?_ = ?_ <;> ring

def Incidence (p q : P2) : Prop :=
  P2.lift₂ (fun p q hp hq ↦ p 0 * q 0 + p 1 * q 1 = p 2 * q 2) (fun p q r s hp hq hr hs hpr hqs ↦ by
    obtain ⟨l, hl0, rfl⟩ := hpr
    obtain ⟨m, hm0, rfl⟩ := hqs
    simp_rw [Pi.smul_apply, smul_eq_mul]
    conv_rhs =>
      rw [← mul_left_inj' (mul_ne_zero hl0 hm0)]
    congrm ?_ = ?_ <;> ring
  ) p q

def dom : Set (P2 × P2) := {pq | OuterCircle u r pq.1 ∧ InnerCircle pq.2 ∧ Incidence pq.1 pq.2}

@[simp]
theorem mem_dom {p q : Fin 3 → ℂ} (hp : p ≠ 0) (hq : q ≠ 0) :
    ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom u r ↔ (
    (p 0 - u * p 2) ^ 2 + p 1 ^ 2 = r ^ 2 * p 2 ^ 2 ∧
    q 0 ^ 2 + q 1 ^ 2 = q 2 ^ 2 ∧
    p 0 * q 0 + p 1 * q 1 = p 2 * q 2) := by rfl

noncomputable
def rPoint' (p q : Fin 3 → ℂ) : Fin 3 → ℂ :=
  if q 2 = 0 then
    if p 2 = 0 then
      ![-(r ^ 2 - u ^ 2) * q 1, (r ^ 2 - u ^ 2) * q 0, 2 * u * q 1]
    else
      ![q 1, -q 0, 0]
  else
    ![2 * q 0 * p 2 * q 2 + 2 * u * q 1 ^ 2 * p 2 - p 0 * q 2 ^ 2,
      2 * q 1 * p 2 * q 2 - 2 * u * q 0 * q 1 * p 2  - p 1 * q 2 ^ 2,
      p 2 * q 2 ^ 2]

theorem rPoint'_rPoint' (hu : u ≠ 0) {p q : Fin 3 → ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom u r) :
    ∃ l : ℂ, rPoint' u r (rPoint' u r p q) q = l • p := by
  obtain ⟨ho, hi, hpq⟩ := mem_dom u r hp hq |>.mp h
  unfold rPoint'
  by_cases! hq0 : q 2 = 0
  · by_cases hp0 : p 2 = 0
    · have hq2 : q 1 ≠ 0 := by
        by_contra! hq2
        have : q 0 = 0 := by simpa [hq0, hq2] using hi
        clear h
        contrapose! hq
        ext n; fin_cases n <;> assumption
      have hp1 : p 0 ≠ 0 := by
        by_contra! hp1
        have : p 1 = 0 := by simpa [hp1, hp0, hq2] using hpq
        clear h
        contrapose! hp
        ext n; fin_cases n <;> assumption
      use q 1 / p 0
      ext n
      fin_cases n
      · suffices q 1 = q 1 / p 0 * p 0 by simpa [hp0, hq0, hu, hq2]
        grind
      · suffices -q 0 = q 1 / p 0 * p 1 by simpa [hp0, hq0, hu, hq2]
        grind
      · simp [hp0, hq0, hu, hq2]
    · use 2 * u * q 1 / p 2
      ext n
      fin_cases n
      · suffices (u ^ 2 - r ^ 2) * q 1 = 2 * u * q 1 / p 2 * p 0 by simpa [hp0, hq0]
        grind
      · suffices (r ^ 2 - u ^ 2) * q 0 = 2 * u * q 1 / p 2 * p 1 by simpa [hp0, hq0]
        grind
      · simp [hp0, hq0]
  use q 2 ^ 4
  ext n
  fin_cases n
  all_goals
  simp [hq0]
  ring

theorem rPoint'_ne_zero (hu : u ≠ 0) {p q : Fin 3 → ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom u r) : rPoint' u r p q ≠ 0 := by
  unfold rPoint'
  by_contra! h0
  by_cases! hq0 : q 2 = 0
  · by_cases! hp0 : p 2 = 0
    · obtain ⟨_, _, hq2⟩ : _ ∧ _ ∧ q 1 = 0 := by simpa [hu, hp0, hq0] using h0
      have hq1 : q 0 = 0 := by simpa [hq2, hq0] using (mem_dom u r hp hq |>.mp hpq).2.1
      clear hpq
      contrapose! hq
      ext n; fin_cases n <;> assumption
    · obtain ⟨hq2, hq1⟩ : q 1 = 0 ∧ q 0 = 0 := by simpa [hp0, hq0] using h0
      clear hpq
      contrapose! hq
      ext n; fin_cases n <;> assumption
  · by_cases! hp0 : p 2 = 0
    · obtain ⟨hp1, hp2⟩ : p 0 = 0 ∧ p 1 = 0 := by simpa [hp0, hq0] using h0
      clear hpq
      contrapose! hp
      ext n; fin_cases n <;> assumption
    · simp [hp0, hq0] at h0

/-theorem rPoint'_eq_self (hu : u ≠ 0) {p q : Fin 3 → ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom u r) :
    (∃ l : ℂ, rPoint' u r p q = l • p) ↔
    (2 * u * q 0 * q 2 + u ^ 2 * q 1 ^ 2) * q 1 = (1 + u ^ 2 - r ^ 2) * q 2 ^ 2 * q 1 := by
  obtain ⟨ho, hi, hpq⟩ := mem_dom u r hp hq |>.mp h

  by_cases! hq0 : q 2 = 0
  · unfold rPoint'
    by_cases! hp0 : p 2 = 0
    · have hq2 : q 1 ≠ 0 := by
        by_contra! hq2
        have : q 0 = 0 := by simpa [hq0, hq2] using hi
        clear h
        contrapose! hq
        ext n; fin_cases n <;> assumption
      simp [hq0, hp0, hu]

      · sorry
    · sorry
  trans rPoint' u r p q = q 2 ^ 2 • p
  · sorry

  unfold rPoint'
  constructor
  · sorry
  · sorry-/

noncomputable
def rPoint (pq : P2 × P2) : P2 × P2 := ⟨P2.lift₂ (fun p q hp hq ↦ P2.mk' (rPoint' u r p q)) (by
  intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
  unfold rPoint'
  have hp0 : p' 2 = 0 ↔ p 2 = 0 := by aesop
  have hq0 : q' 2 = 0 ↔ q 2 = 0 := by aesop
  simp_rw [hp0, hq0]
  split_ifs
  · apply P2.mk'_eq_mk' hm0
    rw [Matrix.smul_vec3]
    apply Matrix.vec3_eq
    all_goals
    simp_rw [hm, Pi.smul_apply, smul_eq_mul]
    ring
  · apply P2.mk'_eq_mk' hm0
    rw [Matrix.smul_vec3]
    apply Matrix.vec3_eq
    · simp [hm]
    · simp [hm]
    · simp
  apply P2.mk'_eq_mk' (show l * m ^ 2 ≠ 0 by simp [hl0, hm0])
  rw [Matrix.smul_vec3]
  apply Matrix.vec3_eq
  all_goals
  simp_rw [hl, hm, Pi.smul_apply, smul_eq_mul]
  ring
  ) pq.1 pq.2, pq.2⟩

theorem rPoint_mk (hu : u ≠ 0) {p q : Fin 3 → ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom u r) :
    rPoint u r ⟨P2.mk p hp, P2.mk q hq⟩ =
    ⟨P2.mk (rPoint' u r p q) (rPoint'_ne_zero u r hu hp hq hpq), P2.mk q hq⟩ := by
  simp [rPoint, rPoint'_ne_zero u r hu hp hq hpq]

theorem mapsTo_rPoint (hu : u ≠ 0) : Set.MapsTo (rPoint u r) (dom u r) (dom u r) := by
  intro ⟨p, q⟩ hpq
  induction p with | mk p hp
  induction q with | mk q hq
  rw [rPoint_mk u r hu hp hq hpq]
  obtain ⟨ho, hi, hpq⟩ := mem_dom u r hp hq |>.mp hpq
  rw [mem_dom]
  simp_rw [rPoint']
  split_ifs
  all_goals
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
  grind

theorem rPoint_rPoint (hu : u ≠ 0) {pq : P2 × P2} (hpq : pq ∈ dom u r) :
    rPoint u r (rPoint u r pq) = pq := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain hmem := mapsTo_rPoint u r hu hpq
  rw [rPoint_mk u r hu hp hq hpq] at ⊢ hmem
  rw [rPoint_mk u r hu _ _ hmem]
  refine Prod.ext_iff.mpr ⟨?_, rfl⟩
  rw [P2.mk_eq_mk']
  exact rPoint'_rPoint' u r hu hp hq hpq

theorem rPoint_bijOn (hu : u ≠ 0) : Set.BijOn (rPoint u r) (dom u r) (dom u r) := by
  refine ⟨mapsTo_rPoint u r hu, ?_, ?_⟩
  · intro p hp q hq h
    simpa [rPoint_rPoint, hu, hp, hq] using congr(rPoint u r $h)
  · intro p hp
    exact ⟨rPoint u r p, mapsTo_rPoint u r hu hp, rPoint_rPoint u r hu hp⟩

noncomputable
def rChord' (p q : Fin 3 → ℂ) : Fin 3 → ℂ :=
  if 2 * u * p 0 + r ^ 2 * p 2 - u ^ 2 * p 2 = 0 then -- all sorts of edge cases
    if p 0 = 0 then
      ![q 0, - q 1, q 2]
    else if q 2 = 0 then
      ![p 1 * (p 2 ^ 2 - p 1 ^ 2), p 0 * (p 2 ^ 2 + p 1 ^ 2), 2 * p 0 * p 1 * p 2]
    else
      ![p 1, -p 0, 0]
  else -- the only part I had on my notebook
    ![2 * p 0 * q 2 - (2 * u * p 0 + r ^ 2 * p 2 - u ^ 2 * p 2) * q 0,
      2 * p 1 * q 2 - (2 * u * p 0 + r ^ 2 * p 2 - u ^ 2 * p 2) * q 1,
      (2 * u * p 0 + r ^ 2 * p 2 - u ^ 2 * p 2) * q 2]

theorem rChord'_ne_zero (hu : u ≠ 0) {p q : Fin 3 → ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom u r) : rChord' u r p q ≠ 0 := by
  obtain ⟨ho, hi, hpq⟩ := mem_dom u r hp hq |>.mp h
  unfold rChord'
  by_cases! hxy : 2 * u * p 0 + r ^ 2 * p 2 - u ^ 2 * p 2 = 0
  · have h0' : p 0 ^ 2 + p 1 ^ 2 = 0 := by linear_combination ho + p 2 * hxy
    simp_rw [hxy]
    by_cases! hp1 : p 0 = 0
    · suffices q 0 = 0 → q 1 = 0 → q 2 ≠ 0 by simpa [hp1]
      intro hq0 hq1
      clear h
      contrapose! hq with hq2
      ext n; fin_cases n <;> assumption
    have hp2 : p 1 ≠ 0 := by
      contrapose! hp1
      simpa [hp1] using h0'
    have hp0 : p 2 ≠ 0 := by grind
    by_cases! hq0 : q 2 = 0
    · simp [hp1, hq0, hp2, hp0]
    · simp [hp1, hq0]
  by_cases! hq0 : q 2 = 0
  · suffices q 0 = 0 → q 1 ≠ 0 by simpa [hxy, hq0]
    intro hq0 hq1
    clear h
    contrapose! hq with hq2
    ext n; fin_cases n <;> assumption
  simp [hxy, hq0]

theorem rChord'_rChord' (hu : u ≠ 0) {p q : Fin 3 → ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom u r) :
    ∃ l : ℂ, rChord' u r p (rChord' u r p q) = l • q := by
  obtain ⟨ho, hi, hpq⟩ := mem_dom u r hp hq |>.mp h
  unfold rChord'
  by_cases h0 : 2 * u * p 0 + r ^ 2 * p 2 - u ^ 2 * p 2 = 0
  · have h0' : p 0 ^ 2 + p 1 ^ 2 = 0 := by linear_combination ho + p 2 * h0
    simp_rw [h0]
    by_cases! hp1 : p 0 = 0
    · use 1
      ext n
      fin_cases n
      all_goals
      simp [hp1]
    have hp2 : p 1 ≠ 0 := by
      contrapose! hp1
      simpa [hp1] using h0'
    have hp0 : p 2 ≠ 0 := by grind
    by_cases! hq0 : q 2 = 0
    · have hp0 : p 2 ≠ 0 := by grind
      have hq12 : p 0 * q 0 + p 1 * q 1 = 0 := by simpa [hq0] using hpq
      suffices ∃ l, ![p 1, -p 0, 0] = l • q by simpa [hp1, hq0, hp0, hp2]
      have hq1 : q 0 ≠ 0 := by
        clear h
        contrapose! hq with hq1
        have hq2 : q 1 = 0 := by simpa [hq1, hp2] using hq12
        ext n; fin_cases n <;> assumption
      use p 1 / q 0
      ext n
      fin_cases n
      · simp [hq1]
      · simp
        grind
      · simp [hq0]
    use 2 * p 0 * p 1 * p 2 / q 2
    ext n
    fin_cases n
    · simp [hp1, hq0]
      grind
    · simp [hp1, hq0]
      grind
    · simp [hp1, hq0]
  · use (2 * u * p 0 + (r ^ 2) * p 2 - u ^ 2 * p 2) ^ 2
    ext n
    fin_cases n
    all_goals
    simp [h0]
    ring

/-theorem rChord'_eq_self (hu : u ≠ 0) {p q : Fin 3 → ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom u r) :
    (∃ l : ℂ, rChord' u r p q = l • q) ↔ p 0 ^ 2 + p 1 ^ 2 = p 2 ^ 2 := by
  by_cases! hxy : 2 * u * p 0 + r ^ 2 * p 2 - u ^ 2 * p 2 = 0
  · sorry
  trans rChord' u r p q = (2 * u * p 0 + r ^ 2 * p 2 - u ^ 2 * p 2) • q
  · sorry
  · simp only [rChord', Fin.isValue, hxy, ↓reduceIte]
    constructor
    · intro h
      sorry
    · sorry-/

noncomputable
def rChord (pq : P2 × P2) : P2 × P2 :=
  ⟨pq.1, P2.lift₂ (fun p q hp hq ↦ P2.mk' (rChord' u r p q)) (by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    unfold rChord'
    have hxy : 2 * u * p' 0 + r ^ 2 * p' 2 - u ^ 2 * p' 2 = 0 ↔
        2 * u * p 0 + r ^ 2 * p 2 - u ^ 2 * p 2 = 0 := by
      rw [hl]
      conv_lhs =>
        rw [← mul_left_inj' hl0]
      congrm ?_ = ?_
      · simp only [Pi.smul_apply, smul_eq_mul]
        ring
      · simp
    have hp1 : p' 0 = 0 ↔ p 0 = 0 := by aesop
    have hq0 : q' 2 = 0 ↔ q 2 = 0 := by aesop
    simp_rw [hxy, hp1, hq0]
    split_ifs
    · apply P2.mk'_eq_mk' hm0
      rw [Matrix.smul_vec3]
      apply Matrix.vec3_eq
      · simp [hm]
      · simp_rw [hm, Pi.smul_apply, smul_eq_mul]
        ring
      · simp [hm]
    · apply P2.mk'_eq_mk' (mul_ne_zero hl0 (mul_ne_zero hl0 hl0))
      rw [Matrix.smul_vec3]
      apply Matrix.vec3_eq
      all_goals
      simp_rw [hl, Pi.smul_apply, smul_eq_mul]
      ring
    · apply P2.mk'_eq_mk' hl0
      rw [Matrix.smul_vec3]
      apply Matrix.vec3_eq
      · simp [hl, Pi.smul_apply]
      · simp [hl, Pi.smul_apply]
      · simp
    · apply P2.mk'_eq_mk' (mul_ne_zero hl0 hm0)
      rw [Matrix.smul_vec3]
      apply Matrix.vec3_eq
      all_goals
      simp_rw [hl, hm, Pi.smul_apply, smul_eq_mul]
      ring
  ) pq.1 pq.2⟩

theorem rChord_mk (hu : u ≠ 0) {p q : Fin 3 → ℂ} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom u r) :
    rChord u r ⟨P2.mk p hp, P2.mk q hq⟩ =
    ⟨P2.mk p hp, P2.mk (rChord' u r p q) (rChord'_ne_zero u r hu hp hq hpq)⟩ := by
  simp [rChord, rChord'_ne_zero u r hu hp hq hpq]

theorem mapsTo_rChord (hu : u ≠ 0) : Set.MapsTo (rChord u r) (dom u r) (dom u r) := by
  intro ⟨p, q⟩ hpq
  induction p with | mk p hp
  induction q with | mk q hq
  rw [rChord_mk u r hu hp hq hpq]
  obtain ⟨ho, hi, hpq⟩ := mem_dom u r hp hq |>.mp hpq
  rw [mem_dom]
  simp_rw [rChord']
  split_ifs
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
    grind
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
    grind
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
    grind
  · simp
    grind

theorem rChord_rChord (hu : u ≠ 0) {pq : P2 × P2} (hpq : pq ∈ dom u r) :
    rChord u r (rChord u r pq) = pq := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain hmem := mapsTo_rChord u r hu hpq
  rw [rChord_mk u r hu hp hq hpq] at ⊢ hmem
  rw [rChord_mk u r hu _ _ hmem]
  refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
  rw [P2.mk_eq_mk']
  exact rChord'_rChord' u r hu hp hq hpq

theorem rChord_bijOn (hu : u ≠ 0) : Set.BijOn (rChord u r) (dom u r) (dom u r) := by
  refine ⟨mapsTo_rChord u r hu, ?_, ?_⟩
  · intro p hp q hq h
    simpa [rChord_rChord, hu, hp, hq] using congr(rChord u r $h)
  · intro p hp
    exact ⟨rChord u r p, mapsTo_rChord u r hu hp, rChord_rChord u r hu hp⟩
