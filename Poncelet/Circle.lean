import Mathlib
import Poncelet.P2

variable {K : Type*} [Field K]

variable (K) in
/-- A set of parameters to represent a two-circle configuration.
The inner circle is fixed at $[0 : 0 : 1]$ with radius $1$, and the outer circle
is at $[u : 0 : 1]$ with radius $r$. -/
structure Config where
  /-- x-coordinate of the center of the outer circle -/
  u : K
  /-- Radius of the outer circle -/
  r : K
  /-- Disallow concentric circles -/
  hu : u ≠ 0
  /-- Disallow degenerate circles -/
  hr : r ≠ 0
  /-- An auxilliary constant for computation -/
  k : K
  /-- The constant `k` must satisfy this equation -/
  k_sq : k ^ 2 = (u + r) ^ 2 - 1

variable (cf : Config K)

/-- The predicate that a point is on the outer circle. -/
def OuterCircle (p : P2 K) : Prop :=
  p.lift (fun p hp ↦ (p 0 - cf.u * p 2) ^ 2 + p 1 ^ 2 = cf.r ^ 2 * p 2 ^ 2) fun p q hp hq h ↦ by
    obtain ⟨l, h0, rfl⟩ := h
    simp_rw [Pi.smul_apply, smul_eq_mul]
    conv_rhs =>
      rw [← mul_left_inj' (sq_eq_zero_iff.ne.mpr h0)]
    congrm ?_ = ?_ <;> ring

instance [DecidableEq K] : DecidablePred (OuterCircle cf) := by
  unfold OuterCircle P2.lift
  infer_instance

theorem outerCircle_iff_of_r_eq_neg (cf' : Config K)
    (hu : cf'.u = cf.u) (hr : cf'.r = -cf.r) (p : P2 K) :
    OuterCircle cf p ↔ OuterCircle cf' p := by
  unfold OuterCircle
  simp_rw [hu, hr, neg_sq]

/-- The predicate that a line (where $[a : b : c]$ means $ax + by = cz$)
is tangent to the outer circle. -/
def TangentOuterCircle (p : P2 K) : Prop :=
  p.lift (fun p hp ↦
      (cf.r ^ 2 - cf.u ^ 2) * p 0 ^ 2 + 2 * cf.u * p 0 * p 2 + cf.r ^ 2 * p 1 ^ 2 = p 2 ^ 2)
    fun p q hp hq h ↦ by
    obtain ⟨l, h0, rfl⟩ := h
    simp_rw [Pi.smul_apply, smul_eq_mul]
    conv_rhs =>
      rw [← mul_left_inj' (sq_eq_zero_iff.ne.mpr h0)]
    congrm ?_ = ?_ <;> ring

instance [DecidableEq K] : DecidablePred (TangentOuterCircle cf) := by
  unfold TangentOuterCircle P2.lift
  infer_instance

theorem tangentOuterCircle_iff_of_r_eq_neg (cf' : Config K)
    (hu : cf'.u = cf.u) (hr : cf'.r = -cf.r) (p : P2 K) :
    TangentOuterCircle cf p ↔ TangentOuterCircle cf' p := by
  unfold TangentOuterCircle
  simp_rw [hu, hr, neg_sq]

/-- This is a dual-purpose predicate:
 - a point is on the inner circle.
 - a line (where $[a : b : c]$ means $ax + by = cz$) is tangent to the inner circle. -/
def InnerCircle (_ : Config K) (p : P2 K) : Prop :=
  p.lift (fun p hp ↦ p 0 ^ 2 + p 1 ^ 2 = p 2 ^ 2) fun p q hp hq h ↦ by
    obtain ⟨l, h0, rfl⟩ := h
    simp_rw [Pi.smul_apply, smul_eq_mul]
    conv_rhs =>
      rw [← mul_left_inj' (sq_eq_zero_iff.ne.mpr h0)]
    congrm ?_ = ?_ <;> ring

instance [DecidableEq K] : DecidablePred (InnerCircle cf) := by
  unfold InnerCircle P2.lift
  infer_instance

theorem innerCircle_iff (cf' : Config K) (p : P2 K) :
    InnerCircle cf p ↔ InnerCircle cf' p := by
  rfl

theorem tangentOuterCircle_iff (p : P2 K) (hi : InnerCircle cf p) :
    TangentOuterCircle cf p ↔
      (p.lift (fun p hp ↦
        2 * cf.u * p 0 * p 2 + cf.u ^ 2 * p 1 ^ 2 = (1 + cf.u ^ 2 - cf.r ^ 2) * p 2 ^ 2)
        fun p q hp hq h ↦ by
          obtain ⟨l, h0, rfl⟩ := h
          simp_rw [Pi.smul_apply, smul_eq_mul]
          conv_rhs =>
            rw [← mul_left_inj' (sq_eq_zero_iff.ne.mpr h0)]
          congrm ?_ = ?_ <;> ring) := by
  induction p with | mk p hp
  simp only [TangentOuterCircle, P2.lift_mk]
  conv_lhs => rw [← sub_eq_zero]
  conv_rhs => rw [← sub_eq_zero]
  congrm(?_ = 0)
  simp only [InnerCircle, P2.lift_mk] at hi
  have : p 0 ^ 2 = p 2 ^ 2 - p 1 ^ 2 := by linear_combination hi
  rw [this]
  ring

/-- The predicate that a point is on the line. -/
def Incidence (_ : Config K) (p q : P2 K) : Prop :=
  P2.lift₂ (fun p q hp hq ↦ p 0 * q 0 + p 1 * q 1 = p 2 * q 2) (fun p q r s hp hq hr hs hpr hqs ↦ by
    obtain ⟨l, hl0, rfl⟩ := hpr
    obtain ⟨m, hm0, rfl⟩ := hqs
    simp_rw [Pi.smul_apply, smul_eq_mul]
    conv_rhs =>
      rw [← mul_left_inj' (mul_ne_zero hl0 hm0)]
    congrm ?_ = ?_ <;> ring
  ) p q

instance [DecidableEq K] (p : P2 K) : DecidablePred (Incidence cf p) := by
  unfold Incidence P2.lift₂
  infer_instance

theorem incidence_iff (cf' : Config K) (p q : P2 K) :
    Incidence cf p q ↔ Incidence cf' p q := by
  rfl

/-- The set of pairs of vertex and edge, where the vertex is on the outer circle,
the edge is tanget to the inner circle, and the vertex is on the line of the edge. -/
def dom : Set (P2 K × P2 K) :=
  {pq | OuterCircle cf pq.1 ∧ InnerCircle cf pq.2 ∧ Incidence cf pq.1 pq.2}

instance [DecidableEq K] : DecidablePred (· ∈ dom cf) := by
  unfold dom
  infer_instance

theorem dom_eq_of_r_eq_neg (cf' : Config K)
    (hu : cf'.u = cf.u) (hr : cf'.r = -cf.r) :
    dom cf = dom cf' := by
  simp_rw [dom, outerCircle_iff_of_r_eq_neg cf cf' hu hr, innerCircle_iff cf cf',
    incidence_iff cf cf']

@[simp]
theorem mem_dom {p q : Fin 3 → K} (hp : p ≠ 0) (hq : q ≠ 0) :
    ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf ↔ (
    (p 0 - cf.u * p 2) ^ 2 + p 1 ^ 2 = cf.r ^ 2 * p 2 ^ 2 ∧
    q 0 ^ 2 + q 1 ^ 2 = q 2 ^ 2 ∧
    p 0 * q 0 + p 1 * q 1 = p 2 * q 2) := by rfl

theorem encard_dom_fix1_le [hchar : NeZero (2 : K)] (p : P2 K) :
    Set.encard {pq ∈ dom cf | pq.1 = p} ≤ 2 := by
  classical
  induction p with | mk p hp
  by_cases hp2 : p 2 = 0
  · by_cases hp1 : p 1 = 0
    · suffices {pq ∈ dom cf | pq.1 = P2.mk _ hp} = ∅ by
        simp [this]
      rw [Set.eq_empty_iff_forall_notMem]
      intro pq
      obtain ⟨p', q⟩ := pq
      by_contra! hpq
      obtain ⟨hpq, rfl⟩ : ⟨p', q⟩ ∈ dom cf ∧ p' = P2.mk p hp := by simpa using hpq
      have hp0 : p 0 = 0 := by simpa [OuterCircle, hp2, hp1] using hpq.1
      suffices p = 0 from hp this
      ext i
      fin_cases i
      · simpa using hp0
      · simpa using hp1
      · simpa using hp2
    suffices {pq ∈ dom cf | pq.1 = P2.mk _ hp} ⊆
        {⟨P2.mk _ hp, P2.mk ![p 1, -p 0, 0] (by simp [hp1])⟩} by
      apply (Set.encard_mono this).trans
      simp
    intro pq h
    obtain ⟨p', q⟩ := pq
    obtain ⟨hpq, rfl⟩ : (p', q) ∈ dom cf ∧ p' = P2.mk p hp := by simpa using h
    induction q with | mk q hq
    obtain ⟨ho, hi, hpq⟩ : p 0 ^ 2 + p 1 ^ 2 = 0
        ∧ q 0 ^ 2 + q 1 ^ 2 = q 2 ^ 2 ∧ p 0 * q 0 + p 1 * q 1 = 0 := by
      simpa [hp2] using hpq
    suffices P2.mk q hq = P2.mk ![p 1, -p 0, 0] _ by simpa
    refine P2.mk_eq_mk_of_third_zero _ _ ?_ (by simp) ?_
    · have ho : p 0 ^ 2 = - p 1 ^ 2 := by linear_combination ho
      obtain hpq : p 0 * q 0 = -p 1 * q 1 := by linear_combination hpq
      obtain hpq : p 0 ^ 2 * q 0 ^ 2 = p 1 ^ 2 * q 1 ^ 2 := by linear_combination congr($hpq ^ 2)
      rw [ho] at hpq
      have hpq : q 0 ^ 2 + q 1 ^ 2 = 0 := by
        rw [← mul_left_inj' hp1, ← mul_left_inj' hp1]
        linear_combination -hpq
      simpa [hpq] using hi.symm
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      linear_combination -hpq
  by_cases hq1 : ∃ (q0 q2 : K) (hq : ![q0, 0, q2] ≠ 0),
      ⟨P2.mk _ hp, P2.mk _ hq⟩ ∈ {pq ∈ dom cf | pq.1 = P2.mk _ hp}
  · obtain ⟨q0, q2, hq, hpq⟩ := hq1
    obtain ⟨ho, hi, hpq⟩ : (p 0 - cf.u * p 2) ^ 2 + p 1 ^ 2 = cf.r ^ 2 * p 2 ^ 2
        ∧ q0 ^ 2 = q2 ^ 2
        ∧ p 0 * q0 = p 2 * q2 := by
      simpa using hpq
    have hq2 : q2 ≠ 0 := by
      by_contra! hq2
      suffices ![q0, 0, q2] = 0 from hq this
      suffices q0 = 0 by simpa [hq2]
      simpa [hq2] using hi
    have hp02 : p 0 ^ 2 = p 2 ^ 2 := by
      obtain hi | hi := eq_or_eq_neg_of_sq_eq_sq _ _ hi
      · have hp02 : p 0 = p 2 := by simpa [hi, hq2] using hpq
        simp [hp02]
      · have hp02 : -p 0 = p 2 := by simpa [hi, hq2, ← neg_mul] using hpq
        simp [← hp02]
    have hp2' : p 2 = p 0 * q0 / q2 := by
      field_simp
      linear_combination -hpq
    have hp0 : p 0 ≠ 0 := by
      by_contra! hp0
      suffices p = 0 from hp this
      have hp20 : p 2 = 0 := by simpa [hp0] using hp2'
      simp [hp20] at hp2
    suffices {pq ∈ dom cf | pq.1 = P2.mk _ hp} ⊆
        {⟨P2.mk _ hp, P2.mk _ hq⟩,
        ⟨P2.mk _ hp, P2.mk ![(p 2 ^ 2 - p 1 ^ 2) / (2 * p 0 * p 1), 1,
        (((p 2 ^ 2 - p 1 ^ 2) / (2 * p 0 * p 1) * p 0) + p 1) / p 2] (by simp)⟩} by
      apply (Set.encard_mono this).trans
      grw [Set.encard_insert_le]
      simp [one_add_one_eq_two]
    intro pq' hpq'mem
    obtain ⟨p', q'⟩ := pq'
    obtain ⟨hq'mem, rfl⟩ : (p', q') ∈ dom cf ∧ p' = P2.mk p hp := by simpa using hpq'mem
    suffices q' = P2.mk _ hq ∨ q' = P2.mk ![(p 2 ^ 2 - p 1 ^ 2) / (2 * p 0 * p 1), 1,
          (((p 2 ^ 2 - p 1 ^ 2) / (2 * p 0 * p 1) * p 0) + p 1) / p 2] (by simp) by simpa
    induction q' with | mk q' hq'
    obtain ⟨_, hi', hpq'⟩ : (p 0 - cf.u * p 2) ^ 2 + p 1 ^ 2 = cf.r ^ 2 * p 2 ^ 2
      ∧ q' 0 ^ 2 + q' 1 ^ 2 = q' 2 ^ 2
      ∧ p 0 * q' 0 + p 1 * q' 1 = p 2 * q' 2 := by
      simpa using hq'mem
    by_cases hq'1 : q' 1 = 0
    · left
      rw [P2.mk_eq_mk']
      use q' 2 / q2
      ext i
      fin_cases i
      · suffices q' 0 = q' 2 / q2 * q0 by simpa
        field_simp
        rw [hp2', hq'1] at hpq'
        field_simp at hpq'
        rw [← mul_left_inj' hp0]
        linear_combination hpq'
      · simp [hq'1]
      · simp [field]
    · have h : (p 2 ^ 2 - p 0 ^ 2) * (q' 0) ^ 2
        - 2 * p 0 * p 1 * q' 0 * q' 1 + (p 2 ^ 2 - p 1 ^ 2) * q' 1 ^ 2 = 0 := by
        linear_combination p 2 ^ 2 * hi' - congr($hpq' ^ 2)
      rw [hp02] at h
      have h : 2 * p 0 * p 1 * q' 0 * q' 1 = (p 2 ^ 2 - p 1 ^ 2) * q' 1 ^ 2 := by
        linear_combination -h
      have h : 2 * p 0 * p 1 * q' 0 = (p 2 ^ 2 - p 1 ^ 2) * q' 1  := by
        rw [← mul_left_inj' hq'1]
        linear_combination h
      have hp1 : p 1 ≠ 0 := by
        by_contra! hp1
        simp [hp0, hp1, hq'1, ← hp02] at h
      right
      rw [P2.mk_eq_mk']
      use q' 1
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
        field_simp
        linear_combination h
      · simp
      · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, Matrix.cons_val, smul_eq_mul]
        field_simp
        grind
  let poly : Polynomial K := Polynomial.C (p 2 ^ 2 - p 0 ^ 2) * Polynomial.X ^ 2
    - Polynomial.C (2 * p 0 * p 1) * Polynomial.X + Polynomial.C (p 2 ^ 2 - p 1 ^ 2)
  have hpoly : poly ≠ 0 := by
    by_contra!
    unfold poly at this
    have ha : p 2 ^ 2 - p 0 ^ 2 = 0 := by simpa [-map_sub] using congr(Polynomial.coeff $this 2)
    have hb : 2 * p 0 * p 1 = 0 := by simpa [-map_sub] using congr(Polynomial.coeff $this 1)
    have hc : p 2 ^ 2 - p 1 ^ 2 = 0 := by simpa [-map_sub] using congr(Polynomial.coeff $this 0)
    obtain h0 | h1 : p 0 = 0 ∨ p 1 = 0 := by simpa [hchar.out] using hb
    · refine hp2 ?_
      simpa [h0] using ha
    · refine hp2 ?_
      simpa [h1] using hc
  suffices {pq ∈ dom cf | pq.1 = P2.mk _ hp} ⊆
    (fun x ↦ ⟨P2.mk _ hp, P2.mk ![x, 1, (p 0 * x + p 1) / p 2] (by simp)⟩) '' poly.roots.toFinset by
    apply (Set.encard_mono this).trans
    grw [Set.encard_image_le]
    rw [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le_ofNat]
    grw [Multiset.toFinset_card_le]
    grw [Polynomial.card_roots']
    unfold poly
    rw [Polynomial.natDegree_add_C]
    grw [Polynomial.natDegree_sub_le]
    apply max_le
    · grw [Polynomial.natDegree_C_mul_le]
      simp
    · grw [Polynomial.natDegree_C_mul_le]
      simp
  intro pq h
  obtain ⟨p', q⟩ := pq
  obtain ⟨hpq, rfl⟩ : (p', q) ∈ dom cf ∧ p' = P2.mk p hp := by simpa using h
  induction q with | mk q hq
  have hq1 : q 1 ≠ 0 := by
    contrapose! hq1
    have hqeq : ![q 0, 0, q 2] = q := by
      ext i
      fin_cases i
      · simp
      · simpa using hq1.symm
      · simp
    refine ⟨q 0, q 2, ?_, ?_⟩
    · convert hq
    · convert h
  rw [mem_dom] at hpq
  obtain ⟨_, hi, hpq⟩ := hpq
  suffices ∃ x, Polynomial.eval x poly = 0 ∧ P2.mk ![x, 1, (p 0 * x + p 1) / p 2] _ = P2.mk q hq by
    simpa [hpoly]
  use q 0 / q 1
  constructor
  · have h : (p 2 ^ 2 - p 0 ^ 2) * (q 0 / q 1) ^ 2
        - 2 * p 0 * p 1 * (q 0 / q 1) + (p 2 ^ 2 - p 1 ^ 2) = 0 := by
      field_simp
      linear_combination p 2 ^ 2 * hi - congr($hpq ^ 2)
    simpa [poly] using h
  · symm
    rw [P2.mk_eq_mk']
    use q 1
    ext i
    fin_cases i
    · simp [field]
    · simp
    · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, Matrix.cons_val, smul_eq_mul]
      field_simp
      linear_combination -hpq

theorem encard_dom_fix2_le [hchar : NeZero (2 : K)] (q : P2 K) :
    Set.encard {pq ∈ dom cf | pq.2 = q} ≤ 2 := by
  obtain _ := cf.hu
  classical
  induction q with | mk q hq
  by_cases hp2 : ∃ (p0 p1 : K) (hp : ![p0, p1, 0] ≠ 0),
      ⟨P2.mk _ hp, P2.mk _ hq⟩ ∈ {pq ∈ dom cf | pq.2 = P2.mk _ hq}
  · obtain ⟨p0, p1, hp, hmem⟩ := hp2
    obtain ⟨ho, hi, hpq⟩ : p0 ^ 2 + p1 ^ 2 = 0 ∧
        q 0 ^ 2 + q 1 ^ 2 = q 2 ^ 2 ∧ p0 * q 0 + p1 * q 1 = 0 := by
      simpa using hmem
    have hp1ne0 : p1 ≠ 0 := by
      by_contra! hp1
      suffices ![p0, p1, 0] = 0 from hp this
      ext i
      fin_cases i
      · simpa [hp1] using ho
      · simpa using hp1
      · simp
    have hq2 : q 2 = 0 := by
      have hpq : p0 * q 0 = - p1 * q 1 := by linear_combination hpq
      have hpq : p0 ^ 2 * q 0 ^ 2 = p1 ^ 2 * q 1 ^ 2 := by linear_combination congr($hpq ^ 2)
      have ho : p0 ^ 2 = -p1 ^ 2 := by linear_combination ho
      rw [ho] at hpq
      have : q 0 ^ 2 = -q 1 ^ 2 := by
        rw [← mul_left_inj' hp1ne0, ← mul_left_inj' hp1ne0]
        linear_combination -hpq
      simpa [this] using hi.symm
    have hq1ne0 : q 1 ≠ 0 := by
      by_contra! hq1
      suffices q = 0 from hq this
      ext i
      fin_cases i
      · simpa [hq1, hq2] using hi
      · simpa using hq1
      · simpa using hq2
    suffices {pq ∈ dom cf | pq.2 = P2.mk _ hq} ⊆
        {⟨P2.mk _ hp, P2.mk _ hq⟩,
        ⟨P2.mk ![(cf.u ^ 2 - cf.r ^ 2) / (2 * cf.u),
          -q 0 * (cf.u ^ 2 - cf.r ^ 2) / (2 * cf.u * q 1), 1] (by simp), P2.mk _ hq⟩} by
      apply (Set.encard_mono this).trans
      grw [Set.encard_insert_le]
      simp [one_add_one_eq_two]
    intro pq h
    obtain ⟨p, q'⟩ := pq
    obtain ⟨hpq', rfl⟩ : ⟨p, q'⟩ ∈ dom cf ∧ q' = P2.mk q hq := by simpa using h
    induction p with | mk p hp
    rw [mem_dom] at hpq'
    obtain ⟨ho, hi, hpq'⟩ := hpq'
    rw [hq2, zero_pow (by simp)] at hi
    rw [hq2, mul_zero] at hpq'
    have hpq' : p 1 * q 1 = - p 0 * q 0 := by linear_combination hpq'
    have : 2 * cf.u * p 0 * q 1 ^ 2 * p 2 = p 2 * (cf.u ^ 2 - cf.r ^ 2) * q 1 ^ 2 * p 2 := by
      linear_combination -q 1 ^ 2 * ho + congr($hpq' ^ 2) + hi * p 0 ^ 2
    suffices P2.mk p hp = P2.mk ![p0, p1, 0] _ ∨
        P2.mk p hp = P2.mk ![(cf.u ^ 2 - cf.r ^ 2) / (2 * cf.u),
        -(q 0 * (cf.u ^ 2 - cf.r ^ 2)) / (2 * cf.u * q 1), 1] _ by
      simpa
    by_cases hp2' : p 2 = 0
    · left
      apply P2.mk_eq_mk_of_third_zero _ _ hp2' rfl
      suffices p 0 * p1 = p 1 * p0 by simpa
      suffices p 0 * (p1 * q 1) = p 1 * q 1 * p0 by
        rw [← mul_left_inj' hq1ne0]
        linear_combination this
      rw [hpq']
      linear_combination p 0 * hpq
    · right
      have : 2 * cf.u * p 0 = p 2 * (cf.u ^ 2 - cf.r ^ 2) := by simpa [hp2', hq1ne0] using this
      rw [P2.mk_eq_mk']
      use p 2
      ext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
        field_simp
        linear_combination this
      · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, Matrix.cons_val_one,
          Matrix.cons_val_zero, smul_eq_mul]
        suffices p 1 * q 1 * cf.u * 2 = -(p 2 * q 0 * (cf.u ^ 2 - cf.r ^ 2)) by
          field_simp
          linear_combination this
        rw [hpq']
        linear_combination -q 0 * this
      · simp
  by_cases hq1 : q 1 = 0
  · by_cases hy0 : ((q 2 - cf.u * q 0) ^ 2 - cf.r ^ 2 * q 0 ^ 2) = 0
    · suffices {pq ∈ dom cf | pq.2 = P2.mk _ hq} ⊆
          {⟨P2.mk ![1, 0, q 0 / q 2] (by simp), P2.mk _ hq⟩} by
        apply (Set.encard_mono this).trans
        simp
      intro pq h
      obtain ⟨p, q'⟩ := pq
      obtain ⟨hpq, rfl⟩ : ⟨p, q'⟩ ∈ dom cf ∧ q' = P2.mk q hq := by simpa using h
      induction p with | mk p hp
      rw [mem_dom] at hpq
      obtain ⟨ho, hi, hpq⟩ := hpq
      rw [hq1] at hi hpq
      have hq02 : q 0 ^ 2 = q 2 ^ 2 := by simpa using hi
      have hq2ne0 : q 2 ≠ 0 := by
        by_contra! hq2
        suffices q = 0 from hq this
        ext i
        fin_cases i
        · simpa [hq2] using hq02
        · simpa using hq1
        · simpa using hq2
      have hp02 : p 2 = q 0 * p 0 / q 2 := by
        field_simp
        linear_combination -hpq
      suffices P2.mk p hp = P2.mk ![1, 0, q 0 / q 2] _ by simpa
      rw [P2.mk_eq_mk']
      use p 0
      ext i
      fin_cases i
      · simp
      · have : ((q 2 - cf.u * q 0) ^ 2 - cf.r ^ 2 * q 0 ^ 2) * p 0 ^ 2 + q 2 ^ 2 * p 1 ^ 2 = 0 := by
          rw [hp02] at ho
          field_simp at ho
          linear_combination ho
        simpa [hy0, hq2ne0] using this
      · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, Matrix.cons_val, smul_eq_mul]
        field_simp
        linear_combination -hpq
    let poly : Polynomial K := Polynomial.C ((q 2 - cf.u * q 0) ^ 2 - cf.r ^ 2 * q 0 ^ 2)
        * Polynomial.X ^ 2 + Polynomial.C (q 2 ^ 2)
    suffices {pq ∈ dom cf | pq.2 = P2.mk _ hq} ⊆
      (fun x ↦ ⟨P2.mk ![x, 1, q 0 * x / q 2] (by simp), P2.mk _ hq⟩) '' poly.roots.toFinset by
      apply (Set.encard_mono this).trans
      grw [Set.encard_image_le]
      rw [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le_ofNat]
      grw [Multiset.toFinset_card_le]
      grw [Polynomial.card_roots']
      unfold poly
      rw [Polynomial.natDegree_add_C]
      grw [Polynomial.natDegree_C_mul_le]
      simp
    intro pq h
    obtain ⟨p, q'⟩ := pq
    obtain ⟨hpq, rfl⟩ : ⟨p, q'⟩ ∈ dom cf ∧ q' = P2.mk q hq := by simpa using h
    induction p with | mk p hp
    rw [mem_dom] at hpq
    obtain ⟨ho, hi, hpq⟩ := hpq
    rw [hq1] at hi hpq
    have hq02 : q 0 ^ 2 = q 2 ^ 2 := by simpa using hi
    have hq2ne0 : q 2 ≠ 0 := by
      by_contra! hq2
      suffices q = 0 from hq this
      ext i
      fin_cases i
      · simpa [hq2] using hq02
      · simpa using hq1
      · simpa using hq2
    have hpoly : poly ≠ 0 := by
      contrapose! hq2ne0 with h
      unfold poly at h
      simpa [-map_pow] using congr(Polynomial.coeff $h 0)
    have hp02 : p 2 = q 0 * p 0 / q 2 := by
      field_simp
      linear_combination -hpq
    suffices ∃ x, Polynomial.eval x poly = 0 ∧ P2.mk ![x, 1, q 0 * x / q 2] _ = P2.mk p hp by
      simpa [hpoly]
    have : ((q 2 - cf.u * q 0) ^ 2 - cf.r ^ 2 * q 0 ^ 2) * p 0 ^ 2 + q 2 ^ 2 * p 1 ^ 2 = 0 := by
        rw [hp02] at ho
        field_simp at ho
        linear_combination ho
    have hp1ne0 : p 1 ≠ 0 := by
      by_contra! hp1
      have hp0 : p 0 = 0 := by simpa [hy0, hp1] using this
      suffices p = 0 from hp this
      ext i
      fin_cases i
      · simpa using hp0
      · simpa using hp1
      · simpa [hp0] using hp02
    use p 0 / p 1
    constructor
    · suffices ((q 2 - cf.u * q 0) ^ 2 - cf.r ^ 2 * q 0 ^ 2) * (p 0 / p 1) ^ 2 + q 2 ^ 2 = 0 by
        simpa [poly]
      field_simp
      linear_combination this
    · symm
      rw [P2.mk_eq_mk']
      use p 1
      ext i
      fin_cases i
      · simp [field]
      · simp
      · simp [hp02, field]
  let poly : Polynomial K := Polynomial.C (q 0 ^ 2 + q 1 ^ 2) * Polynomial.X ^ 2
    - Polynomial.C (2 * cf.u * q 1 ^ 2 + 2 * q 0 * q 2) * Polynomial.X
    + Polynomial.C ((cf.u ^ 2 - cf.r ^ 2) * q 1 ^ 2 + q 2 ^ 2)
  suffices {pq ∈ dom cf | pq.2 = P2.mk _ hq} ⊆
    (fun x ↦ ⟨P2.mk ![x, (q 2 - q 0 * x) / q 1, 1] (by simp), P2.mk _ hq⟩) '' poly.roots.toFinset by
    apply (Set.encard_mono this).trans
    grw [Set.encard_image_le]
    rw [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le_ofNat]
    grw [Multiset.toFinset_card_le]
    grw [Polynomial.card_roots']
    unfold poly
    rw [Polynomial.natDegree_add_C]
    grw [Polynomial.natDegree_sub_le]
    apply max_le
    · grw [Polynomial.natDegree_C_mul_le]
      simp
    · grw [Polynomial.natDegree_C_mul_le]
      simp
  intro pq h
  obtain ⟨p, q'⟩ := pq
  obtain ⟨hpq, rfl⟩ : ⟨p, q'⟩ ∈ dom cf ∧ q' = P2.mk q hq := by simpa using h
  induction p with | mk p hp
  rw [mem_dom] at hpq
  obtain ⟨ho, hi, hpq⟩ := hpq
  have hpoly : poly ≠ 0 := by
    by_contra! hpoly
    unfold poly at hpoly
    have ha : q 0 ^ 2 + q 1 ^ 2 = 0 := by
      simpa [-map_add] using congr(Polynomial.coeff $hpoly 2)
    have hb : 2 * cf.u * q 1 ^ 2 + 2 * q 0 * q 2 = 0 := by
      set guard := 2 * cf.u * q 1 ^ 2 + 2 * q 0 * q 2
      simpa [-map_add] using congr(Polynomial.coeff $hpoly 1)
    have hc : (cf.u ^ 2 - cf.r ^ 2) * q 1 ^ 2 + q 2 ^ 2 = 0 := by
      simpa [-map_add] using congr(Polynomial.coeff $hpoly 0)
    have hq2 : q 2 = 0 := by
      simpa [ha] using hi.symm
    have hq1 : q 1 = 0 := by simpa [hq2, cf.hu, hchar.out] using hb
    suffices q = 0 from hq this
    ext i
    fin_cases i
    · simpa [hq1] using ha
    · simpa using hq1
    · simpa using hq2
  have hp2 : p 2 ≠ 0 := by
    contrapose! hp2
    have hqeq : ![p 0, p 1, 0] = p := by
      ext i
      fin_cases i
      · simp
      · simp
      · simpa using hp2.symm
    refine ⟨p 0, p 1, ?_, ?_⟩
    · convert hp
    · convert h
  suffices ∃ x, Polynomial.eval x poly = 0 ∧ P2.mk ![x, (q 2 - q 0 * x) / q 1, 1] _ = P2.mk p hp by
    simpa [hpoly]
  use p 0 / p 2
  constructor
  · have hpq : p 1 * q 1 = p 2 * q 2 - p 0 * q 0 := by linear_combination hpq
    suffices (q 0 ^ 2 + q 1 ^ 2) * (p 0 / p 2) ^ 2 -
        (2 * cf.u * q 1 ^ 2 + 2 * q 0 * q 2) * (p 0 / p 2) +
        ((cf.u ^ 2 - cf.r ^ 2) * q 1 ^ 2 + q 2 ^ 2) = 0 by
      simpa [poly]
    field_simp
    linear_combination q 1 ^ 2 * ho - congr($hpq ^ 2)
  · symm
    rw [P2.mk_eq_mk']
    use p 2
    ext i
    fin_cases i
    · simp [field]
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
        smul_eq_mul]
      field_simp
      linear_combination hpq
    · simp


/-- Reflect the vertex across the edge, expressed in raw coordinates. -/
def rPoint' [DecidableEq K] (p q : Fin 3 → K) : Fin 3 → K :=
  if q 2 = 0 then
    if p 2 = 0 then
      ![-(cf.r ^ 2 - cf.u ^ 2) * q 1, (cf.r ^ 2 - cf.u ^ 2) * q 0, 2 * cf.u * q 1]
    else
      ![q 1, -q 0, 0]
  else
    ![2 * q 0 * p 2 * q 2 + 2 * cf.u * q 1 ^ 2 * p 2 - p 0 * q 2 ^ 2,
      2 * q 1 * p 2 * q 2 - 2 * cf.u * q 0 * q 1 * p 2 - p 1 * q 2 ^ 2,
      p 2 * q 2 ^ 2]

theorem rPoint'_rPoint' [DecidableEq K] [hchar : NeZero (2 : K)]
    {p q : Fin 3 → K} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf) :
    ∃ l : K, rPoint' cf (rPoint' cf p q) q = l • p := by
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp h
  unfold rPoint'
  by_cases! hq2 : q 2 = 0
  · by_cases hp2 : p 2 = 0
    · have hq1 : q 1 ≠ 0 := by
        by_contra! hq1
        have : q 0 = 0 := by simpa [hq2, hq1] using hi
        clear h
        contrapose! hq
        ext n; fin_cases n <;> assumption
      have hp0 : p 0 ≠ 0 := by
        by_contra! hp0
        have : p 1 = 0 := by simpa [hp0, hp2, hq1] using hpq
        clear h
        contrapose! hp
        ext n; fin_cases n <;> assumption
      use q 1 / p 0
      ext n
      fin_cases n
      · suffices q 1 = q 1 / p 0 * p 0 by simpa [hp2, hq2, cf.hu, hq1, hchar.out]
        grind
      · suffices -q 0 = q 1 / p 0 * p 1 by simpa [hp2, hq2, cf.hu, hq1, hchar.out]
        grind
      · simp [hp2, hq2, cf.hu, hq1, hchar.out]
    · use 2 * cf.u * q 1 / p 2
      ext n
      fin_cases n
      · suffices (cf.u ^ 2 - cf.r ^ 2) * q 1 = 2 * cf.u * q 1 / p 2 * p 0 by simpa [hp2, hq2]
        grind
      · suffices (cf.r ^ 2 - cf.u ^ 2) * q 0 = 2 * cf.u * q 1 / p 2 * p 1 by simpa [hp2, hq2]
        grind
      · simp [hp2, hq2]
  use q 2 ^ 4
  ext n
  fin_cases n
  all_goals
  simp [hq2]
  ring

theorem rPoint'_ne_zero [DecidableEq K] [hchar : NeZero (2 : K)]
    {p q : Fin 3 → K} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf) : rPoint' cf p q ≠ 0 := by
  unfold rPoint'
  by_contra! h0
  by_cases! hq2 : q 2 = 0
  · by_cases! hp2 : p 2 = 0
    · obtain ⟨_, _, hq1⟩ : _ ∧ _ ∧ q 1 = 0 := by simpa [cf.hu, hp2, hq2, hchar.out] using h0
      have hq0 : q 0 = 0 := by simpa [hq1, hq2] using (mem_dom cf hp hq |>.mp hpq).2.1
      clear hpq
      contrapose! hq
      ext n; fin_cases n <;> assumption
    · obtain ⟨hq1, hq0⟩ : q 1 = 0 ∧ q 0 = 0 := by simpa [hp2, hq2] using h0
      clear hpq
      contrapose! hq
      ext n; fin_cases n <;> assumption
  · by_cases! hp2 : p 2 = 0
    · obtain ⟨hp0, hp1⟩ : p 0 = 0 ∧ p 1 = 0 := by simpa [hp2, hq2] using h0
      clear hpq
      contrapose! hp
      ext n; fin_cases n <;> assumption
    · simp [hp2, hq2] at h0

theorem rPoint'_eq_self [DecidableEq K] [hchar : NeZero (2 : K)]
    {p q : Fin 3 → K} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf) :
    (∃ l : K, rPoint' cf p q = l • p) ↔
    2 * cf.u * q 0 * q 2 + cf.u ^ 2 * q 1 ^ 2 = (1 + cf.u ^ 2 - cf.r ^ 2) * q 2 ^ 2 := by
  obtain ⟨ho, hi, heq⟩ := mem_dom cf hp hq |>.mp h
  clear h
  simp only [rPoint', neg_sub]
  obtain _ := cf.hr
  obtain _ := cf.hu
  obtain _ := hchar.out
  have hq : q 0 = 0 → q 1 = 0 → q 2 ≠ 0 := by simpa [funext_iff, Fin.forall_fin_succ] using hq
  have hp : p 0 = 0 → p 1 = 0 → p 2 ≠ 0 := by simpa [funext_iff, Fin.forall_fin_succ] using hp
  by_cases hq2 : q 2 = 0;
  · by_cases hp2 : p 2 = 0
    · suffices (∃ l, ![(cf.u ^ 2 - cf.r ^ 2) * q 1,
          (cf.r ^ 2 - cf.u ^ 2) * q 0, 2 * cf.u * q 1] = l • p) ↔ cf.u = 0 ∨ q 1 = 0 by
        simpa [hp2, hq2]
      suffices (∃ l, (cf.u ^ 2 - cf.r ^ 2) * q 1 = l * p 0 ∧
          (cf.r ^ 2 - cf.u ^ 2) * q 0 = l * p 1 ∧ 2 * cf.u * q 1 = l * p 2) ↔
          cf.u = 0 ∨ q 1 = 0 by
        simpa [funext_iff, Fin.forall_fin_succ]
      grind
    · suffices (∃ l, ![q 1, -q 0, 0] = l • p) ↔ cf.u = 0 ∨ q 1 = 0 by
        simpa [hq2, hp2]
      suffices (∃ l, q 1 = l * p 0 ∧ -q 0 = l * p 1 ∧ (l = 0 ∨ p 2 = 0)) ↔ cf.u = 0 ∨ q 1 = 0 by
        simpa [funext_iff, Fin.forall_fin_succ]
      grind
  · suffices (∃ l,
      2 * q 0 * p 2 * q 2 + 2 * cf.u * q 1 ^ 2 * p 2 - p 0 * q 2 ^ 2 = l * p 0 ∧
      2 * q 1 * p 2 * q 2 - 2 * cf.u * q 0 * q 1 * p 2 - p 1 * q 2 ^ 2 = l * p 1 ∧
      p 2 * q 2 ^ 2 = l * p 2) ↔
      2 * cf.u * q 0 * q 2 + cf.u ^ 2 * q 1 ^ 2 = (1 + cf.u ^ 2 - cf.r ^ 2) * q 2 ^ 2 by
      simpa [hq2, funext_iff, Fin.forall_fin_succ]
    constructor <;> intro h
    · by_cases hp2: p 2 = 0
      · have hp0: p 0 = 0 := by
          grind
        grind
      · obtain ⟨l, hl⟩ := h
        grind
    · exact ⟨q 2 ^ 2, (by grind), (by grind), (by ring)⟩

/-- Reflect the vertex across the edge. -/
def rPoint [DecidableEq K] (pq : P2 K × P2 K) : P2 K × P2 K :=
  ⟨P2.lift₂ (fun p q hp hq ↦ P2.mk' (rPoint' cf p q)) (by
  intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
  unfold rPoint'
  have hp2 : p' 2 = 0 ↔ p 2 = 0 := by aesop
  have hq2 : q' 2 = 0 ↔ q 2 = 0 := by aesop
  simp_rw [hp2, hq2]
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

theorem rPoint_eq_of_r_eq_neg [DecidableEq K] (cf' : Config K)
    (hu : cf'.u = cf.u) (hr : cf'.r = -cf.r) :
    rPoint cf = rPoint cf' := by
  ext1
  simp_rw [rPoint, rPoint', hu, hr, neg_sq]

theorem snd_rPoint [DecidableEq K] (pq : P2 K × P2 K) :
    (rPoint cf pq).2 = pq.2 := rfl

theorem IsAffine_rPoint [DecidableEq K] {pq : P2 K × P2 K}
    (hp : pq.1.IsAffine)
    (hq : pq.2.IsAffine) :
    (rPoint cf pq).1.IsAffine := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp'
  induction q with | mk q hq'
  have hp2 : p 2 ≠ 0 := by simpa [P2.IsAffine] using hp
  have hq2 : q 2 ≠ 0 := by simpa [P2.IsAffine] using hq
  simp [rPoint, rPoint', P2.IsAffine, hq2, P2.mk', hp2]

theorem rPoint_mk [DecidableEq K] [hchar : NeZero (2 : K)]
    {p q : Fin 3 → K} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf) :
    rPoint cf ⟨P2.mk p hp, P2.mk q hq⟩ =
    ⟨P2.mk (rPoint' cf p q) (rPoint'_ne_zero cf hp hq hpq), P2.mk q hq⟩ := by
  simp [rPoint, rPoint'_ne_zero cf hp hq hpq]

theorem mapsTo_rPoint [DecidableEq K] [hchar : NeZero (2 : K)] :
    Set.MapsTo (rPoint cf) (dom cf) (dom cf) := by
  intro ⟨p, q⟩ hpq
  induction p with | mk p hp
  induction q with | mk q hq
  rw [rPoint_mk cf hp hq hpq]
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
  rw [mem_dom]
  simp_rw [rPoint']
  split_ifs
  all_goals
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val]
  grind

theorem rPoint_rPoint [DecidableEq K] [hchar : NeZero (2 : K)]
    {pq : P2 K × P2 K} (hpq : pq ∈ dom cf) :
    rPoint cf (rPoint cf pq) = pq := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain hmem := mapsTo_rPoint cf hpq
  rw [rPoint_mk cf hp hq hpq] at ⊢ hmem
  rw [rPoint_mk cf _ _ hmem]
  refine Prod.ext_iff.mpr ⟨?_, rfl⟩
  rw [P2.mk_eq_mk']
  exact rPoint'_rPoint' cf hp hq hpq

theorem rPoint_bijOn [DecidableEq K] [hchar : NeZero (2 : K)] :
    Set.BijOn (rPoint cf) (dom cf) (dom cf) := by
  refine ⟨mapsTo_rPoint cf, ?_, ?_⟩
  · intro p hp q hq h
    simpa [rPoint_rPoint, cf.hu, hp, hq] using congr(rPoint cf $h)
  · intro p hp
    exact ⟨rPoint cf p, mapsTo_rPoint cf hp, rPoint_rPoint cf hp⟩

theorem rPoint_eq_self [DecidableEq K] [hchar : NeZero (2 : K)]
    {pq : P2 K × P2 K} (h : pq ∈ dom cf) :
    rPoint cf (pq) = pq ↔ TangentOuterCircle cf pq.2 := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp h
  simp only
  simp [rPoint,
      tangentOuterCircle_iff cf (P2.mk q hq) (by simpa [InnerCircle] using hi),
      P2.mk'_eq (rPoint'_ne_zero cf hp hq h),
    P2.mk_eq_mk' _ _, rPoint'_eq_self cf hp hq h]

/-- Reflect the edge across the vertex, expressed in raw coordinates. -/
def rChord' [DecidableEq K] (p q : Fin 3 → K) : Fin 3 → K :=
  if 2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2 = 0 then -- all sorts of edge cases
    if p 0 = 0 then
      ![q 0, - q 1, q 2]
    else if q 2 = 0 then
      ![p 1 * (p 2 ^ 2 - p 1 ^ 2), p 0 * (p 2 ^ 2 + p 1 ^ 2), 2 * p 0 * p 1 * p 2]
    else
      ![p 1, -p 0, 0]
  else -- the only part I had on my notebook
    ![2 * p 0 * q 2 - (2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2) * q 0,
      2 * p 1 * q 2 - (2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2) * q 1,
      (2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2) * q 2]

theorem rChord'_ne_zero [DecidableEq K] [hchar : NeZero (2 : K)]
    {p q : Fin 3 → K} (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf) : rChord' cf p q ≠ 0 := by
  obtain _ := cf.hu
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp h
  unfold rChord'
  by_cases! hxy : 2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2 = 0
  · have h0' : p 0 ^ 2 + p 1 ^ 2 = 0 := by linear_combination ho + p 2 * hxy
    simp_rw [hxy]
    by_cases! hp0 : p 0 = 0
    · suffices q 0 = 0 → q 1 = 0 → q 2 ≠ 0 by simpa [hp0]
      intro hq2 hq0
      clear h
      contrapose! hq with hq1
      ext n; fin_cases n <;> assumption
    have hp1 : p 1 ≠ 0 := by
      contrapose! hp0
      simpa [hp0] using h0'
    have hp2 : p 2 ≠ 0 := by
      contrapose! hp0
      simpa [hp0, cf.hu, hchar.out] using hxy
    by_cases! hq2 : q 2 = 0
    · simp [hp0, hq2, hp1, hp2, hchar.out]
    · simp [hp0, hq2]
  by_cases! hq2 : q 2 = 0
  · suffices q 0 = 0 → q 1 ≠ 0 by simpa [hxy, hq2]
    intro hq2 hq0
    clear h
    contrapose! hq with hq1
    ext n; fin_cases n <;> assumption
  simp [hxy, hq2]

theorem rChord'_rChord' [DecidableEq K] [hchar : NeZero (2 : K)] {p q : Fin 3 → K}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf) :
    ∃ l : K, rChord' cf p (rChord' cf p q) = l • q := by
  obtain _ := cf.hu
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp h
  unfold rChord'
  by_cases h0 : 2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2 = 0
  · have h0' : p 0 ^ 2 + p 1 ^ 2 = 0 := by linear_combination ho + p 2 * h0
    simp_rw [h0]
    by_cases! hp0 : p 0 = 0
    · use 1
      ext n
      fin_cases n
      all_goals
      simp [hp0]
    have hp1 : p 1 ≠ 0 := by
      contrapose! hp0
      simpa [hp0] using h0'
    have hp2 : p 2 ≠ 0 := by
      contrapose! hp0
      simpa [hp0, cf.hu, hchar.out] using h0
    by_cases! hq2 : q 2 = 0
    · have hp2 : p 2 ≠ 0 := by grind
      have hq12 : p 0 * q 0 + p 1 * q 1 = 0 := by simpa [hq2] using hpq
      suffices ∃ l, ![p 1, -p 0, 0] = l • q by simpa [hp0, hq2, hp2, hp1, hchar.out]
      have hq0 : q 0 ≠ 0 := by
        clear h
        contrapose! hq with hq0
        have hq1 : q 1 = 0 := by simpa [hq0, hp1] using hq12
        ext n; fin_cases n <;> assumption
      use p 1 / q 0
      ext n
      fin_cases n
      · simp [hq0]
      · simp
        grind
      · simp [hq2]
    use 2 * p 0 * p 1 * p 2 / q 2
    ext n
    fin_cases n
    · simp [hp0, hq2]
      grind
    · simp [hp0, hq2]
      grind
    · simp [hp0, hq2]
  · use (2 * cf.u * p 0 + (cf.r ^ 2) * p 2 - cf.u ^ 2 * p 2) ^ 2
    ext n
    fin_cases n
    all_goals
    simp [h0]
    ring

theorem rChord'_eq_self_special [DecidableEq K] [hchar : NeZero (2 : K)] {p q : Fin 3 → K}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf)
    (hxy : 2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2 = 0) :
    (∃ l : K, rChord' cf p q = l • q) ↔ p 0 ^ 2 + p 1 ^ 2 = p 2 ^ 2 := by
  obtain _ := hchar.out
  obtain ⟨ho, hi, heq⟩ := mem_dom cf hp hq |>.mp h
  clear h
  simp only [rChord', hxy, ↓reduceIte]
  by_cases hp0 : p 0 = 0
  · suffices (∃ l, q 0 = l * q 0 ∧ -q 1 = l * q 1 ∧ q 2 = l * q 2) ↔ p 1 ^ 2 = p 2 ^ 2 by
      simpa [hp0, funext_iff, Fin.forall_fin_succ]
    constructor
    · rintro ⟨l, ⟨h0, h1, h2⟩⟩
      by_cases hq1 : q 1 = 0
      · have heq : p 0 * q 0 = p 2 * q 2 := by simpa [hq1] using heq
        have : q 0 ^ 2 = q 2 ^ 2 := by simpa [hq1] using hi
        have hq2 : q 2 ≠ 0 := by
          contrapose! hq with hq2
          ext i
          fin_cases i
          · simpa [hq2] using this
          · exact hq1
          · exact hq2
        obtain h | h := eq_or_eq_neg_of_sq_eq_sq _ _ this
        · grind
        · grind
      · grind
    · intro h
      have hp2 : p 2 ≠ 0 := by
        contrapose! hp with hp2
        ext i
        fin_cases i
        · exact hp0
        · simpa [hp2] using h
        · exact hp2
      obtain h | h := eq_or_eq_neg_of_sq_eq_sq _ _ h
      · grind
      · grind
  · by_cases hq2 : q 2 = 0
    · simp only [hp0, hq2, ↓reduceIte]
      constructor
      · rintro ⟨l, hl⟩
        obtain ⟨h0, h1, h2⟩ : p 1 * (p 2 ^ 2 - p 1 ^ 2) = l * q 0 ∧
            p 0 * (p 2 ^ 2 + p 1 ^ 2) = l * q 1 ∧
            2 * p 0 * p 1 * p 2 = l * q 2 := by
          simpa [funext_iff, Fin.forall_fin_succ] using hl
        grind
      · intro h
        suffices ∃ l, p 1 * (p 2 ^ 2 - p 1 ^ 2) = l * q 0 ∧
            p 0 * (p 2 ^ 2 + p 1 ^ 2) = l * q 1 ∧
            2 * p 0 * p 1 * p 2 = l * q 2 by
          simpa [funext_iff, Fin.forall_fin_succ]
        have hq0 : q 0 ≠ 0 := by
          contrapose! hq
          ext i
          fin_cases i
          · exact hq
          · simpa [hq, hq2] using hi
          · exact hq2
        refine ⟨p 1 * (p 2 ^ 2 - p 1 ^ 2) / q 0, ?_, ?_, ?_⟩
        · field
        · field_simp
          grind
        · field_simp
          grind
    · simp only [hp0, hq2, ↓reduceIte]
      suffices (∃ l, p 1 = l * q 0 ∧ -p 0 = l * q 1 ∧ (l = 0 ∨ q 2 = 0))
          ↔ p 0 ^ 2 + p 1 ^ 2 = p 2 ^ 2 by
        simpa [funext_iff, Fin.forall_fin_succ]
      grind

theorem rChord'_eq_self_normal [DecidableEq K] [hchar : NeZero (2 : K)] {p q : Fin 3 → K}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf)
    (hxy : 2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2 ≠ 0) :
    (∃ l : K, rChord' cf p q = l • q) ↔ p 0 ^ 2 + p 1 ^ 2 = p 2 ^ 2 := by
  obtain _ := hchar.out
  obtain ⟨ho, hi, heq⟩ := mem_dom cf hp hq |>.mp h
  clear h
  simp only [rChord', hxy, ↓reduceIte]
  by_cases h_case2 : p 0 ^ 2 + p 1 ^ 2 = p 2 ^ 2;
  · simp only [h_case2, iff_true]
    use 2 * p 2 - (2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2)
    ext i
    fin_cases i
    · simp
      grind
    · simp
      grind
    · simp
      grind
  · simp only [h_case2, iff_false]
    simp_rw [funext_iff, Fin.forall_fin_succ]
    by_contra! h
    obtain ⟨l, hl⟩ := h
    by_cases hq2 : q 2 = 0
    · by_cases hq0 : q 0 = 0
      · by_cases hq1 : q 1 = 0
        · contrapose! hq
          ext i
          fin_cases i <;> assumption
        simp at hl
        grind
      simp at hl
      grind
    simp at hl
    grind

theorem rChord'_eq_self [DecidableEq K] [hchar : NeZero (2 : K)] {p q : Fin 3 → K}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (h : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf) :
    (∃ l : K, rChord' cf p q = l • q) ↔ p 0 ^ 2 + p 1 ^ 2 = p 2 ^ 2 := by
  by_cases! hxy : 2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2 = 0
  · exact rChord'_eq_self_special cf hp hq h hxy
  · exact rChord'_eq_self_normal cf hp hq h hxy

/-- Reflect the edge across the vertex. -/
def rChord [DecidableEq K] (pq : P2 K × P2 K) : P2 K × P2 K :=
  ⟨pq.1, P2.lift₂ (fun p q hp hq ↦ P2.mk' (rChord' cf p q)) (by
    intro p q p' q' hp hq hp' hq' ⟨l, hl0, hl⟩ ⟨m, hm0, hm⟩
    unfold rChord'
    have hxy : 2 * cf.u * p' 0 + cf.r ^ 2 * p' 2 - cf.u ^ 2 * p' 2 = 0 ↔
        2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2 = 0 := by
      rw [hl]
      conv_lhs =>
        rw [← mul_left_inj' hl0]
      congrm ?_ = ?_
      · simp only [Pi.smul_apply, smul_eq_mul]
        ring
      · simp
    have hp0 : p' 0 = 0 ↔ p 0 = 0 := by aesop
    have hq2 : q' 2 = 0 ↔ q 2 = 0 := by aesop
    simp_rw [hxy, hp0, hq2]
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

theorem rChord_eq_of_r_eq_neg [DecidableEq K] (cf' : Config K)
    (hu : cf'.u = cf.u) (hr : cf'.r = -cf.r) :
    rChord cf = rChord cf':= by
  ext1
  simp_rw [rChord, rChord', hu, hr, neg_sq]

theorem fst_rChord [DecidableEq K] (pq : P2 K × P2 K) :
    (rChord cf pq).1 = pq.1 := rfl

theorem isAffineLine_rChord [DecidableEq K] {pq : P2 K × P2 K}
    (hpq : pq ∈ dom cf)
    (hq : pq.2.IsAffineLine)
    (hqPoint : pq.2.IsAffine):
    (rChord cf pq).2.IsAffineLine := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp'
  induction q with | mk q hq'
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp' hq' |>.mp hpq
  have hq2 : q 2 ≠ 0 := by simpa [P2.IsAffine] using hqPoint
  by_cases h0 : rChord' cf p q = 0
  · suffices P2.mk ![(1 : K), 0, 0] _ ≠ P2.mk ![0, 0, 1] _ by
      simpa [rChord, P2.IsAffineLine, P2.mk', h0]
    by_contra! h
    rw [P2.mk_eq_mk] at h
    obtain ⟨l, hl0, hl⟩ := h
    simpa [hl0] using congr($hl 2).symm
  suffices P2.mk (rChord' cf p q) _ ≠ P2.mk ![0, 0, 1] _ by
    simpa [rChord, P2.IsAffineLine, P2.mk', h0]
  unfold rChord'
  by_cases hs : 2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2 = 0
  · simp only [hs, ↓reduceIte]
    by_cases hp0 : p 0 = 0
    · simp only [hp0, ↓reduceIte]
      contrapose! hq
      simp only [P2.IsAffineLine, Decidable.not_not]
      rw [P2.mk_eq_mk'] at hq ⊢
      obtain ⟨l, hl⟩ := hq
      use l
      ext i
      fin_cases i
      · simpa using congr($hl 0)
      · simpa using congr($hl 1)
      · simpa using congr($hl 2)
    suffices P2.mk ![p 1, -p 0, 0] _ ≠ P2.mk ![0, 0, 1] _ by
      simpa [hp0, hq2]
    by_contra! h
    rw [P2.mk_eq_mk] at h
    obtain ⟨l, hl0, hl⟩ := h
    simpa [hl0] using congr($hl 2).symm
  · simp only [hs, ↓reduceIte]
    by_contra! h
    rw [P2.mk_eq_mk'] at h
    obtain ⟨l, h⟩ := h
    have hx : 2 * p 0 * q 2 - (2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2) * q 0 = 0 := by
      simpa using congr($h 0)
    have hx : 2 * p 1 * q 2 - (2 * cf.u * p 0 + cf.r ^ 2 * p 2 - cf.u ^ 2 * p 2) * q 1 = 0 := by
      simpa using congr($h 1)
    grind

theorem rChord_mk [DecidableEq K] [hchar : NeZero (2 : K)] {p q : Fin 3 → K}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : ⟨P2.mk p hp, P2.mk q hq⟩ ∈ dom cf) :
    rChord cf ⟨P2.mk p hp, P2.mk q hq⟩ =
    ⟨P2.mk p hp, P2.mk (rChord' cf p q) (rChord'_ne_zero cf hp hq hpq)⟩ := by
  simp [rChord, rChord'_ne_zero cf hp hq hpq]

theorem mapsTo_rChord [DecidableEq K] [hchar : NeZero (2 : K)] :
    Set.MapsTo (rChord cf) (dom cf) (dom cf) := by
  intro ⟨p, q⟩ hpq
  induction p with | mk p hp
  induction q with | mk q hq
  rw [rChord_mk cf hp hq hpq]
  obtain ⟨ho, hi, hpq⟩ := mem_dom cf hp hq |>.mp hpq
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

theorem rChord_rChord [DecidableEq K] [hchar : NeZero (2 : K)]
    {pq : P2 K × P2 K} (hpq : pq ∈ dom cf) :
    rChord cf (rChord cf pq) = pq := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  obtain hmem := mapsTo_rChord cf hpq
  rw [rChord_mk cf hp hq hpq] at ⊢ hmem
  rw [rChord_mk cf _ _ hmem]
  refine Prod.ext_iff.mpr ⟨rfl, ?_⟩
  rw [P2.mk_eq_mk']
  exact rChord'_rChord' cf hp hq hpq

theorem rChord_bijOn [DecidableEq K] [hchar : NeZero (2 : K)] :
    Set.BijOn (rChord cf) (dom cf) (dom cf) := by
  refine ⟨mapsTo_rChord cf, ?_, ?_⟩
  · intro p hp q hq h
    simpa [rChord_rChord, cf.hu, hp, hq] using congr(rChord cf $h)
  · intro p hp
    exact ⟨rChord cf p, mapsTo_rChord cf hp, rChord_rChord cf hp⟩

theorem rChord_eq_self [DecidableEq K] [hchar : NeZero (2 : K)]
    {pq : P2 K × P2 K} (h : pq ∈ dom cf) :
    (rChord cf pq = pq) ↔ InnerCircle cf pq.1 := by
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  simp [rChord, InnerCircle, P2.mk'_eq (rChord'_ne_zero cf hp hq h),
    P2.mk_eq_mk' _ _, rChord'_eq_self cf hp hq h]

/-- Send a pair of vertex and edge to the next one on the polygon. -/
def next [DecidableEq K] (pq : P2 K × P2 K) : P2 K × P2 K :=
  rChord cf (rPoint cf pq)

theorem next_eq_of_r_eq_neg [DecidableEq K] (cf' : Config K)
    (hu : cf'.u = cf.u) (hr : cf'.r = -cf.r) :
    next cf = next cf' := by
  ext1
  simp_rw [next, rPoint_eq_of_r_eq_neg cf cf' hu hr,
    rChord_eq_of_r_eq_neg cf cf' hu hr]

theorem mapsTo_next [DecidableEq K] [hchar : NeZero (2 : K)] :
    Set.MapsTo (next cf) (dom cf) (dom cf) :=
  (mapsTo_rChord cf).comp (mapsTo_rPoint cf)

theorem next_bijOn [DecidableEq K] [hchar : NeZero (2 : K)] :
    Set.BijOn (next cf) (dom cf) (dom cf) :=
  (rChord_bijOn cf).comp (rPoint_bijOn cf)

theorem next_eq_self [DecidableEq K] [hchar : NeZero (2 : K)] {pq : P2 K × P2 K} (h : pq ∈ dom cf) :
    next cf (pq) = pq ↔ InnerCircle cf pq.1 ∧ TangentOuterCircle cf pq.2 := by
  rw [← rChord_eq_self cf h, ← rPoint_eq_self cf h]
  unfold next
  unfold rChord rPoint
  grind

theorem next_eq_self' [DecidableEq K] [hchar : NeZero (2 : K)]
    {pq : P2 K × P2 K} (h : pq ∈ dom cf) :
    next cf (pq) = pq ↔
    pq = ⟨P2.mk ![1, 0, 1] (by simp), P2.mk ![1, 0, 1] (by simp)⟩ ∨
    pq = ⟨P2.mk ![-1, 0, 1] (by simp), P2.mk ![-1, 0, 1] (by simp)⟩ := by
  obtain _ := cf.hu
  obtain _ := cf.hr
  obtain hchar := hchar.out
  have h4 : (4 : K) ≠ 0 := by
    suffices (2 * 2 : K) ≠ 0 by contrapose! this; linear_combination this
    simpa using hchar
  rw [next_eq_self cf h]
  obtain ⟨p, q⟩ := pq
  induction p with | mk p hp
  induction q with | mk q hq
  rw [mem_dom] at h
  obtain ⟨ho, hi, heq⟩ := h
  simp_rw [Prod.mk.injEq]
  rw [P2.mk_eq_mk', P2.mk_eq_mk', P2.mk_eq_mk', P2.mk_eq_mk']
  suffices InnerCircle cf (P2.mk p hp) ∧ TangentOuterCircle cf (P2.mk q hq) ↔
      (p 1 = 0 ∧ p 2 = p 0) ∧ q 1 = 0 ∧ q 2 = q 0 ∨
      (p 0 = -p 2 ∧ p 1 = 0) ∧ q 0 = -q 2 ∧ q 1 = 0 by
    simpa [P2.mk_eq_mk', funext_iff, Fin.forall_fin_succ]
  simp only [InnerCircle,
    tangentOuterCircle_iff cf (P2.mk q hq) (by simpa [InnerCircle] using hi), P2.lift_mk]
  constructor
  · rintro ⟨h1, h2⟩
    have hp2 : p 2 ≠ 0 := by
      contrapose! hq with hp2
      rw [hp2] at h1 heq
      rw [zero_pow (by simp), ← eq_neg_iff_add_eq_zero] at h1
      rw [zero_mul, ← eq_neg_iff_add_eq_zero] at heq
      have heq : p 0 ^ 2 * q 0 ^ 2 = p 1 ^ 2 * q 1 ^ 2 := by linear_combination congr($heq ^ 2)
      rw [h1, neg_mul_comm] at heq
      have : p 1 ^ 2 ≠ 0 := by
        contrapose! hp
        ext i
        fin_cases i
        · simpa [hp] using h1
        · simpa using hp
        · exact hp2
      rw [mul_right_inj' this] at heq
      have hq2 : q 2 = 0 := by simpa [← heq] using hi.symm
      have hq1 : q 1 = 0 := by simpa [hq2, cf.hu] using h2
      ext i
      fin_cases i
      · simpa [hq1] using heq
      · exact hq1
      · exact hq2
    have hq2 : q 2 ≠ 0 := by
      contrapose! hp2 with hq2
      rw [hq2] at hi heq
      rw [zero_pow (by simp), ← eq_neg_iff_add_eq_zero] at hi
      rw [mul_zero, ← eq_neg_iff_add_eq_zero] at heq
      have heq : p 0 ^ 2 * q 0 ^ 2 = p 1 ^ 2 * q 1 ^ 2 := by linear_combination congr($heq ^ 2)
      rw [hi, ← neg_mul_comm] at heq
      have : q 1 ^ 2 ≠ 0 := by
        contrapose! hq
        ext i
        fin_cases i
        · simpa [hq] using hi
        · simpa using hq
        · exact hq2
      rw [mul_left_inj' this] at heq
      simpa [← heq] using h1.symm
    have : p 2 * (2 * cf.u * p 0 - (1 - cf.r ^ 2 + cf.u ^ 2 ) * p 2) = 0 := by
      linear_combination h1 - ho
    have h : 2 * cf.u * p 0 - (1 - cf.r ^ 2 + cf.u ^ 2) * p 2 = 0 := by simpa [hp2] using this
    have hxz : p 0 = (1 - cf.r ^ 2 + cf.u ^ 2) * p 2 / (2 * cf.u) := by
      field_simp
      linear_combination h
    have hyz : p 1 ^ 2 = (1 - (cf.u - cf.r) ^ 2) * ((cf.u + cf.r) ^ 2 - 1) * p 2 ^ 2
        / (4 * cf.u ^ 2) := by
      rw [hxz] at ho
      field_simp at ho ⊢
      linear_combination ho
    have hby : q 1 ^ 2 * p 1 ^ 2 = (q 2 * p 2 - q 0 * p 0) ^ 2 := by
      rw [← mul_pow]
      congrm ?_ ^ 2
      linear_combination heq
    rw [hxz, hyz] at hby
    have hac : (cf.u * q 0 - q 2) ^ 2 = (cf.r * q 2) ^ 2 := by
      linear_combination -(h2 - cf.u ^ 2 * hi)
    obtain hac' | hac' := eq_or_eq_neg_of_sq_eq_sq _ _ hac
    · have hac : q 0 = (cf.r + 1) * q 2 / cf.u := by
        field_simp
        linear_combination hac'
      have hbc : q 1 ^ 2 = (cf.u ^ 2 - (cf.r + 1) ^ 2) * q 2 ^ 2 / cf.u ^ 2 := by
        rw [hac] at hi
        field_simp at hi ⊢
        linear_combination hi
      rw [hac, hbc] at hby
      field_simp at hby
      have : 4 * cf.u ^ 2 * ((cf.u - cf.r - 1) * (cf.u + cf.r + 1)) ^ 2 = 0 := by
        linear_combination -hby
      obtain hur | hur : cf.u - cf.r - 1 = 0 ∨ cf.u + cf.r + 1 = 0 := by
        simpa [cf.hu, h4] using this
      · have : cf.r = cf.u - 1 := by linear_combination -hur
        rw [this] at h hyz hac' hbc
        field_simp at hyz hbc
        grind
      · have : cf.r = -cf.u - 1 := by linear_combination hur
        rw [this] at h hyz hac' hbc
        field_simp at hyz hbc
        grind
    · have hac : q 0 = (-cf.r + 1) * q 2 / cf.u := by
        field_simp
        linear_combination hac'
      have hbc : q 1 ^ 2 = (cf.u ^ 2 - (-cf.r + 1) ^ 2) * q 2 ^ 2 / cf.u ^ 2 := by
        rw [hac] at hi
        field_simp at hi ⊢
        linear_combination hi
      rw [hac, hbc] at hby
      field_simp at hby
      have : 4 * cf.u ^ 2 * ((cf.u - cf.r + 1) * (cf.u + cf.r - 1)) ^ 2 = 0 := by
        linear_combination -hby
      obtain hur | hur : cf.u - cf.r + 1 = 0 ∨ cf.u + cf.r - 1 = 0 := by
        simpa [cf.hu, h4] using this
      · have : cf.r = cf.u + 1 := by linear_combination -hur
        rw [this] at h hyz hac' hbc
        field_simp at hyz hbc
        grind
      · have : cf.r = -cf.u + 1 := by linear_combination hur
        rw [this] at h hyz hac' hbc
        field_simp at hyz hbc
        grind
  · intro h
    obtain ⟨⟨hp1, hp2⟩, ⟨hq1, hq2⟩⟩ | ⟨⟨hp2, hp1⟩, ⟨hq2, hq1⟩⟩ := h
    · constructor
      · simp [hp1, hp2]
      · have hp0 : p 0 ≠ 0 := by
          contrapose! hp
          ext i
          fin_cases i
          · exact hp
          · exact hp1
          · exact hp2 ▸ hp
        grind
    · constructor
      · simp [hp1, hp2]
      · have hp0 : p 0 ≠ 0 := by
          contrapose! hp
          ext i
          fin_cases i
          · exact hp
          · exact hp1
          · simpa [hp] using hp2
        grind

/-- The non-singular part of `dom` -/
def dom₀ : Set (P2 K × P2 K) :=
  dom cf \
  {⟨P2.mk ![1, 0, 1] (by simp), P2.mk ![1, 0, 1] (by simp)⟩,
   ⟨P2.mk ![-1, 0, 1] (by simp), P2.mk ![-1, 0, 1] (by simp)⟩}

instance [DecidableEq K] : DecidablePred (· ∈ dom₀ cf) := by
  unfold dom₀
  infer_instance

theorem dom₀_eq_of_r_eq_neg (cf' : Config K)
    (hu : cf'.u = cf.u) (hr : cf'.r = -cf.r) :
    dom₀ cf = dom₀ cf' := by
  simp_rw [dom₀, dom_eq_of_r_eq_neg cf cf' hu hr]

theorem mem_dom₀ {pq : P2 K × P2 K} :
    pq ∈ dom₀ cf ↔ pq ∈ dom cf ∧
    pq ≠ ⟨P2.mk ![1, 0, 1] (by simp), P2.mk ![1, 0, 1] (by simp)⟩ ∧
    pq ≠ ⟨P2.mk ![-1, 0, 1] (by simp), P2.mk ![-1, 0, 1] (by simp)⟩ := by
  simp [dom₀]

theorem mem_dom₀' {pq : P2 K × P2 K} :
    pq ∈ dom₀ cf ↔ pq ∈ dom cf ∧
    pq.1 ≠ P2.mk ![1, 0, 1] (by simp) ∧
    pq.1 ≠ P2.mk ![-1, 0, 1] (by simp) := by
  simp_rw [dom₀, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  by_cases hmem : pq ∈ dom cf
  · congrm(_ ∧ ?_ ∧ ?_)
    · contrapose!
      refine ⟨by grind, fun h ↦ ?_⟩
      ext
      · exact h
      obtain ⟨p, q⟩ := pq
      induction p with | mk p hp
      induction q with | mk q hq
      obtain ⟨l, hl0, hl⟩ := (P2.mk_eq_mk _ _).mp h
      have hp02 : p 0 = p 2 := by
        trans l
        · simpa using congr($hl 0)
        · simpa using congr($hl 2).symm
      have hp1 : p 1 = 0 := by simpa using congr($hl 1)
      have hp2 : p 2 ≠ 0 := by
        by_contra! hp2
        suffices p = 0 from hp this
        ext i
        fin_cases i
        · exact hp02.trans hp2
        · exact hp1
        · exact hp2
      obtain ⟨ho, hi, hpq⟩ := (mem_dom _ _ _).mp hmem
      have hq02 : q 0 = q 2 := by simpa [hp02, hp1, hp2] using hpq
      simp only
      rw [P2.mk_eq_mk']
      use q 0
      ext i
      fin_cases i
      · simp
      · simpa [hq02] using hi
      · simpa using hq02.symm
    · contrapose!
      refine ⟨by grind, fun h ↦ ?_⟩
      ext
      · exact h
      obtain ⟨p, q⟩ := pq
      induction p with | mk p hp
      induction q with | mk q hq
      obtain ⟨l, hl0, hl⟩ := (P2.mk_eq_mk _ _).mp h
      have hp02 : p 0 = -p 2 := by
        trans -l
        · simpa using congr($hl 0)
        · simpa using congr($hl 2).symm
      have hp1 : p 1 = 0 := by simpa using congr($hl 1)
      have hp2 : p 2 ≠ 0 := by
        by_contra! hp2
        suffices p = 0 from hp this
        ext i
        fin_cases i
        · simpa [hp02] using hp2
        · exact hp1
        · exact hp2
      obtain ⟨ho, hi, hpq⟩ := (mem_dom _ _ _).mp hmem
      have hq02 : q 2 = -q 0 := by simpa [hp02, hp1, hp2, ← mul_neg] using hpq.symm
      simp only
      rw [P2.mk_eq_mk']
      use -q 0
      ext i
      fin_cases i
      · simp
      · simpa [hq02] using hi
      · simpa using hq02
  · simp [hmem]

theorem next_ne_self [DecidableEq K] [hchar : NeZero (2 : K)]
    {pq : P2 K × P2 K} (h : pq ∈ dom₀ cf) :
    next cf (pq) ≠ pq := by
  intro heq
  obtain ⟨hmem, hright, hleft⟩ := (mem_dom₀ cf).mp h
  obtain h | h := (next_eq_self' cf hmem).mp heq
  · simp [h] at hright
  · simp [h] at hleft
