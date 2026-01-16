import Mathlib
import Poncelet.Circle

open EuclideanGeometry Real RealInnerProductSpace

-- by droplet739 from Discord
theorem radius_lt_of_inside {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Nontrivial V]
    (i o : Sphere P) (hi : 0 < i.radius)
    (hinside : ∀ p ∈ i, dist p o.center < o.radius) :
    i.radius < o.radius := by
  simp only [dist_eq_norm_vsub] at hinside
  let d : V := i.center -ᵥ o.center
  contrapose! hinside
  obtain ⟨y, hy_norm⟩ := exists_norm_eq V hi.le
  have : 2 * i.radius ≤ ‖d + y‖ + ‖d - y‖ := by
    grw [← norm_sub_le]
    simp [← two_smul ℝ, norm_smul, hy_norm]
  obtain h | h : o.radius ≤ ‖y + d‖ ∨ o.radius ≤ ‖-y + d‖ := by grind [neg_add_eq_sub]
  · exact ⟨y +ᵥ i.center, by simp [mem_sphere, hy_norm], by simpa [d, vadd_vsub_assoc] using h⟩
  · exact ⟨-y +ᵥ i.center, by simp [mem_sphere, hy_norm], by simpa [d, vadd_vsub_assoc] using h⟩

-- by Aristotle
lemma exists_dist_eq_dist_add_radius {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Nontrivial V]
    (s : EuclideanGeometry.Sphere P) (c : P) (hs : 0 < s.radius) :
    ∃ p ∈ s, dist p c = s.radius + dist s.center c := by
  simp_rw [EuclideanGeometry.mem_sphere, dist_eq_norm_vsub]
  obtain ⟨x, hx1, hx2⟩ : ∃ x : V, ‖x‖ = s.radius ∧ ‖x + (s.center -ᵥ c)‖ =
      s.radius + ‖s.center -ᵥ c‖ := by
    by_cases h : s.center = c
    · obtain ⟨x, hx⟩ := exists_ne (0 : V)
      use ‖s.radius / ‖x‖‖ • x
      simp [h, norm_smul, abs_of_pos hs, hx]
    · refine ⟨(s.radius / ‖s.center -ᵥ c‖) • (s.center -ᵥ c), ?_, ?_⟩
      · rw [norm_smul, Real.norm_of_nonneg (div_nonneg hs.le (norm_nonneg _)),
          div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (vsub_ne_zero.mpr h))]
      · have h' : (s.radius / ‖s.center -ᵥ c‖) • (s.center -ᵥ c) + (s.center -ᵥ c) =
            (s.radius / ‖s.center -ᵥ c‖ + 1) • (s.center -ᵥ c) := by
          rw [add_smul, one_smul]
        rw [h', norm_smul,
          Real.norm_of_nonneg (add_nonneg (div_nonneg hs.le (norm_nonneg _)) zero_le_one)]
        have : ‖s.center -ᵥ c‖ ≠ 0 := by simpa using h
        field
  use x +ᵥ s.center
  simp [hx1, hx2, vadd_vsub_assoc]

theorem radius_lt_of_inside' {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Nontrivial V]
    (i o : Sphere P) (hi : 0 < i.radius)
    (hinside : ∀ p ∈ i, dist p o.center < o.radius)
    {p : P} (hp : p ∈ o) :
    i.radius < dist p i.center := by
  obtain ⟨q, hq₁, hq₂⟩ := exists_dist_eq_dist_add_radius i o.center hi;
  have hp_dist : dist p o.center = o.radius := by
    exact mem_sphere.mp hp;
  have := dist_triangle p i.center o.center
  linarith [hinside q hq₁]

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [hrank : Fact (Module.finrank ℝ V = 2)]

omit [Fact (Module.finrank ℝ V = 2)] in
theorem finrank_direction_affineSpan_eq_two {p q : P} (h : p ≠ q) :
    Module.finrank ℝ (affineSpan ℝ {p, q}).direction = 1 := by
  classical
  have : ({p, q} : Set P) = Set.range ((↑) : ({p, q} : Finset P) → P) := by
    ext i
    simp
  rw [direction_affineSpan, this]
  apply AffineIndependent.finrank_vectorSpan ?_ ?_
  · rw [affineIndependent_iff_linearIndependent_vsub ℝ _ ⟨p, by simp⟩]
    have : Subsingleton {x : ({p, q} : Finset P) // x ≠ ⟨p, by simp⟩} :=
      ⟨by grind⟩
    apply LinearIndependent.of_subsingleton ⟨⟨q, by simp⟩, by simpa using h.symm⟩
    simpa using h.symm
  · simpa using Finset.card_eq_two.mpr ⟨_, _, h, rfl⟩

theorem basis_two {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (h : ⟪x, y⟫ = 0)
    (v : V) :  ∃ a b : ℝ, v = a • x + b • y := by
  have hli : LinearIndependent ℝ ![x, y] := by
    rw [LinearIndependent.pair_iff' hx]
    intro a ha
    simpa [h, inner_smul_left, hy] using congr(⟪$ha, y⟫).symm
  have hrangexy : {x, y} = Set.range ![x, y] := by aesop
  have hr : Module.finrank ℝ (Submodule.span ℝ {x, y}) = 2 := by
    convert finrank_span_eq_card hli
  have hspan : Submodule.span ℝ {x, y} = ⊤ := by
    have h_finite_dim : FiniteDimensional ℝ V := by
      exact FiniteDimensional.of_finrank_pos (by simp [hrank.1])
    apply Submodule.eq_top_of_finrank_eq
    rw [hr, hrank.1]
  have := hspan.ge (Submodule.mem_top : v ∈ ⊤)
  rw [Submodule.mem_span_pair] at this
  tauto

theorem proj_two {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (h : ⟪x, y⟫ = 0) (v : V) :
    ⟪v, x⟫ ^ 2 / ‖x‖ ^ 2 + ⟪v, y⟫ ^ 2 / ‖y‖ ^ 2 = ‖v‖ ^ 2 := by
  obtain ⟨a, b, hv⟩ := basis_two hx hy h v
  have h' : ⟪y, x⟫ = 0 := by
    rw [real_inner_comm]
    exact h
  simp [hv, h, h',
    inner_add_left, inner_smul_left, inner_smul_right, norm_add_sq_real, norm_smul, mul_pow, field]

theorem inner_swap {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (h : ⟪x, y⟫ = 0) {u v : V} (hu0 : u ≠ 0) :
    (∃ a : ℝ, a • u = v) ↔ ⟪v, x⟫ * ⟪u, y⟫ = ⟪v, y⟫ * ⟪u, x⟫ := by
  constructor
  · rintro ⟨a, rfl⟩
    simp_rw [real_inner_smul_left]
    ring
  intro hleft
  obtain ⟨a, b, hv⟩ := basis_two hx hy h v
  obtain ⟨c, d, hu⟩ := basis_two hx hy h u
  have h' : ⟪y, x⟫ = 0 := by
    rw [real_inner_comm]
    exact h
  have habcd : a * ‖x‖ ^ 2 * (d * ‖y‖ ^ 2) = b * ‖y‖ ^ 2 * (c * ‖x‖ ^ 2) := by
    simpa [hu, hv, inner_add_left, real_inner_smul_left, h, h'] using hleft
  rw [mul_mul_mul_comm a, mul_mul_mul_comm b, mul_comm (‖x‖ ^ 2)] at habcd
  rw [mul_left_inj' (by simp [hx, hy])] at habcd
  rw [hu, hv]
  simp_rw [smul_add, smul_smul]
  rw [add_comm (a • x)]
  simp_rw [← sub_eq_sub_iff_add_eq_add, ← sub_smul]
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by
      contrapose! hu0 with hd
      simp [hu, hc, hd]
    have ha : a = 0 := by
      simpa [hc, hd] using habcd
    use b / d
    simp [hc, hd, ha]
  · use a / c
    suffices b - a / c * d = 0 by simp [this, hc]
    field_simp
    linear_combination -habcd

def IsProperPolygon
    {n : ℕ} [NeZero n] (a : Fin n → P) :=
  ∀ i, a i ≠ a (i + 1) ∧ affineSpan ℝ {a i, a (i + 1)} ≠ affineSpan ℝ {a (i + 1), a (i + 2)}

def Inscribe {n : ℕ} [NeZero n] (a : Fin n → P) (s : Sphere P) :=
  ∀ i, a i ∈ s

def Circumscribe {n : ℕ} [NeZero n] (a : Fin n → P) (s : Sphere P) :=
  ∀ i, s.IsTangent (affineSpan ℝ {a i, a (i + 1)})

variable (P) in
structure EuConfig where
  o : Sphere P
  i : Sphere P
  o_pos : 0 < o.radius
  i_pos : 0 < i.radius
  inside : ∀ p ∈ i, dist p o.center < o.radius
  center : o.center ≠ i.center

namespace EuConfig
variable (cf : EuConfig P)

def xAxis := affineSpan ℝ {cf.o.center, cf.i.center}

omit [Fact (Module.finrank ℝ V = 2)] in
theorem finrank_direction_xAxis : Module.finrank ℝ cf.xAxis.direction = 1 := by
  apply finrank_direction_affineSpan_eq_two cf.center

def yAxis := AffineSubspace.mk' cf.i.center cf.xAxis.directionᗮ

theorem finrank_direction_yAxis : Module.finrank ℝ cf.yAxis.direction = 1 := by
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
  rw [← add_right_inj (Module.finrank ℝ cf.xAxis.direction)]
  rw [yAxis, AffineSubspace.direction_mk', Submodule.finrank_add_finrank_orthogonal]
  simp [finrank_direction_xAxis, hrank.out]

theorem eixsts_mem_yAxis_ne_center_i :
    ∃ p ∈ cf.yAxis, p ≠ cf.i.center := by
  by_contra! h
  have : cf.yAxis ≤ affineSpan ℝ {cf.i.center}  := by
    intro p hp
    simpa using h p hp
  obtain hdir := Submodule.finrank_mono <| AffineSubspace.direction_le this
  rw [finrank_direction_yAxis, direction_affineSpan] at hdir
  simp at hdir

noncomputable
def yDir := cf.eixsts_mem_yAxis_ne_center_i.choose

theorem yDir_mem_yAxis : cf.yDir ∈ cf.yAxis := cf.eixsts_mem_yAxis_ne_center_i.choose_spec.1
theorem yDir_ne_center_i : cf.yDir ≠ cf.i.center := cf.eixsts_mem_yAxis_ne_center_i.choose_spec.2

theorem inner_yDir_center_o : ⟪cf.o.center -ᵥ cf.i.center, cf.yDir -ᵥ cf.i.center⟫ = 0 := by
  obtain hmem := cf.yDir_mem_yAxis
  rw [yAxis, AffineSubspace.mem_mk', Submodule.mem_orthogonal] at hmem
  apply hmem
  rw [xAxis, direction_affineSpan, mem_vectorSpan_pair]
  use 1
  simp

noncomputable
def toConfig : Config ℝ where
  u := dist cf.o.center cf.i.center / cf.i.radius
  r := cf.o.radius / cf.i.radius
  hu := by simp [cf.center, cf.i_pos.ne.symm]
  hr := by simp [cf.o_pos.ne.symm, cf.i_pos.ne.symm]
  k := √(((dist cf.o.center cf.i.center + cf.o.radius) / cf.i.radius) ^ 2 - 1)
  k_sq := by
    rw [sq_sqrt ?_]
    · ring
    apply sub_nonneg_of_le
    rw [one_le_sq_iff_one_le_abs, abs_div]
    rw [one_le_div (by simpa using cf.i_pos.ne.symm)]
    rw [(abs_add_eq_add_abs_iff _ _).mpr (Or.inl ⟨by simp, cf.o_pos.le⟩)]
    suffices |cf.i.radius| ≤ |cf.o.radius| from this.trans (by simp)
    rw [abs_of_nonneg (by simpa using cf.i_pos.le)]
    rw [abs_of_nonneg (by simpa using cf.o_pos.le)]
    apply le_of_lt
    have : Nontrivial V := by
      have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
      apply (Module.finrank_pos_iff_of_free ℝ _).mp
      simp [hrank.out]
    exact radius_lt_of_inside cf.i cf.o cf.i_pos cf.inside

noncomputable
def sendPoint (p : P) : P2 ℝ := P2.mk ![
  ⟪p -ᵥ cf.i.center, cf.o.center -ᵥ cf.i.center⟫ / (dist cf.o.center cf.i.center * cf.i.radius),
  ⟪p -ᵥ cf.i.center, cf.yDir -ᵥ cf.i.center⟫ / (dist cf.yDir cf.i.center * cf.i.radius),
  1] (by simp)

theorem sendPoint_inj {p q : P} (h : cf.sendPoint p = cf.sendPoint q) :
    p = q := by
  unfold sendPoint at h
  obtain ⟨l, hl⟩ := (P2.mk_eq_mk' _ _).mp h
  have hl1 : l = 1 := by simpa using congr($hl 2).symm
  have h0 : dist cf.o.center cf.i.center * cf.i.radius ≠ 0 := by
    simp [cf.center, cf.i_pos.ne.symm]
  have h0' : (dist cf.yDir cf.i.center * cf.i.radius) ≠ 0 := by
    simp [cf.yDir_ne_center_i, cf.i_pos.ne.symm]
  obtain hx : ⟪p -ᵥ cf.i.center, cf.o.center -ᵥ cf.i.center⟫ =
    ⟪q -ᵥ cf.i.center, cf.o.center -ᵥ cf.i.center⟫ := by simpa [hl1, h0] using congr($hl 0)
  obtain hy : ⟪p -ᵥ cf.i.center, cf.yDir -ᵥ cf.i.center⟫ =
    ⟪q -ᵥ cf.i.center, cf.yDir -ᵥ cf.i.center⟫ := by simpa [hl1, h0'] using congr($hl 1)
  obtain hxy := cf.inner_yDir_center_o
  obtain hyx := real_inner_comm (cf.o.center -ᵥ cf.i.center) _ ▸ hxy
  obtain ⟨a, b, hv⟩ := basis_two (by simpa using cf.center)
    (by simpa using cf.yDir_ne_center_i) hxy (p -ᵥ cf.i.center)
  obtain ⟨c, d, hu⟩ := basis_two (by simpa using cf.center)
    (by simpa using cf.yDir_ne_center_i) hxy (q -ᵥ cf.i.center)
  have hac : a = c := by
    simpa [hu, hv, inner_add_left, real_inner_smul_left, hyx, cf.center] using hx
  have hbd : b = d := by
    simpa [hu, hv, inner_add_left, real_inner_smul_left, hxy, cf.yDir_ne_center_i] using hy
  rw [← (vsub_left_injective cf.i.center).eq_iff]
  rw [hu, hv, hac, hbd]

theorem mem_o_iff {p : P} : p ∈ cf.o ↔ OuterCircle cf.toConfig (cf.sendPoint p) := by
  rw [OuterCircle, sendPoint, EuclideanGeometry.mem_sphere]
  simp only [P2.lift_mk, Matrix.cons_val_zero, Matrix.cons_val, mul_one,
    Matrix.cons_val_one, one_pow]
  rw [toConfig]
  simp only
  simp_rw [← div_div, ← sub_div, div_pow, ← add_div, dist_eq_norm_vsub V]
  rw [div_left_inj' (by simpa using cf.i_pos.ne.symm)]
  rw [div_sub' (by simpa using cf.center), div_pow, ← real_inner_self_eq_norm_mul_norm]
  rw [← inner_sub_left]
  rw [vsub_sub_vsub_cancel_right]
  rw [show ⟪p -ᵥ cf.i.center, cf.yDir -ᵥ cf.i.center⟫ =
        ⟪p -ᵥ cf.o.center, cf.yDir -ᵥ cf.i.center⟫ by
    rw [← sub_eq_zero, ← inner_sub_left, vsub_sub_vsub_cancel_left]
    apply inner_yDir_center_o]
  rw [proj_two (by simpa using cf.center) (by simpa using cf.yDir_ne_center_i)
    cf.inner_yDir_center_o]
  exact (sq_eq_sq₀ (by simp) cf.o_pos.le).symm

theorem not_innerCircle_of_mem_o {p : P} (hp : p ∈ cf.o) :
    ¬ InnerCircle cf.toConfig (cf.sendPoint p) := by
  simp only [InnerCircle, sendPoint, P2.lift_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, one_pow]
  simp_rw [div_pow, mul_pow, ← div_div, ← add_div, dist_eq_norm_vsub]
  rw [proj_two (by simp [cf.center]) (by simp [cf.yDir_ne_center_i])
    (by simpa using cf.inner_yDir_center_o)]
  rw [div_eq_one_iff_eq (by simpa using cf.i_pos.ne.symm)]
  rw [sq_eq_sq₀ (by simp) cf.i_pos.le]
  rw [← dist_eq_norm_vsub]
  apply ne_of_gt
  have : Nontrivial V := by
    have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
    apply (Module.finrank_pos_iff_of_free ℝ _).mp
    simp [hrank.out]
  apply radius_lt_of_inside' cf.i cf.o cf.i_pos cf.inside hp

noncomputable def dirVec {p : AffineSubspace ℝ P} (hp : Module.finrank ℝ p.direction = 1) :
    p.direction :=
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
  (Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank ℝ p.direction by simp [hp])).choose

theorem dirVec_ne_zero {p : AffineSubspace ℝ P} (hp : Module.finrank ℝ p.direction = 1) :
    dirVec hp ≠ 0 :=
  have : FiniteDimensional ℝ V := FiniteDimensional.of_finrank_pos (by simp [hrank.out])
  (Module.finrank_pos_iff_exists_ne_zero.mp
    (show 0 < Module.finrank ℝ p.direction by simp [hp])).choose_spec

theorem dirVec_ne_zero' {p : AffineSubspace ℝ P} (hp : Module.finrank ℝ p.direction = 1) :
    (dirVec hp : V) ≠ 0 := by
  simpa using dirVec_ne_zero hp

theorem eq_span_dirVec {p : AffineSubspace ℝ P} (hp : Module.finrank ℝ p.direction = 1) :
    p.direction = Submodule.span ℝ {(dirVec hp).val} := by
  rw [finrank_eq_one_iff_of_nonzero _ (dirVec_ne_zero hp)] at hp
  rw [← Submodule.map_subtype_span_singleton, hp]
  simp

noncomputable def linePoint {p : AffineSubspace ℝ P} (hp : Module.finrank ℝ p.direction = 1) :
    P :=
  ((AffineSubspace.nonempty_iff_ne_bot p).mpr fun h ↦ by
    rw [h, AffineSubspace.direction_bot] at hp
    simp at hp
  ).some

omit hrank in
theorem linePoint_mem {p : AffineSubspace ℝ P} (hp : Module.finrank ℝ p.direction = 1) :
    linePoint hp ∈ p :=
  ((AffineSubspace.nonempty_iff_ne_bot p).mpr fun h ↦ by
    rw [h, AffineSubspace.direction_bot] at hp
    simp at hp
  ).some_mem

noncomputable
def sendChord' (p : P) (d : V) (hd : d ≠ 0) : P2 ℝ :=
  P2.mk ![
      ⟪d, cf.yDir -ᵥ cf.i.center⟫ / (dist cf.yDir cf.i.center),
      -⟪d, cf.o.center -ᵥ cf.i.center⟫ / (dist cf.o.center cf.i.center),
      (⟪p -ᵥ cf.i.center, cf.o.center -ᵥ cf.i.center⟫ *
        ⟪d, cf.yDir -ᵥ cf.i.center⟫
      - ⟪p -ᵥ cf.i.center, cf.yDir -ᵥ cf.i.center⟫ *
        ⟪d, cf.o.center -ᵥ cf.i.center⟫)
        / (dist cf.yDir cf.i.center * dist cf.o.center cf.i.center * cf.i.radius)
    ] (fun h ↦ by
      have h0 : ⟪d, cf.yDir -ᵥ cf.i.center⟫ = 0 := by
        simpa [cf.yDir_ne_center_i] using congr($h 0)
      have h1 : ⟪d, cf.o.center -ᵥ cf.i.center⟫ = 0 := by
        simpa [cf.center] using congr($h 1)
      obtain hxy := cf.inner_yDir_center_o
      obtain hyx := real_inner_comm (cf.o.center -ᵥ cf.i.center) _ ▸ hxy
      obtain ⟨a, b, hv⟩ := basis_two (by simpa using cf.center)
        (by simpa using cf.yDir_ne_center_i) cf.inner_yDir_center_o d
      rw [hv] at h0 h1
      have ha : a = 0 := by
        simpa [inner_add_left, real_inner_smul_left, hxy, hyx, cf.center, cf.yDir_ne_center_i]
          using h1
      have hb : b = 0 := by
        simpa [inner_add_left, real_inner_smul_left, hxy, hyx, cf.center, cf.yDir_ne_center_i]
          using h0
      simp [ha, hb, hd] at hv)

theorem sendChord'_eq {p1 p2 : P} {d1 d2 : V} {p : AffineSubspace ℝ P}
    (hp : Module.finrank ℝ p.direction = 1)
    (hp1 : p1 ∈ p) (hp2 : p2 ∈ p)
    (hd1 : d1 ≠ 0) (hd2 : d2 ≠ 0)
    (hdp1 : d1 ∈ p.direction) (hdp2 : d2 ∈ p.direction) :
    cf.sendChord' p1 d1 hd1 = cf.sendChord' p2 d2 hd2 := by
  have hy0 : dist cf.yDir cf.i.center ≠ 0 := by
    simpa using cf.yDir_ne_center_i
  have hd2' : (⟨d2, hdp2⟩ : p.direction) ≠ 0 := by
    simpa using hd2
  obtain ⟨l, hl⟩ := exists_smul_eq_of_finrank_eq_one hp hd2' ⟨d1, hdp1⟩
  have hl : l • d2 = d1 := by simpa using hl
  unfold sendChord'
  rw [P2.mk_eq_mk']
  use l
  ext i
  fin_cases i
  · simp [← hl, real_inner_smul_left, field]
  · simp [← hl, real_inner_smul_left, field]
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val, Pi.smul_apply,
      Fin.isValue, smul_eq_mul]
    simp_rw [← hl, real_inner_smul_left, ← mul_assoc, mul_comm _ l]
    simp_rw [mul_assoc l, ← mul_sub, mul_div_assoc]
    congr 2
    rw [← sub_eq_zero, sub_sub_sub_comm]
    simp_rw [← sub_mul, ← inner_sub_left, vsub_sub_vsub_cancel_right]
    rw [sub_eq_zero]
    rw [← inner_swap (by simpa using cf.center) (by simpa using cf.yDir_ne_center_i)
      cf.inner_yDir_center_o hd2]
    obtain ⟨m, hm⟩ := exists_smul_eq_of_finrank_eq_one hp hd2'
      ⟨p1 -ᵥ p2, AffineSubspace.vsub_mem_direction hp1 hp2⟩
    exact ⟨m, by simpa using hm⟩

noncomputable
def sendChord (p : AffineSubspace ℝ P) : P2 ℝ :=
  if hp : Module.finrank ℝ p.direction = 1 then
    cf.sendChord' (linePoint hp) (dirVec hp).val (by simpa using dirVec_ne_zero hp)
  else
    P2.mk ![0, 0, 1] (by simp)

theorem sendChord_eq {g : P} {d : V} {p : AffineSubspace ℝ P}
    (hp : Module.finrank ℝ p.direction = 1)
    (hg : g ∈ p) (hd : d ≠ 0)
    (hdp : d ∈ p.direction) :
    cf.sendChord p = cf.sendChord' g d hd := by
  simpa [sendChord, hp] using cf.sendChord'_eq hp (linePoint_mem _)
    hg (by simpa using dirVec_ne_zero hp) hd (by simp) hdp

theorem sendChord_inj {p q : AffineSubspace ℝ P}
    (hp : Module.finrank ℝ p.direction = 1)
    (hq : Module.finrank ℝ q.direction = 1) (h : cf.sendChord p = cf.sendChord q) :
    p = q := by
  have : Nontrivial p.direction := by
    have : FiniteDimensional ℝ p.direction := FiniteDimensional.of_finrank_pos (by simp [hp])
    apply (Module.finrank_pos_iff_of_free ℝ _).mp
    simp [hp]
  have hpb : p ≠ ⊥ := fun h ↦ by
    rw [h, AffineSubspace.direction_bot] at hp
    simp at hp
  have hqb : q ≠ ⊥ := fun h ↦ by
    rw [h, AffineSubspace.direction_bot] at hq
    simp at hq
  obtain hpnonempty := (AffineSubspace.nonempty_iff_ne_bot p).mpr hpb
  obtain hqnonempty := (AffineSubspace.nonempty_iff_ne_bot q).mpr hqb
  obtain hxy := cf.inner_yDir_center_o
  obtain hxy' := real_inner_comm (cf.o.center -ᵥ cf.i.center) _ ▸ hxy
  by_cases hpara : p.direction = q.direction
  · obtain ⟨mp, hmp⟩ := hpnonempty
    obtain ⟨mq, hmq⟩ := hqnonempty
    obtain ⟨⟨v, hvmemp⟩, hv⟩ := exists_ne (0 : p.direction)
    have hv : v ≠ 0 := by simpa using hv
    have hvmemq : v ∈ q.direction := hpara ▸ hvmemp
    rw [cf.sendChord_eq hp hmp hv hvmemp, cf.sendChord_eq hq hmq hv hvmemq] at h
    unfold sendChord' at h
    obtain ⟨l, hl⟩ := (P2.mk_eq_mk' _ _).mp h
    have hl1 : l = 1 := by
      by_cases hx : ⟪v, cf.yDir -ᵥ cf.i.center⟫ = 0
      · have hy : ⟪v, cf.o.center -ᵥ cf.i.center⟫ ≠ 0 := by
          by_contra! hy
          suffices v = 0 from hv this
          obtain ⟨a, b, hv⟩ := basis_two (by simpa using cf.center)
            (by simpa using cf.yDir_ne_center_i) hxy v
          have ha : a = 0 := by
            simpa [hv, inner_add_left, real_inner_smul_left, hxy, hxy', cf.center,
              cf.yDir_ne_center_i] using hy
          have hb : b = 0 := by
            simpa [hv, inner_add_left, real_inner_smul_left, hxy, hxy', cf.center,
              cf.yDir_ne_center_i] using hx
          simpa [ha, hb] using hv
        have : -⟪v, cf.o.center -ᵥ cf.i.center⟫ / dist cf.o.center cf.i.center ≠ 0 := by
          simp [hy, cf.center]
        simpa [this] using congr($hl 1)
      · have : (⟪v, cf.yDir -ᵥ cf.i.center⟫ / dist cf.yDir cf.i.center) ≠ 0 := by
          simp [hx, cf.yDir_ne_center_i]
        simpa [this] using congr($hl 0)
    have : (dist cf.yDir cf.i.center * dist cf.o.center cf.i.center * cf.i.radius) ≠ 0 := by
      simp [cf.yDir_ne_center_i, cf.i_pos.ne.symm, cf.center]
    obtain hz : ⟪mp -ᵥ cf.i.center, cf.o.center -ᵥ cf.i.center⟫ * ⟪v, cf.yDir -ᵥ cf.i.center⟫ -
        ⟪mp -ᵥ cf.i.center, cf.yDir -ᵥ cf.i.center⟫ * ⟪v, cf.o.center -ᵥ cf.i.center⟫ =
        ⟪mq -ᵥ cf.i.center, cf.o.center -ᵥ cf.i.center⟫ * ⟪v, cf.yDir -ᵥ cf.i.center⟫ -
        ⟪mq -ᵥ cf.i.center, cf.yDir -ᵥ cf.i.center⟫ * ⟪v, cf.o.center -ᵥ cf.i.center⟫ := by
      simpa [hl1, this] using congr($hl 2)
    rw [sub_eq_sub_iff_sub_eq_sub] at hz
    simp_rw [← sub_mul, ← inner_sub_left, vsub_sub_vsub_cancel_right] at hz
    rw [← inner_swap (by simpa using cf.center) (by simpa using cf.yDir_ne_center_i)
      cf.inner_yDir_center_o hv] at hz
    obtain ⟨a, ha⟩ := hz
    have hmpadd : mp = a • v +ᵥ mq := by
      rw [eq_vadd_iff_vsub_eq]
      exact ha.symm
    have hmpmemq : mp ∈ q := by
      rw [hmpadd]
      exact AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ _ hvmemq) hmq
    rw [← AffineSubspace.mk'_eq hmp, hpara]
    apply AffineSubspace.mk'_eq hmpmemq
  · sorry

theorem mem_iff_incidence_sendChord {p : P} {q : AffineSubspace ℝ P}
    (hq : Module.finrank ℝ q.direction = 1) :
    p ∈ q ↔ Incidence cf.toConfig (cf.sendPoint p) (cf.sendChord q) := by
  rw [Incidence, sendPoint, sendChord]
  simp only [sendChord', Fin.isValue, hq, ↓reduceDIte, P2.lift₂_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, one_mul]
  simp_rw [div_mul_div_comm]
  rw [show dist cf.o.center cf.i.center * cf.i.radius * dist cf.yDir cf.i.center
    = dist cf.yDir cf.i.center * dist cf.o.center cf.i.center * cf.i.radius by ring]
  rw [show dist cf.yDir cf.i.center * cf.i.radius * dist cf.o.center cf.i.center
    = dist cf.yDir cf.i.center * dist cf.o.center cf.i.center * cf.i.radius by ring]
  rw [← add_div]
  rw [div_left_inj' (by simp [cf.yDir_ne_center_i, cf.center, cf.i_pos.ne.symm])]
  rw [mul_neg, ← sub_eq_add_neg]
  rw [sub_eq_sub_iff_sub_eq_sub]
  simp_rw [← sub_mul, ← inner_sub_left, vsub_sub_vsub_cancel_right]
  conv_lhs => rw [← AffineSubspace.mk'_eq (linePoint_mem hq), AffineSubspace.mem_mk',
    eq_span_dirVec hq, Submodule.mem_span_singleton]
  exact inner_swap (by simpa using cf.center) (by simpa using cf.yDir_ne_center_i)
    cf.inner_yDir_center_o (by simpa using dirVec_ne_zero hq)

theorem isTangent_i_iff {p : AffineSubspace ℝ P} (hp : Module.finrank ℝ p.direction = 1) :
    cf.i.IsTangent p ↔ InnerCircle cf.toConfig (cf.sendChord p) := by
  obtain hnonempty := ((AffineSubspace.nonempty_iff_ne_bot p).mpr fun h ↦ by
    rw [h, AffineSubspace.direction_bot] at hp
    simp at hp
  )
  have : Nonempty p := by simpa using hnonempty
  have h_finite_dim : FiniteDimensional ℝ V := by
    exact FiniteDimensional.of_finrank_pos (by simp [hrank.1])
  obtain hmem : (orthogonalProjection p cf.i.center).val ∈ p :=
    EuclideanGeometry.orthogonalProjection_mem cf.i.center
  rw [cf.sendChord_eq hp hmem (dirVec_ne_zero' hp) (dirVec hp).prop]
  simp only [InnerCircle, sendChord', P2.lift_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  rw [neg_div, neg_sq]
  simp_rw [div_pow, dist_eq_norm_vsub]
  rw [proj_two (by simpa using cf.yDir_ne_center_i) (by simpa using cf.center)
    (real_inner_comm (cf.o.center -ᵥ cf.i.center) _ ▸ cf.inner_yDir_center_o)]
  rw [eq_div_iff (by simp [cf.yDir_ne_center_i, cf.center, cf.i_pos.ne.symm])]
  rw [← EuclideanGeometry.Sphere.dist_orthogonalProjection_eq_radius_iff_isTangent]
  conv_lhs =>
    rw [Eq.comm]
    rw [← sq_eq_sq₀ cf.i_pos.le (by simp)]
    rw [← mul_left_inj' (show ‖(dirVec hp : V)‖ ^ 2 *
      ‖cf.yDir -ᵥ cf.i.center‖ ^ 2 * ‖cf.o.center -ᵥ cf.i.center‖ ^ 2 ≠ 0 by
      simp [cf.yDir_ne_center_i, cf.center, dirVec_ne_zero])]
    rw [dist_eq_norm_vsub']
  congrm($(by ring) = ?_)
  obtain hxy := cf.inner_yDir_center_o
  obtain hxy' := real_inner_comm (cf.o.center -ᵥ cf.i.center) _ ▸ hxy
  rw [pow_two ‖(orthogonalProjection p cf.i.center).val -ᵥ cf.i.center‖]
  rw [pow_two ‖(dirVec hp).val‖]
  obtain ⟨a, b, hv⟩ := basis_two (by simpa using cf.center)
    (by simpa using cf.yDir_ne_center_i) hxy (dirVec hp).val
  obtain ⟨c, d, hu⟩ := basis_two (by simpa using cf.center)
    (by simpa using cf.yDir_ne_center_i) hxy
    ((orthogonalProjection p cf.i.center).val -ᵥ cf.i.center)
  set x := cf.o.center -ᵥ cf.i.center
  set y := cf.yDir -ᵥ cf.i.center
  simp_rw [hu, hv]
  simp_rw [inner_add_left, real_inner_smul_left, hxy, hxy']
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_real (by
    simp [real_inner_smul_left, real_inner_smul_right, hxy])]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_real (by
    simp [real_inner_smul_left, real_inner_smul_right, hxy])]
  simp_rw [← pow_two]
  simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp_rw [real_inner_self_eq_norm_sq]
  suffices (a * c * ‖x‖ ^ 2 + b * d * ‖y‖ ^ 2) ^ 2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 = 0 by
    linear_combination this
  suffices a * c * ‖x‖ ^ 2 + b * d * ‖y‖ ^ 2 = 0 by simp [this]
  suffices ⟪(dirVec hp).val, (orthogonalProjection p cf.i.center).val -ᵥ cf.i.center⟫ = 0 by
    simp_rw [hu, hv, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hxy, hxy', real_inner_self_eq_norm_sq] at this
    linear_combination this
  refine (Submodule.mem_orthogonal p.direction _).mp ?_ _ (dirVec hp).prop
  apply EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal

theorem not_tangentOuterCircle_of_isTangent {p : AffineSubspace ℝ P}
    (hp : Module.finrank ℝ p.direction = 1) (hi : cf.i.IsTangent p) :
    ¬ TangentOuterCircle cf.toConfig (cf.sendChord p) := by
  obtain ⟨g, hg⟩ := hi
  have hx0 : cf.o.center -ᵥ cf.i.center ≠ 0 := by
    simpa using cf.center
  have hy0 : cf.yDir -ᵥ cf.i.center ≠ 0 := by
    simpa using cf.yDir_ne_center_i
  have hi0 : cf.i.radius ≠ 0 := cf.i_pos.ne.symm
  rw [cf.sendChord_eq hp hg.mem_space (by simpa using dirVec_ne_zero hp)
    (dirVec hp).prop]
  obtain hgmemi := hg.mem_sphere
  simp only [TangentOuterCircle, sendChord', P2.lift_mk, Matrix.cons_val_zero,
    Matrix.cons_val, Matrix.cons_val_one, toConfig]
  simp_rw [dist_eq_norm_vsub]
  set v := (dirVec hp : V)
  set y := cf.yDir -ᵥ cf.i.center
  set x := cf.o.center -ᵥ cf.i.center
  set r := g -ᵥ cf.i.center
  field_simp
  sorry

theorem rChord_sendPoint_sendChord {p : P} {q1 q2 : AffineSubspace ℝ P}
    (hqne : q1 ≠ q2) (hq1 : Module.finrank ℝ q1.direction = 1)
    (hq2 : Module.finrank ℝ q2.direction = 1)
    (ho : p ∈ cf.o) (hi1 : cf.i.IsTangent q1) (hi2 : cf.i.IsTangent q2)
    (hpq1 : p ∈ q1) (hpq2 : p ∈ q2) :
    rChord cf.toConfig ⟨sendPoint cf p, sendChord cf q1⟩ = ⟨sendPoint cf p, sendChord cf q2⟩ := by
  have hmem1 : ⟨sendPoint cf p, sendChord cf q1⟩ ∈ dom cf.toConfig :=
    ⟨cf.mem_o_iff.mp ho, (cf.isTangent_i_iff hq1).mp hi1,
    (cf.mem_iff_incidence_sendChord hq1).mp hpq1⟩
  have hmem2 : ⟨sendPoint cf p, sendChord cf q2⟩ ∈ dom cf.toConfig :=
    ⟨cf.mem_o_iff.mp ho, (cf.isTangent_i_iff hq2).mp hi2,
    (cf.mem_iff_incidence_sendChord hq2).mp hpq2⟩
  obtain hmemr := mapsTo_rChord cf.toConfig hmem1
  obtain hne := (rChord_eq_self cf.toConfig hmem1).not.mpr (cf.not_innerCircle_of_mem_o ho)
  have : {⟨cf.sendPoint p, cf.sendChord q1⟩, ⟨cf.sendPoint p, cf.sendChord q2⟩,
      rChord cf.toConfig ⟨sendPoint cf p, sendChord cf q1⟩}
      ⊆ {pq ∈ dom cf.toConfig | pq.1 = cf.sendPoint p} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    obtain hx | hx | hx := hx
    · simp [hx, hmem1]
    · simp [hx, hmem2]
    · simp [hx, hmemr, fst_rChord]
  obtain hcard := (Set.encard_le_encard this).trans (encard_dom_fix1_le _ _)
  contrapose! hcard with h
  rw [Set.encard_eq_three.mpr ?_]
  · norm_num
  use ⟨cf.sendPoint p, cf.sendChord q1⟩, ⟨cf.sendPoint p, cf.sendChord q2⟩,
      rChord cf.toConfig ⟨sendPoint cf p, sendChord cf q1⟩
  refine ⟨fun h ↦ hqne ?_, Ne.symm hne, Ne.symm h, rfl⟩
  exact cf.sendChord_inj hq1 hq2 (by simpa using h)

theorem rPoint_sendPoint_sendChord {p1 p2 : P} {q : AffineSubspace ℝ P}
    (hpne : p1 ≠ p2)
    (hq : Module.finrank ℝ q.direction = 1)
    (ho1 : p1 ∈ cf.o) (ho2 : p2 ∈ cf.o) (hi : cf.i.IsTangent q)
    (hpq1 : p1 ∈ q) (hpq2 : p2 ∈ q) :
    rPoint cf.toConfig ⟨sendPoint cf p1, sendChord cf q⟩ = ⟨sendPoint cf p2, sendChord cf q⟩ := by
  have hmem1 : ⟨sendPoint cf p1, sendChord cf q⟩ ∈ dom cf.toConfig :=
    ⟨cf.mem_o_iff.mp ho1, (cf.isTangent_i_iff hq).mp hi,
    (cf.mem_iff_incidence_sendChord hq).mp hpq1⟩
  have hmem2 : ⟨sendPoint cf p2, sendChord cf q⟩ ∈ dom cf.toConfig :=
    ⟨cf.mem_o_iff.mp ho2, (cf.isTangent_i_iff hq).mp hi,
    (cf.mem_iff_incidence_sendChord hq).mp hpq2⟩
  obtain hmemr := mapsTo_rPoint cf.toConfig hmem1
  obtain hne := (rPoint_eq_self cf.toConfig hmem1).not.mpr
    (cf.not_tangentOuterCircle_of_isTangent hq hi)
  have : {⟨cf.sendPoint p1, cf.sendChord q⟩, ⟨cf.sendPoint p2, cf.sendChord q⟩,
      rPoint cf.toConfig ⟨sendPoint cf p1, sendChord cf q⟩}
      ⊆ {pq ∈ dom cf.toConfig | pq.2 = cf.sendChord q} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    obtain hx | hx | hx := hx
    · simp [hx, hmem1]
    · simp [hx, hmem2]
    · simp [hx, hmemr, snd_rPoint]
  obtain hcard := (Set.encard_le_encard this).trans (encard_dom_fix2_le _ _)
  contrapose! hcard with h
  rw [Set.encard_eq_three.mpr ?_]
  · norm_num
  use ⟨cf.sendPoint p1, cf.sendChord q⟩, ⟨cf.sendPoint p2, cf.sendChord q⟩,
      rPoint cf.toConfig ⟨sendPoint cf p1, sendChord cf q⟩
  refine ⟨fun h ↦ hpne ?_, Ne.symm hne, Ne.symm h, rfl⟩
  exact cf.sendPoint_inj (by simpa using h)

theorem next_sendPoint_sendChord {n : ℕ} [NeZero n] {a : Fin n → P}
    (ho : Inscribe a cf.o) (hi : Circumscribe a cf.i)
    (ha : IsProperPolygon a) (i : Fin n) :
    next cf.toConfig ⟨sendPoint cf (a i), sendChord cf (affineSpan ℝ {a i, a (i + 1)})⟩ =
      ⟨sendPoint cf (a (i + 1)), sendChord cf (affineSpan ℝ {a (i + 1), a (i + 2)})⟩ := by
  rw [next]
  rw [cf.rPoint_sendPoint_sendChord (ha i).1 (finrank_direction_affineSpan_eq_two (ha i).1)
    (ho i) (ho (i + 1)) (hi i)
    (mem_affineSpan ℝ <| (by simp)) (mem_affineSpan ℝ <| (by simp))]
  rw [cf.rChord_sendPoint_sendChord (ha i).2 (finrank_direction_affineSpan_eq_two (ha i).1)
    (finrank_direction_affineSpan_eq_two (by convert (ha (i + 1)).1 using 2; grind))
    (ho (i + 1)) (hi i) (by convert hi (i + 1) using 5; grind)
    (mem_affineSpan ℝ <| (by simp)) (mem_affineSpan ℝ <| (by simp))]

theorem iterate_next_sendPoint_sendChord {n : ℕ} [NeZero n] {a : Fin n → P}
    (ho : Inscribe a cf.o) (hi : Circumscribe a cf.i)
    (ha : IsProperPolygon a) (k : ℕ) (i : Fin n) :
    (next cf.toConfig)^[k] ⟨sendPoint cf (a i), sendChord cf (affineSpan ℝ {a i, a (i + 1)})⟩ =
      ⟨sendPoint cf (a (i + Fin.ofNat n k)),
      sendChord cf (affineSpan ℝ {a (i + Fin.ofNat n k), a (i + Fin.ofNat n k + 1)})⟩ := by
  induction k with
  | zero => simp [-Fin.ofNat_eq_cast]
  | succ k ih =>
  rw [Function.iterate_succ_apply', ih]
  rw [cf.next_sendPoint_sendChord ho hi ha]
  congrm (cf.sendPoint (a ?h1), cf.sendChord (affineSpan ℝ {a ?h1, a ?h2}))
  · rw [← Fin.val_eq_val]
    simp_rw [Fin.val_add, Fin.val_ofNat]
    simp only [Nat.add_mod_mod, Fin.coe_ofNat_eq_mod, Nat.mod_add_mod]
    grind
  · rw [← Fin.val_eq_val]
    simp_rw [Fin.val_add, Fin.val_ofNat]
    simp only [Nat.add_mod_mod, Fin.coe_ofNat_eq_mod, Nat.mod_add_mod]
    grind

theorem iterate_next_sendPoint_sendChord_eq_self {n : ℕ} [NeZero n] {a : Fin n → P}
    (ho : Inscribe a cf.o) (hi : Circumscribe a cf.i)
    (ha : IsProperPolygon a) (i : Fin n) :
    (next cf.toConfig)^[n] ⟨sendPoint cf (a i), sendChord cf (affineSpan ℝ {a i, a (i + 1)})⟩ =
      ⟨sendPoint cf (a i), sendChord cf (affineSpan ℝ {a i, a (i + 1)})⟩ := by
  simp [cf.iterate_next_sendPoint_sendChord ho hi ha n i]

end EuConfig
/-



theorem poncelet {outer inner : Sphere P} (hor : 0 < outer.radius) (hir : 0 < inner.radius)
    (hsphere : ∀ p ∈ outer, inner.radius < dist p inner.center)
    (hcenter : outer.center ≠ inner.center)
    {n : ℕ} [NeZero n] {a : Fin n → P}
    (houter : Inscribe a outer) (hinner : Circumscribe a inner)
    (ha : IsProperPolygon a) {x : P} (hx : x ∈ outer) :
    ∃ b : Fin n → P, b 0 = x ∧ Inscribe b outer ∧ Circumscribe b inner := by sorry
-/
