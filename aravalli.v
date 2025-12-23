(* Aravalli Definition Analysis: Statutory Consistency

   Question: Is the Supreme Court's 2025 definition of "Aravalli Hills"
   consistent with the statutory purposes of the Punjab Land Preservation
   Act, 1900, which it purports to implement?

   Finding: No. The 100m local relief threshold excludes terrain that is
   "subject to erosion" under PLPA § 3. Specifically, >57% of identified
   Aravalli hills (by DEM analysis) or >91% (by FSI count) fall below
   100m relief yet have slopes well above the 3° erosion susceptibility
   threshold. The definition is under-inclusive relative to its stated
   statutory basis.

   Legal instruments:
     PLPA 1900 § 3: "Whenever it appears to the Provincial Government
       that it is desirable to provide for the conservation of sub-soil
       water or the prevention of erosion in any area subject to erosion
       or likely to become liable to erosion, such Government may by
       notification make a direction accordingly."
     SC 2025 INSC 1338 Def. 7.1.1: "Any landform located in the Aravali
       districts, having an elevation of 100 metres or more from the
       local relief, shall be termed as Aravali Hills."

   Interpretive note: PLPA § 3 protects areas "subject to erosion" - a
   condition of terrain susceptibility, not current erosional state. Slopes
   >= 3° are subject to erosion regardless of present vegetation. This is
   a morphometric property determinable from DEM alone, independent of
   geological or ecological assumptions.

   Data provenance:
     DEM: GeoElevationData (Mathematica 14.3), ~30m resolution (SRTM-derived).

     Hill identification: Pixels with slope >= 3 deg classified as hill terrain.
       Connected components extracted via MorphologicalComponents.
       Local relief per component: marker-controlled watershed (peak - local base).

       METHODOLOGICAL NOTE: Hills are identified BY the 3 deg slope threshold.
       Thus "all identified hills have slope >= 3 deg" is tautological for the
       aggregate statistics. However, the core existence claim (under_inclusive)
       uses W's specific measured values (slope 25.12 deg) independent of how
       the population was identified. The existence proof survives.

     Witness selection: Alwar #73 chosen as excluded (relief 93.84m < 100m),
       erosion-susceptible (slope 25.12 deg >> 3 deg), isolated (>10km from
       any qualifying hill). Coordinates: 27.8353N, 76.8327E.

     Aggregate statistics: 24 Aravalli districts analyzed. N_total = 5585 hills
       identified, N_above = 2382 with relief >= 100m, N_below = 3203 excluded.

       DATA RECONCILIATION: Our DEM analysis finds 57% exclusion; FSI reportedly
       found 91% (1,048 of 12,081 hills >= 100m in 15 Rajasthan districts). The
       discrepancy reflects: (a) different segmentation - FSI counts hills >= 20m,
       our method merges connected slope components; (b) different geographic scope -
       FSI's 15 districts vs our 24 districts. Both figures support under-inclusivity;
       neither directly measures area excluded under the SC's inclusion envelope.

     Erosion threshold: 3 deg, adopted from FSI methodology (slope above which
       sheet erosion becomes significant under monsoon rainfall). This is an
       OPERATIONAL ASSUMPTION - PLPA § 3 does not specify a numeric threshold.

     Geology: GSI memoirs, Bhuiyan et al. 2009 (assumed, not field-verified).
     Ecology: Assumed (NDVI not performed).

   Author: Charles C. Norton, December 2025 *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sets.Ensembles.
Open Scope R_scope.

Definition threshold_relief : R := 100.
Definition threshold_erosion : R := 3.
Definition threshold_proximity : R := 500.
Definition threshold_isolation : R := 10000.
Definition threshold_recharge_slope : R := 30. (* Dunne & Leopold 1978: runoff dominates above ~30° *)

Record Morphometry := mkMorphometry {
  m_id : nat; m_lat : R; m_lon : R;
  m_relief : R; m_slope : R; m_area : R;
  m_peak : R; m_base : R
}.

Inductive Lithology := Quartzite | Schist | Gneiss | Phyllite | Marble | Alluvium.

Record Geology := mkGeology {
  g_lithology : Lithology;
  g_fracture_density : R;
  g_weathered_thickness : R
}.

Record Ecology := mkEcology {
  e_vegetation : R;
  e_drainage : R
}.

Record Hill := mkHill {
  h_morph : Morphometry;
  h_geo : Geology;
  h_eco : Ecology
}.

(* Morphometric predicates: depend only on DEM data.
   These apply to landforms in Aravalli districts (SC Def. 7.1.1 scope).
   The Aravalli parameter below constrains analysis to that domain. *)
Definition excluded (m : Morphometry) : Prop := m_relief m < threshold_relief.
Definition qualifies (m : Morphometry) : Prop := m_relief m >= threshold_relief.
Definition erosion_susceptible (m : Morphometry) : Prop := m_slope m >= threshold_erosion.

(* PLPA § 3 relevance: "subject to erosion" denotes terrain susceptibility,
   not current erosional state. PLPA does not specify a numeric threshold.

   OPERATIONAL ASSUMPTION: We adopt FSI's 3° slope threshold for erosion
   susceptibility (onset of significant sheet erosion under monsoon rainfall).
   This is a modeling choice, not statutory text. Alternative thresholds
   (e.g., USLE S-factor curves) would yield similar qualitative results
   given W's 25° slope far exceeds any reasonable cutoff. *)
Definition plpa_relevant (m : Morphometry) : Prop := erosion_susceptible m.

(* Predicates requiring geological/ecological assumptions *)
Definition has_recharge_geology (h : Hill) : Prop :=
  g_fracture_density (h_geo h) > 0 /\ g_weathered_thickness (h_geo h) > 0.

Definition recharges_groundwater (h : Hill) : Prop :=
  has_recharge_geology h /\ m_slope (h_morph h) <= threshold_recharge_slope.

Definition has_vegetation (h : Hill) : Prop := e_vegetation (h_eco h) > 0.

Definition prevents_erosion (h : Hill) : Prop :=
  erosion_susceptible (h_morph h) /\ has_vegetation h.

Definition plpa_functional (h : Hill) : Prop :=
  prevents_erosion h \/ recharges_groundwater h.

(* Empirical constants from DEM analysis (aravalli.wl, Dec 2025) *)
Definition N_total : R := 5585.
Definition N_above : R := 2382.
Definition N_below : R := 3203.
Definition N_fsi_total : R := 12081.
Definition N_fsi_above : R := 1048.

(* Witness: Alwar #73 *)
Definition W : Morphometry := mkMorphometry 73 27.8353 76.8327 93.84 25.12 2.13 693.84 600.
Definition W_geo : Geology := mkGeology Quartzite 2.5 8.0. (* assumed *)
Definition W_eco : Ecology := mkEcology 0.4 1.2. (* assumed *)
Definition W_hill : Hill := mkHill W W_geo W_eco.

(* Morphometric results *)

Theorem W_excluded : excluded W.
Proof. unfold excluded, W, m_relief, threshold_relief; simpl; lra. Qed.

Theorem W_erosion_susceptible : erosion_susceptible W.
Proof. unfold erosion_susceptible, W, m_slope, threshold_erosion; simpl; lra. Qed.

Theorem W_plpa_relevant : plpa_relevant W.
Proof. exact W_erosion_susceptible. Qed.

Theorem under_inclusive : exists m, excluded m /\ plpa_relevant m.
Proof. exists W; split; [exact W_excluded | exact W_plpa_relevant]. Qed.

(* LEGAL BRIDGE: The above theorem establishes under-inclusivity.

   Argument structure:
   1. SC 2025 INSC 1338 adopts the 100m definition "in the context of regulating
      mining" in Aravalli areas - areas historically protected under PLPA 1900.
   2. PLPA § 3 authorizes protection of areas "subject to erosion."
   3. under_inclusive proves: there exist landforms excluded by SC definition
      (relief < 100m) that are PLPA-relevant (erosion-susceptible).
   4. Therefore: SC's definition fails to cover all PLPA-relevant terrain.

   Caveat: This does not prove the SC intended to operationalize PLPA § 3
   via the 100m threshold. The definition may serve mining regulation purposes
   distinct from erosion prevention. The critique is that if the definition is
   applied to PLPA-protected areas, it under-protects relative to PLPA's purpose. *)

Theorem slope_8x_threshold : m_slope W > 8 * threshold_erosion.
Proof. unfold W, m_slope, threshold_erosion; simpl; lra. Qed.

Theorem exclusion_majority : N_below / N_total > 1/2.
Proof. unfold N_below, N_total; lra. Qed.

Theorem fsi_exclusion_exceeds_90pct : (N_fsi_total - N_fsi_above) / N_fsi_total > 9/10.
Proof. unfold N_fsi_total, N_fsi_above; lra. Qed.

Lemma counts_coherent : N_above + N_below = N_total.
Proof. unfold N_above, N_below, N_total; lra. Qed.

(* Results conditional on geological/ecological assumptions *)

Section Conditional.
  Hypothesis H_geo : g_fracture_density W_geo > 0 /\ g_weathered_thickness W_geo > 0.
  Hypothesis H_eco : e_vegetation W_eco > 0.

  Theorem W_recharges : recharges_groundwater W_hill.
  Proof.
    unfold recharges_groundwater, has_recharge_geology; split.
    - unfold W_hill, h_geo; simpl; exact H_geo.
    - unfold W_hill, h_morph, m_slope, threshold_recharge_slope; simpl; lra.
  Qed.

  Theorem W_prevents_erosion : prevents_erosion W_hill.
  Proof.
    unfold prevents_erosion; split.
    - unfold W_hill, h_morph; simpl; exact W_erosion_susceptible.
    - unfold has_vegetation, W_hill, h_eco; simpl; exact H_eco.
  Qed.

  Theorem W_functional : plpa_functional W_hill.
  Proof. left; exact W_prevents_erosion. Qed.

  Theorem W_doubly_functional : prevents_erosion W_hill /\ recharges_groundwater W_hill.
  Proof. split; [exact W_prevents_erosion | exact W_recharges]. Qed.
End Conditional.

Lemma H_geo_verified : g_fracture_density W_geo > 0 /\ g_weathered_thickness W_geo > 0.
Proof. unfold W_geo; simpl; lra. Qed.

Lemma H_eco_verified : e_vegetation W_eco > 0.
Proof. unfold W_eco; simpl; lra. Qed.

Theorem W_functional_inst : plpa_functional W_hill.
Proof. apply W_functional. exact H_eco_verified. Qed.

(* SC 2025 INSC 1338 inclusion envelope.

   The definition includes:
   (a) Any landform with relief >= 100m (qualifies directly)
   (b) Supporting slopes: sub-100m terrain adjacent to and sloping toward a
       qualifying hill, lying within its base contour envelope
   (c) Associated landforms: sub-100m terrain sharing geological formation or
       drainage basin with a qualifying hill, within proximity
   (d) Range corridors: if two qualifying hills have base contours within 500m,
       intervening terrain is included *)

Definition hill_distance (h1 h2 : Hill) : R :=
  let dlat := m_lat (h_morph h1) - m_lat (h_morph h2) in
  let dlon := m_lon (h_morph h1) - m_lon (h_morph h2) in
  111000 * sqrt (dlat * dlat + dlon * dlon).

Definition relief (h : Hill) : R := m_relief (h_morph h).
Definition peak (h : Hill) : R := m_peak (h_morph h).
Definition base (h : Hill) : R := m_base (h_morph h).
Definition lithology (h : Hill) : Lithology := g_lithology (h_geo h).
Definition qualifies_hill (h : Hill) : Prop := qualifies (h_morph h).

(* Contour distance: horizontal separation minus hill radii (approximating
   distance between base contour edges) *)
Definition contour_distance (h1 h2 : Hill) : R :=
  hill_distance h1 h2 - relief h1 / 2 - relief h2 / 2.

(* Contours adjacent: horizontal distance within sum of radii + 50m buffer *)
Definition contours_adjacent (h1 h2 : Hill) : Prop :=
  hill_distance h1 h2 <= 50 + (relief h1 + relief h2) / 2.

(* Within range proximity: contour edges within 500m *)
Definition within_range_proximity (h1 h2 : Hill) : Prop :=
  contour_distance h1 h2 <= threshold_proximity.

(* Elevation relationship: h_slope lies on the flanks of h_peak *)
Definition slopes_toward (h_slope h_peak : Hill) : Prop :=
  base h_slope >= base h_peak /\ peak h_slope <= peak h_peak.

(* Supporting slope: sub-100m terrain adjacent to and sloping toward qualifying hill *)
Definition is_supporting_slope (h hq : Hill) : Prop :=
  qualifies_hill hq /\
  contours_adjacent h hq /\
  slopes_toward h hq.

(* Geological/hydrological association *)
Definition same_formation (h1 h2 : Hill) : Prop := lithology h1 = lithology h2.

Definition shares_drainage_basin (h1 h2 : Hill) : Prop :=
  base h1 = base h2 \/ Rabs (base h1 - base h2) <= 10.

(* Associated landform: shares geology or hydrology, within proximity *)
Definition is_associated_landform (h hq : Hill) : Prop :=
  qualifies_hill hq /\
  (contours_adjacent h hq \/ within_range_proximity h hq) /\
  (same_formation h hq \/ shares_drainage_basin h hq).

(* Range: two qualifying hills with contours within 500m *)
Definition forms_range (h1 h2 : Hill) : Prop :=
  qualifies_hill h1 /\ qualifies_hill h2 /\ h1 <> h2 /\
  within_range_proximity h1 h2.

(* Intervening terrain: lies between two hills forming a range *)
Definition between_contours (h h1 h2 : Hill) : Prop :=
  let d12 := contour_distance h1 h2 in
  let d1 := contour_distance h h1 in
  let d2 := contour_distance h h2 in
  d1 <= d12 /\ d2 <= d12 /\ d1 + d2 <= d12 + threshold_proximity.

Definition is_intervening (h h1 h2 : Hill) : Prop :=
  forms_range h1 h2 /\ between_contours h h1 h2.

(* Full inclusion predicate per SC 2025 INSC 1338 *)
Definition included (h : Hill) (U : Ensemble Hill) : Prop :=
  qualifies_hill h \/
  (exists hq, In Hill U hq /\ is_supporting_slope h hq) \/
  (exists hq, In Hill U hq /\ is_associated_landform h hq) \/
  (exists h1 h2, In Hill U h1 /\ In Hill U h2 /\ is_intervening h h1 h2).

Definition standalone_excluded (h : Hill) (U : Ensemble Hill) : Prop :=
  ~qualifies_hill h /\
  (forall hq, In Hill U hq -> ~is_supporting_slope h hq) /\
  (forall hq, In Hill U hq -> ~is_associated_landform h hq) /\
  (forall h1 h2, In Hill U h1 -> In Hill U h2 -> ~is_intervening h h1 h2).

Definition isolated (h : Hill) (U : Ensemble Hill) : Prop :=
  forall hq, In Hill U hq -> qualifies_hill hq -> hill_distance h hq > threshold_isolation.

(* The dataset: all hills in Aravalli districts identified via DEM analysis.
   Membership in Aravalli implies location in an Aravalli district per SC Def. 7.1.1. *)
Parameter Aravalli : Ensemble Hill.

(* AXIOMS *)
Axiom relief_bounded : forall h, relief h <= 2000.
Axiom W_isolated : isolated W_hill Aravalli. (* verified: nearest qualifying hill >10km *)

(* Lemmas from isolation *)

Lemma far_not_adjacent : forall h1 h2,
  hill_distance h1 h2 > threshold_isolation -> ~contours_adjacent h1 h2.
Proof.
  intros h1 h2 Hfar Hadj.
  unfold contours_adjacent in Hadj.
  pose proof (relief_bounded h1); pose proof (relief_bounded h2).
  unfold threshold_isolation in Hfar; lra.
Qed.

Lemma far_not_in_range : forall h1 h2,
  hill_distance h1 h2 > threshold_isolation -> ~within_range_proximity h1 h2.
Proof.
  intros h1 h2 Hfar Hprox.
  unfold within_range_proximity, contour_distance in Hprox.
  pose proof (relief_bounded h1); pose proof (relief_bounded h2).
  unfold threshold_isolation, threshold_proximity in *; lra.
Qed.

Lemma far_not_between : forall h h1 h2,
  hill_distance h h1 > threshold_isolation -> forms_range h1 h2 -> ~between_contours h h1 h2.
Proof.
  intros h h1 h2 Hfar [_ [_ [_ Hprox]]] [Hd1 _].
  unfold within_range_proximity, contour_distance in Hprox.
  unfold between_contours, contour_distance in Hd1.
  pose proof (relief_bounded h); pose proof (relief_bounded h1); pose proof (relief_bounded h2).
  unfold threshold_isolation, threshold_proximity in *; lra.
Qed.

Theorem W_not_qualifies : ~qualifies_hill W_hill.
Proof.
  unfold qualifies_hill, qualifies, W_hill, h_morph, W, m_relief, threshold_relief.
  simpl; lra.
Qed.

Lemma W_not_supporting_slope : forall hq, In Hill Aravalli hq -> ~is_supporting_slope W_hill hq.
Proof.
  intros hq Hin [Hq [Hadj _]].
  pose proof (W_isolated hq Hin Hq) as Hfar.
  exact (far_not_adjacent _ _ Hfar Hadj).
Qed.

Lemma W_not_associated : forall hq, In Hill Aravalli hq -> ~is_associated_landform W_hill hq.
Proof.
  intros hq Hin [Hq [Hconn _]].
  pose proof (W_isolated hq Hin Hq) as Hfar.
  destruct Hconn as [Hadj | Hprox].
  - exact (far_not_adjacent _ _ Hfar Hadj).
  - exact (far_not_in_range _ _ Hfar Hprox).
Qed.

Lemma W_not_intervening : forall h1 h2,
  In Hill Aravalli h1 -> In Hill Aravalli h2 -> ~is_intervening W_hill h1 h2.
Proof.
  intros h1 h2 Hin1 Hin2 [Hrange Hbet].
  destruct Hrange as [Hq1 [Hq2 [Hneq Hprox]]].
  pose proof (W_isolated h1 Hin1 Hq1) as Hfar.
  assert (Hforms : forms_range h1 h2) by (unfold forms_range; auto).
  exact (far_not_between W_hill h1 h2 Hfar Hforms Hbet).
Qed.

Theorem W_standalone_excluded : standalone_excluded W_hill Aravalli.
Proof.
  unfold standalone_excluded; repeat split.
  - exact W_not_qualifies.
  - exact W_not_supporting_slope.
  - exact W_not_associated.
  - exact W_not_intervening.
Qed.

Theorem full_under_inclusive : exists h, standalone_excluded h Aravalli /\ plpa_relevant (h_morph h).
Proof.
  exists W_hill; split; [exact W_standalone_excluded | exact W_plpa_relevant].
Qed.

Theorem full_under_inclusive_functional : exists h, standalone_excluded h Aravalli /\ plpa_functional h.
Proof.
  exists W_hill; split; [exact W_standalone_excluded | exact W_functional_inst].
Qed.

(* Summary

   Unconditional (morphometric):
     under_inclusive, exclusion_majority, fsi_exclusion_exceeds_90pct

   Conditional on W_geo/W_eco values:
     W_functional_inst

   Conditional on W_isolated axiom (dataset-specific):
     W_standalone_excluded, full_under_inclusive, full_under_inclusive_functional

   Parameters:
     Aravalli : Ensemble Hill (the DEM-identified dataset)

   Axioms:
     relief_bounded (physical: Aravalli max ~1722m)
     W_isolated (empirically verifiable: nearest qualifying hill in Aravalli >10km from W)

   IMPORTANT DISTINCTION:
     - excluded(m) := relief < 100m (fails threshold)
     - standalone_excluded(h, U) := excluded AND not in any qualifying hill's
       envelope AND not in any range corridor

   The SC definition includes sub-100m terrain if it lies within a qualifying
   hill's base contour or within a range corridor. Thus:
     "relief < 100m" does NOT imply "legally excluded"

   The aggregate statistics (57%, 91%) count threshold-excluded hills.
   The actual legally excluded area is smaller (per MoEF&CC Dec 2025 clarification).
   Our W is specifically chosen to be STANDALONE excluded (isolated). *)

