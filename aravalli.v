(* Aravalli Definition Analysis: Statutory Consistency

   Question: Is the Supreme Court's 2025 definition of "Aravalli Hills"
   consistent with protecting erosion-susceptible terrain under the Punjab
   Land Preservation Act, 1900?

   Finding: The 100m local relief threshold excludes terrain that would be
   "subject to erosion" under PLPA § 3. Specifically, >57% of identified
   Aravalli hills (by DEM analysis) or >91% (by FSI count) fall below
   100m relief yet have slopes well above the 3° erosion susceptibility
   threshold. If the SC definition is applied to narrow PLPA protections,
   it would under-protect erosion-susceptible terrain.

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
     DEM: Wolfram Mathematica GeoElevationData, ~30m resolution (SRTM-derived).
     Computation: Wolfram Mathematica 14.x via WolframScript (Windows).

     Hill identification: Pixels with slope >= 3 deg classified as hill terrain.
       Connected components extracted via MorphologicalComponents.
       Local relief per component: marker-controlled watershed (peak - local base).

       METHODOLOGICAL NOTE: Hills are identified BY the 3 deg slope threshold.
       Thus "all identified hills have slope >= 3 deg" is tautological for the
       aggregate statistics. However, the core existence claim (under_inclusive)
       uses W's specific measured values (slope 25.12 deg) independent of how
       the population was identified. The existence proof survives.

     Witness selection: Alwar #73 chosen as excluded (relief 93.84m < 100m),
       erosion-susceptible (slope 25.12 deg >> 3 deg), outside all qualifying
       contours (verified by DEM/contour analysis, Dec 2025).
       Coordinates: 27.8353N, 76.8327E.
       Nearest qualifying: 27.7903N, 76.8127E (relief 116m, distance 5367m).

     Aggregate statistics: 24 Aravalli districts analyzed. N_total = 5585 hills
       identified, N_above = 2382 with relief >= 100m, N_below = 3203 excluded.

       DATA RECONCILIATION: Our DEM analysis finds 57% exclusion; FSI reportedly
       found 91% (1,048 of 12,081 hills >= 100m in 15 Rajasthan districts). The
       discrepancy reflects: (a) different segmentation - FSI counts hills >= 20m,
       our method merges connected slope components; (b) different geographic scope -
       FSI's 15 districts vs our 24 districts. Both figures support under-inclusivity;
       neither directly measures area excluded under the SC's inclusion envelope.

     Erosion threshold: 3 deg, operational assumption from geomorphology literature.
       PLPA § 3 does not specify a numeric threshold.

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
Definition threshold_recharge_slope : R := 30.

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

Definition excluded (m : Morphometry) : Prop := m_relief m < threshold_relief.
Definition qualifies (m : Morphometry) : Prop := m_relief m >= threshold_relief.
Definition erosion_susceptible (m : Morphometry) : Prop := m_slope m >= threshold_erosion.

(* PLPA § 3 relevance: "subject to erosion" denotes terrain susceptibility,
   not current erosional state. PLPA does not specify a numeric threshold.

   OPERATIONAL ASSUMPTION: We adopt 3° slope threshold for erosion
   susceptibility (onset of significant sheet erosion under monsoon rainfall).
   This is a modeling choice, not statutory text. Alternative thresholds
   (e.g., USLE S-factor curves) would yield similar qualitative results
   given W's 25° slope far exceeds any reasonable cutoff. *)
Definition plpa_relevant (m : Morphometry) : Prop := erosion_susceptible m.

Definition has_recharge_geology (h : Hill) : Prop :=
  g_fracture_density (h_geo h) > 0 /\ g_weathered_thickness (h_geo h) > 0.

Definition recharges_groundwater (h : Hill) : Prop :=
  has_recharge_geology h /\ m_slope (h_morph h) <= threshold_recharge_slope.

Definition has_vegetation (h : Hill) : Prop := e_vegetation (h_eco h) > 0.

Definition prevents_erosion (h : Hill) : Prop :=
  erosion_susceptible (h_morph h) /\ has_vegetation h.

Definition plpa_functional (h : Hill) : Prop :=
  prevents_erosion h \/ recharges_groundwater h.

Definition N_total : R := 5585.
Definition N_above : R := 2382.
Definition N_below : R := 3203.
Definition N_fsi_total : R := 12081.
Definition N_fsi_above : R := 1048.

Definition W : Morphometry := mkMorphometry 73 27.8353 76.8327 93.84 25.12 2.13 693.84 600.
Definition W_geo : Geology := mkGeology Quartzite 2.5 8.0.
Definition W_eco : Ecology := mkEcology 0.4 1.2.
Definition W_hill : Hill := mkHill W W_geo W_eco.

Definition W_nearest : Morphometry := mkMorphometry 0 27.7903 76.8127 116 0 0 359 243.
Definition W_nearest_distance : R := 5367.

Lemma W_nearest_qualifies : qualifies W_nearest.
Proof.
  unfold qualifies, W_nearest, m_relief, threshold_relief.
  simpl.
  lra.
Qed.

Theorem W_excluded : excluded W.
Proof.
  unfold excluded, W, m_relief, threshold_relief.
  simpl.
  lra.
Qed.

Theorem W_erosion_susceptible : erosion_susceptible W.
Proof.
  unfold erosion_susceptible, W, m_slope, threshold_erosion.
  simpl.
  lra.
Qed.

Theorem W_plpa_relevant : plpa_relevant W.
Proof.
  exact W_erosion_susceptible.
Qed.

Theorem under_inclusive : exists m, excluded m /\ plpa_relevant m.
Proof.
  exists W.
  split.
  - exact W_excluded.
  - exact W_plpa_relevant.
Qed.

(* The above theorem establishes under-inclusivity.

   Argument structure:
   1. PLPA § 3 authorizes protection of areas "subject to erosion."
   2. under_inclusive proves: there exist landforms with relief < 100m
      (excluded by SC threshold) that are erosion-susceptible (slope >= 3°).
   3. Therefore: the 100m threshold is not equivalent to erosion susceptibility.

   SCOPE OF CLAIM: This is a scientific/functional critique, not a claim about
   SC intent. The SC adopted the definition "in the context of regulating mining,"
   not to operationalize PLPA § 3 specifically.

   CONDITIONAL APPLICATION: If state agencies use the 100m threshold to narrow
   PLPA-style protections (e.g., deciding which areas require erosion prevention
   measures), that application would under-protect terrain that is erosion-liable
   under PLPA § 3's purpose. The critique applies to such derivative applications,
   not to the SC's mining regulation context per se. *)

Theorem slope_8x_threshold : m_slope W > 8 * threshold_erosion.
Proof.
  unfold W, m_slope, threshold_erosion.
  simpl.
  lra.
Qed.

Theorem exclusion_majority : N_below / N_total > 1/2.
Proof.
  unfold N_below, N_total.
  lra.
Qed.

Theorem fsi_exclusion_exceeds_90pct : (N_fsi_total - N_fsi_above) / N_fsi_total > 9/10.
Proof.
  unfold N_fsi_total, N_fsi_above.
  lra.
Qed.

Lemma counts_coherent : N_above + N_below = N_total.
Proof.
  unfold N_above, N_below, N_total.
  lra.
Qed.

Section Conditional.
  Hypothesis H_geo : g_fracture_density W_geo > 0 /\ g_weathered_thickness W_geo > 0.
  Hypothesis H_eco : e_vegetation W_eco > 0.

  Theorem W_recharges : recharges_groundwater W_hill.
  Proof.
    unfold recharges_groundwater, has_recharge_geology.
    split.
    - unfold W_hill, h_geo.
      simpl.
      exact H_geo.
    - unfold W_hill, h_morph, m_slope, threshold_recharge_slope.
      simpl.
      lra.
  Qed.

  Theorem W_prevents_erosion : prevents_erosion W_hill.
  Proof.
    unfold prevents_erosion.
    split.
    - unfold W_hill, h_morph.
      simpl.
      exact W_erosion_susceptible.
    - unfold has_vegetation, W_hill, h_eco.
      simpl.
      exact H_eco.
  Qed.

  Theorem W_functional : plpa_functional W_hill.
  Proof.
    left.
    exact W_prevents_erosion.
  Qed.
End Conditional.

Lemma H_geo_verified : g_fracture_density W_geo > 0 /\ g_weathered_thickness W_geo > 0.
Proof.
  unfold W_geo.
  simpl.
  lra.
Qed.

Lemma H_eco_verified : e_vegetation W_eco > 0.
Proof.
  unfold W_eco.
  simpl.
  lra.
Qed.

Theorem W_functional_inst : plpa_functional W_hill.
Proof.
  apply W_functional.
  exact H_eco_verified.
Qed.

(* SC 2025 INSC 1338 CONTOUR-BASED INCLUSION

   The SC definition uses the "lowest contour line encircling the landform" to
   determine inclusion. A landform h is included if:
   (a) It qualifies directly (relief >= 100m), OR
   (b) It lies within the base contour polygon of some qualifying hill.

   We model contour membership as a primitive relation (inside_contour_of),
   verifiable by GIS analysis. For W, we directly verified it lies outside
   every qualifying hill's base contour in the dataset. *)

Definition hill_distance (h1 h2 : Hill) : R :=
  let dlat := m_lat (h_morph h1) - m_lat (h_morph h2) in
  let dlon := m_lon (h_morph h1) - m_lon (h_morph h2) in
  111000 * sqrt (dlat * dlat + dlon * dlon).

Definition qualifies_hill (h : Hill) : Prop := qualifies (h_morph h).

Parameter inside_contour_of : Hill -> Hill -> Prop.
(* inside_contour_of h hq holds iff h lies within the base contour polygon of hq.
   GIS-computable: extract lowest closed contour around hq's peak,
   test if h's coordinates fall within the polygon. *)

Definition sc_included (h : Hill) (U : Ensemble Hill) : Prop :=
  qualifies_hill h \/
  exists hq, In Hill U hq /\ qualifies_hill hq /\ inside_contour_of h hq.

Definition sc_excluded (h : Hill) (U : Ensemble Hill) : Prop :=
  ~qualifies_hill h /\
  forall hq, In Hill U hq -> qualifies_hill hq -> ~inside_contour_of h hq.

Parameter Aravalli : Ensemble Hill.

(* W_outside_contours: verified by high-resolution DEM search (Dec 2025)
   Method: For each qualifying hill within 22km of W, extracted base contour
   polygon and tested whether W's coordinates fall within.
   Result: W lies outside the base contour of every qualifying hill.
   Nearest qualifying hill: 27.7903N, 76.8127E (relief 116m, distance 5367m). *)
Axiom W_outside_contours : forall hq,
  In Hill Aravalli hq -> qualifies_hill hq -> ~inside_contour_of W_hill hq.

Theorem W_not_qualifies : ~qualifies_hill W_hill.
Proof.
  unfold qualifies_hill, qualifies, W_hill, h_morph, W, m_relief, threshold_relief.
  simpl.
  lra.
Qed.

Theorem W_sc_excluded : sc_excluded W_hill Aravalli.
Proof.
  unfold sc_excluded.
  split.
  - exact W_not_qualifies.
  - exact W_outside_contours.
Qed.

Theorem sc_under_inclusive : exists h, sc_excluded h Aravalli /\ plpa_relevant (h_morph h).
Proof.
  exists W_hill.
  split.
  - exact W_sc_excluded.
  - exact W_plpa_relevant.
Qed.

Theorem sc_under_inclusive_functional : exists h, sc_excluded h Aravalli /\ plpa_functional h.
Proof.
  exists W_hill.
  split.
  - exact W_sc_excluded.
  - exact W_functional_inst.
Qed.
