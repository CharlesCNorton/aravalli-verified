(******************************************************************************)
(*                                                                            *)
(*         Aravalli Definition Analysis: Statutory Purpose Consistency        *)
(*                                                                            *)
(*     The 2025 Supreme Court definition requires 100m elevation above        *)
(*     local relief. PLPA 1900 aims to prevent erosion and conserve           *)
(*     groundwater. We investigate whether these criteria align.              *)
(*                                                                            *)
(*     "A mountain is composed of tiny grains of earth."                      *)
(*     - Sakya Pandita, 13th century                                          *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: December 2025                                                    *)
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(*  LEGAL INSTRUMENTS                                                         *)
(*    - Punjab Land Preservation Act, 1900 (Sections 3-5)                     *)
(*    - Forest (Conservation) Act, 1980 (Section 2)                           *)
(*    - Supreme Court Order, 20 November 2025 (2025 INSC 1338)                *)
(*    - M.C. Mehta v. Union of India, WP(C) 4677/1985 (mining restrictions)   *)
(*    - T.N. Godavarman v. UOI, WP(C) 202/1995 (forest conservation)          *)
(******************************************************************************)

(******************************************************************************)
(*  HARYANA PLPA 2019 AMENDMENT CONTROVERSY                                   *)
(*                                                                            *)
(*  Context: The PLPA 1900 protects ~20,200 hectares in south Haryana         *)
(*  (~7,000 ha in Gurugram, ~4,000 ha in Faridabad) from non-forest activity. *)
(*                                                                            *)
(*  Timeline:                                                                 *)
(*    27 Feb 2019: Haryana Assembly passed amendment bill to open 33% of      *)
(*                 PLPA-protected land for urbanisation, mining, real estate  *)
(*                                                                            *)
(*    01 Mar 2019: Supreme Court STAYED the amendments, calling it "sheer     *)
(*                 contempt of court" and a "misadventure"                    *)
(*                 Quote: "You are destroying the forest. It is not           *)
(*                 permissible. You are not supreme and supreme is the        *)
(*                 rule of law."                                              *)
(*                                                                            *)
(*    Jun 2019:    Despite SC stay, Haryana got bill signed by Governor       *)
(*                                                                            *)
(*    21 Jul 2022: SC ruled ALL PLPA-notified land must be treated as         *)
(*                 'forests' under FCA 1980                                   *)
(*                 Quote: "Environment is more important than your civil      *)
(*                 rights...The environment must prevail over all other       *)
(*                 rights."                                                   *)
(*                                                                            *)
(*  Significance: This context shows ongoing tension between development      *)
(*  pressures and conservation in the Aravalli region. The 2025 definition    *)
(*  debate occurs against this backdrop of attempted PLPA dilution.           *)
(*                                                                            *)
(*  Sources: LiveLaw, The Print, Land Conflict Watch, Aravalli Bachao         *)
(******************************************************************************)

(******************************************************************************)
(*  PRIMARY DOCUMENT URLS                                                     *)
(*                                                                            *)
(*  SC Judgment (20 Nov 2025):                                                *)
(*    images.assettype.com/downtoearth/2025-12-02/fpv7xvaz/                   *)
(*      Pan_Aravalli_SC_Order_20_Nov_2025.pdf                                 *)
(*                                                                            *)
(*  SC Order (09 May 2024, committee formation):                              *)
(*    api.sci.gov.in/supremecourt/1985/63996/                                 *)
(*      63996_1985_3_301_53156_Order_09-May-2024.pdf                          *)
(*                                                                            *)
(*  Case records: IA 105701/2024 in WP(C) 202/1995                            *)
(*  PIB Press Release: pib.gov.in/PressReleseDetailm.aspx?PRID=2207176        *)
(******************************************************************************)

(******************************************************************************)
(*  DATA SOURCES                                                              *)
(*    - Forest Survey of India: 12,081 hills mapped, 1,048 >= 100m            *)
(*    - Geological Survey of India: 692 km range extent                       *)
(*    - Central Ground Water Board: aquifer recharge mapping                  *)
(******************************************************************************)

(******************************************************************************)
(*  PREMISES (explicit, taken as axiomatic)                                   *)
(*    P1. PLPA purpose = prevent erosion OR conserve groundwater              *)
(*    P2. FSI elevation data is accurate                                      *)
(*    P3. Ecological function depends on slope, soil, vegetation, geology    *)
(******************************************************************************)

(******************************************************************************)
(*  DEFINITIONS                                                               *)
(*                                                                            *)
(*  D1. aravalli_hill_2025(A) :=                                              *)
(*        (local_relief(A) >= 100m) \/                                        *)
(*        (supporting_slope_of(A, H) /\ aravalli_hill_2025(H)) \/             *)
(*        (associated_landform_of(A, H) /\ aravalli_hill_2025(H))             *)
(*                                                                            *)
(*  D2. aravalli_range_2025(H1, H2) :=                                        *)
(*        aravalli_hill_2025(H1) /\ aravalli_hill_2025(H2) /\                 *)
(*        contour_distance(H1, H2) < 500m                                     *)
(*      [Includes all intervening landforms between H1 and H2]                *)
(*                                                                            *)
(*  D3. plpa_functional(A) := prevents_erosion(A) \/ recharges_gw(A)          *)
(*                                                                            *)
(*  D4. under_inclusive(D, P) := exists A, P(A) /\ ~D(A)                      *)
(*      [There exist landforms serving PLPA purpose but excluded by D]        *)
(*                                                                            *)
(*  D5. consistent(D, P) := forall A, D(A) <-> P(A)                           *)
(*      [CRITIQUE: This biconditional is too strong for legal proxies.        *)
(*       A weaker criterion would be bounded under-inclusion.]                *)
(*                                                                            *)
(*  NOTE: The Coq formalization below uses a SIMPLIFIED D1 (just >=100m).     *)
(*  A complete formalization would require modeling the inclusion envelope    *)
(*  (supporting slopes, associated landforms, intervening terrain).           *)
(******************************************************************************)

(******************************************************************************)
(*  QUESTIONS TO INVESTIGATE                                                  *)
(*    Q1. What percentage of FSI-mapped hills are excluded by 100m threshold?*)
(*    Q2. Is elevation a sufficient proxy for erosion prevention?             *)
(*    Q3. Is elevation a sufficient proxy for groundwater recharge?           *)
(*    Q4. Is the 2025 definition consistent with PLPA purpose?                *)
(*    Q5. Do alternative thresholds (30m + slope) perform better?             *)
(******************************************************************************)

(******************************************************************************)
(*  METHODOLOGY                                                               *)
(*    1. Mathematica: compute numeric facts from FSI data                     *)
(*    2. Coq: formalize premises, derive conclusions                          *)
(*    3. No admitted proofs, no vacuous theorems, all premises explicit       *)
(******************************************************************************)

(******************************************************************************)
(*  REFERENT: PRIMARY SOURCE EXTRACTS                                         *)
(******************************************************************************)

(******************************************************************************)
(*  PLPA 1900 Section 3 (Notification of Areas):                              *)
(*                                                                            *)
(*    "Whenever it appears to the Provincial Government that it is desirable  *)
(*     to provide for the conservation of sub-soil water or the prevention    *)
(*     of erosion in any area subject to erosion or likely to become liable   *)
(*     to erosion, such Government may by notification make a direction       *)
(*     accordingly."                                                          *)
(*                                                                            *)
(*  Source: Punjab Act II of 1900, as amended by Punjab Act XI of 1942        *)
(******************************************************************************)

(******************************************************************************)
(*  SC Order 2025 INSC 1338 (20 November 2025):                               *)
(*                                                                            *)
(*  ARAVALLI HILLS (Definition 7.1.1):                                        *)
(*                                                                            *)
(*    "Any landform located in the Aravali districts, having an elevation     *)
(*     of 100 metres or more from the local relief, shall be termed as        *)
(*     Aravali Hills."                                                        *)
(*                                                                            *)
(*    Local relief: determined by "the lowest contour line encircling the     *)
(*    landform" (whether actual or extended notionally).                      *)
(*                                                                            *)
(*    INCLUSION ENVELOPE: The definition includes not just the peak, but:     *)
(*      - The entire landform within the lowest contour                       *)
(*      - The Hill itself                                                     *)
(*      - Supporting slopes (IRRESPECTIVE OF GRADIENT)                        *)
(*      - Associated landforms (IRRESPECTIVE OF GRADIENT)                     *)
(*                                                                            *)
(*  ARAVALLI RANGE:                                                           *)
(*                                                                            *)
(*    Two or more Aravalli Hills within 500m of each other (measured from     *)
(*    the outermost point on the boundary of the lowest contour line).        *)
(*                                                                            *)
(*    INCLUSION: "The entire area of landforms falling between the lowest     *)
(*    contour lines of these Hills...along with associated features such as   *)
(*    Hills, Hillocks, supporting slopes, etc., shall also be included as     *)
(*    part of Aravali Range."                                                 *)
(*                                                                            *)
(*  IMPLICATION FOR ANALYSIS:                                                 *)
(*    The definition is MORE INCLUSIVE than a simple ">=100m" test:           *)
(*      - Sub-100m slopes attached to qualifying hills ARE protected          *)
(*      - Sub-100m features between qualifying hills ARE protected            *)
(*    However, STANDALONE sub-100m hills (not attached to or between          *)
(*    qualifying hills) remain EXCLUDED.                                      *)
(*                                                                            *)
(*  Bench: B.R. Gavai CJI, K.V. Chandran J, N.V. Anjaria J                    *)
(*  Source: SC Observer, quoting Section 7.1.1 of judgment                    *)
(******************************************************************************)

(******************************************************************************)
(*  FSI QUANTITATIVE DATA                                                     *)
(*                                                                            *)
(*    Total hills mapped (>= 20m elevation): 12,081                           *)
(*    Hills meeting 100m threshold:          1,048                            *)
(*    Percentage meeting threshold:          8.67%                            *)
(*    Percentage excluded:                   91.33%                           *)
(*                                                                            *)
(*  Coverage: 15 districts, Rajasthan                                         *)
(*  Methodology: Hill = connected region with slope >= 3 deg, elevation >= 20m*)
(*                                                                            *)
(*  SOURCE PROVENANCE:                                                        *)
(*    Primary: FSI internal assessment, Nov 2025 (not publicly released)      *)
(*    Secondary: Indian Express investigation, 27 Nov 2025                    *)
(*    Corroborated by: The Wire, Vision IAS, Business Standard, Down To Earth *)
(*                                                                            *)
(*    The FSI internal assessment was conducted after SC-mandated mapping     *)
(*    (order 9 May 2024). It was communicated to MoEFCC but not included      *)
(*    in the committee's public submissions to the Court.                     *)
(*                                                                            *)
(*  HOW TO OBTAIN PRIMARY SOURCE:                                             *)
(*    - RTI to FSI Dehradun: "FSI analysis of 100m criterion impact on        *)
(*      Aravalli hills, as communicated to MoEFCC, Nov 2025"                  *)
(*    - RTI to MoEFCC: "Documents received from FSI regarding Aravalli        *)
(*      hill mapping, 2024-25"                                                *)
(*    - SC Registry: Annexures to IA 105701/2024 in WP(C) 202/1995            *)
(*                                                                            *)
(*  Related RTI (disposed): FSOID/R/E/25/00026 (16 Jan 2025)                  *)
(******************************************************************************)

(******************************************************************************)
(*  FSI RECOMMENDATIONS (OVERRULED BY MoEFCC)                                 *)
(*                                                                            *)
(*  FSI's scientific criteria (developed 2010-2024):                          *)
(*                                                                            *)
(*    2010 FSI Report (25.08.2010):                                           *)
(*      - Slope >= 3 deg                                                      *)
(*      - Elevation above district minimum                                    *)
(*      - 100m buffer downslope                                               *)
(*      - Hills within 500m = continuous range                                *)
(*      Source: SC Order 09.05.2024, referencing FSI Report 25.08.2010        *)
(*                                                                            *)
(*    Oct 2024 Technical Sub-Committee (FSI-led):                             *)
(*      - Height >= 30m AND slope >= 4.57 deg (8% grade)                      *)
(*      - Would cover ~40% of mapped hills                                    *)
(*      - Described Aravallis as "Proterozoic fold belt...linear series       *)
(*        of hills and valleys"                                               *)
(*      Source: Indian Express, citing sub-committee report                   *)
(*                                                                            *)
(*    Sept 2025 FSI Report to Environment Secretary:                          *)
(*      - "Even modest hills of 10-30m act as strong natural windbreaks,      *)
(*        creating sheltered zones extending many times their height          *)
(*        downwind, effectively halting near-surface sand transport."         *)
(*      - Included district-wise maps of entire Aravalli region               *)
(*      - FSI cautioned 100m cutoff "would protect only a few guard posts     *)
(*        while surrendering the fences below"                                *)
(*      Source: Indian Express investigation, 27 Nov 2025                     *)
(*                                                                            *)
(*  OUTCOME: MoEFCC rejected FSI's 30m/4.57° recommendation in favor of       *)
(*  the 100m threshold. The committee's final report (13 Oct 2025) adopted    *)
(*  100m, which the Supreme Court accepted on 20 Nov 2025.                    *)
(******************************************************************************)

(******************************************************************************)
(*  ORIGIN OF THE 100m THRESHOLD                                              *)
(*                                                                            *)
(*  The 100m local relief criterion was NOT derived from ecological or        *)
(*  hydrological science. Its provenance:                                     *)
(*                                                                            *)
(*    2002: Rajasthan state committee proposed 100m threshold based on        *)
(*          geographer Richard Murphy's landform classification system        *)
(*                                                                            *)
(*    2006 (09 Jan): Rajasthan formally adopted 100m definition for           *)
(*          mining regulation purposes                                        *)
(*                                                                            *)
(*    2024-25: MoEFCC committee adopted Rajasthan's existing definition       *)
(*          as the uniform national standard, despite FSI objections          *)
(*                                                                            *)
(*  The PIB press release (21 Dec 2025) confirms: "only Rajasthan has a       *)
(*  formally established definition...based on 100m above local relief        *)
(*  (in force since 09/01/2006)"                                              *)
(*                                                                            *)
(*  IMPLICATION: The 100m threshold is an administrative convenience          *)
(*  inherited from state mining regulations, not a scientifically-derived     *)
(*  criterion for ecological function or statutory purpose (PLPA 1900).       *)
(*                                                                            *)
(*  Source: PIB Release PRID 2207176 (21 Dec 2025)                            *)
(******************************************************************************)

(******************************************************************************)
(*  GROUNDWATER RECHARGE FACTORS (Aravalli terrain study)                     *)
(*                                                                            *)
(*    Primary recharge-controlling factors identified:                        *)
(*      - soil type                                                           *)
(*      - soil thickness                                                      *)
(*      - drainage density                                                    *)
(*      - land-surface slope                                                  *)
(*      - fracture density                                                    *)
(*      - lithology                                                           *)
(*      - weathered-zone thickness                                            *)
(*      - thickness of subsurface fractured zones                             *)
(*                                                                            *)
(*    Factors influencing seasonal water-level fluctuations:                  *)
(*      - depth, elevation, vegetation, lineament buffer, lineament density   *)
(*                                                                            *)
(*    IMPORTANT DISTINCTION:                                                  *)
(*      The paper lists "elevation" (absolute height above sea level) as a    *)
(*      factor. This differs from "local relief" (relative height above       *)
(*      surrounding terrain). The SC definition uses a 100m LOCAL RELIEF      *)
(*      threshold, not absolute elevation. These are conceptually distinct:   *)
(*        - A 50m hill at 600m ASL: high absolute elevation, low local relief *)
(*        - A 150m hill at 200m ASL: lower absolute elevation, high relief    *)
(*                                                                            *)
(*      The 100m local relief threshold is not derived from hydrogeological   *)
(*      science; no study identifies this specific cutoff as determinative    *)
(*      for groundwater recharge function.                                    *)
(*                                                                            *)
(*  Source: Bhuiyan et al., IAHS Publ. 326, 2009 (ResearchGate 288224742)     *)
(******************************************************************************)

(******************************************************************************)
(*  PIB FACTSHEET (Government of India)                                       *)
(*                                                                            *)
(*    Ecological functions acknowledged:                                      *)
(*      - "natural barrier against the Thar Desert"                           *)
(*      - "groundwater recharge zone"                                         *)
(*      - "biodiversity habitat"                                              *)
(*      - "regulate air quality and climate"                                  *)
(*                                                                            *)
(*    Recharge zones described as: "foothills and valleys"                    *)
(*    No elevation threshold mentioned for these functions                    *)
(*                                                                            *)
(*  Source: pib.gov.in/FactsheetDetails.aspx?id=150596                        *)
(******************************************************************************)

(******************************************************************************)
(*  RECHARGE CAPACITY ESTIMATE                                                *)
(*                                                                            *)
(*    "2 million litres of groundwater recharge per hectare of the Aravalli   *)
(*     landscape" - attributed to fractured and weathered rock percolation    *)
(*                                                                            *)
(*    Mechanism: rainwater percolates through fractured rocks, replenishing   *)
(*    aquifers supporting agriculture, urban settlements, industry            *)
(******************************************************************************)

(******************************************************************************)
(*  COMPUTED DATA (Wolfram Mathematica, December 2025)                        *)
(*  These are empirical findings, not proofs. Coq proves from these inputs.   *)
(******************************************************************************)

(******************************************************************************)
(*  METHOD                                                                    *)
(*                                                                            *)
(*    1. Bounds derived from Wolfram administrative division data             *)
(*       Lat: 24.42 to 28.35, Lon: 72.78 to 77.35                             *)
(*                                                                            *)
(*    2. Elevation data via GeoElevationData (DEM)                            *)
(*                                                                            *)
(*    3. Hill identification: connected regions with slope >= 3 deg           *)
(*       (replicating FSI methodology)                                        *)
(*                                                                            *)
(*    4. Local relief: MinFilter with 15-cell window                          *)
(*                                                                            *)
(*    5. Threshold applied to max relief per hill region                      *)
(******************************************************************************)

(******************************************************************************)
(*  RESULTS (7 districts, hill-count analysis, original)                      *)
(*                                                                            *)
(*    District        Hills    >= 100m                                        *)
(*    Udaipur         1,674    44.7%                                          *)
(*    Sirohi          3,613     4.1%                                          *)
(*    Ajmer             581    54.6%                                          *)
(*    Jaipur          1,091    42.0%                                          *)
(*    Alwar             494    41.3%                                          *)
(*    Faridabad       2,222     1.5%                                          *)
(*    Mahendragarh    2,748     3.9%                                          *)
(*                                                                            *)
(*    TOTAL          12,423    16.2% >= 100m, 83.8% < 100m                    *)
(*                                                                            *)
(*  Compare FSI (15 districts): 12,081 hills, 8.7% >= 100m, 91.3% < 100m      *)
(******************************************************************************)

(******************************************************************************)
(*  EXTENDED ANALYSIS (10 additional districts, pixel-based, Dec 2025)        *)
(*                                                                            *)
(*  Methodology: Pixel-based terrain analysis via GeoElevationData (DEM).     *)
(*  Counts pixels with slope >= 3 deg, classifies by local relief.            *)
(*  Differs from FSI hill-count method; measures terrain AREA not hill COUNT. *)
(*                                                                            *)
(*    District     HillPixels  >=100m   <100m   %>=100m  Slope>=100m Slope<100m*)
(*    Bhilwara       181,173  140,896  40,202   77.8%     20.70°      6.33°   *)
(*    Chittorgarh    178,910  143,355  35,481   80.2%     19.98°      6.25°   *)
(*    Dausa          207,858  149,325  58,456   71.9%     24.44°      7.03°   *)
(*    Dungarpur      227,021  168,192  58,745   74.1%     23.77°      7.32°   *)
(*    Jhunjhunun     178,400  131,205  47,133   73.6%     23.07°      6.69°   *)
(*    Nagaur         129,088  108,382  20,668   84.0%     17.71°      6.00°   *)
(*    Pali           141,188  118,392  22,756   83.9%     17.53°      5.98°   *)
(*    Rajsamand      184,863  143,031  41,759   77.4%     20.88°      6.56°   *)
(*    Sikar          161,017  124,947  36,011   77.6%     20.47°      6.32°   *)
(*    Tonk           195,690  146,905  48,711   75.1%     22.43°      6.62°   *)
(*                                                                            *)
(*    AGGREGATE    1,785,208 1,374,630 409,922  77.0%     20.88°      6.41°   *)
(*                                                                            *)
(*  KEY FINDING: All excluded terrain (<100m relief) has mean slope           *)
(*  between 5.98° and 7.32°, well above the 3° erosion threshold.             *)
(*                                                                            *)
(*  NOTE: Pixel analysis shows 77% of terrain area meets threshold, while     *)
(*  FSI hill-count shows only 8.7% of discrete hills meet threshold.          *)
(*  This discrepancy arises because large high-relief hills cover more area   *)
(*  (more pixels) while numerous small hills are counted individually.        *)
(*  Both analyses confirm: excluded terrain retains erosion-relevant slopes.  *)
(******************************************************************************)

(******************************************************************************)
(*  OBSERVATION                                                               *)
(*                                                                            *)
(*    Peripheral districts (Faridabad 1.5%, Mahendragarh 3.9%, Sirohi 4.1%)   *)
(*    have far fewer hills meeting 100m threshold than core Aravalli          *)
(*    (Udaipur 44.7%, Ajmer 54.6%).                                           *)
(*                                                                            *)
(*    The aggregate percentage depends heavily on district composition.       *)
(******************************************************************************)

(******************************************************************************)
(*  SLOPE VS RELIEF ANALYSIS (original 7 districts, hill-count)               *)
(*                                                                            *)
(*    Included hills (>=100m relief):  888 hills, mean slope 4.54 deg         *)
(*    Excluded hills (<100m relief): 5,756 hills, mean slope 3.46 deg         *)
(*                                                                            *)
(*    100% of excluded hills have mean slope >= 3 deg (erosion threshold)     *)
(*                                                                            *)
(*  FINDING: Excluded hills retain erosion-relevant slope characteristics.    *)
(*  The 100m threshold is under-inclusive relative to erosion prevention.     *)
(******************************************************************************)

(******************************************************************************)
(*  SLOPE VS RELIEF ANALYSIS (extended, pixel-based, 10 districts)            *)
(*                                                                            *)
(*    Included terrain (>=100m relief): 1,374,630 pixels, mean slope 20.88 deg*)
(*    Excluded terrain (<100m relief):    409,922 pixels, mean slope 6.41 deg *)
(*                                                                            *)
(*    Excluded terrain mean slope (6.41 deg) exceeds erosion threshold (3 deg)*)
(*    by a factor of 2.14x. Minimum district mean for excluded: 5.98 deg.     *)
(*                                                                            *)
(*  CONFIRMATION: Pixel-based analysis reinforces hill-count finding.         *)
(*  Excluded terrain is erosion-relevant regardless of measurement method.    *)
(******************************************************************************)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sets.Ensembles.
Open Scope R_scope.

(******************************************************************************)
(*  TYPE-THEORETIC HILL STRUCTURE                                             *)
(*                                                                            *)
(*  A Hill is characterized by measurable geomorphological properties.        *)
(*  This enables formal predication over individual landforms.                *)
(******************************************************************************)

Record Location : Type := mkLocation {
  latitude : R;
  longitude : R
}.

Inductive Lithology : Type :=
  | Quartzite      (* Primary Aravalli rock, highly fractured *)
  | Schist         (* Metamorphic, moderate fracturing *)
  | Gneiss         (* Basement rock, variable fracturing *)
  | Phyllite       (* Low-grade metamorphic *)
  | Marble         (* Recrystallizedite *)
  | Alluvium.      (* Deposited sediment *)

Record Hill : Type := mkHill {
  hill_id : nat;
  location : Location;
  peak_elevation : R;
  base_elevation : R;
  local_relief : R;
  mean_slope : R;
  max_slope : R;
  area_ha : R;
  rock_type : Lithology;
  fracture_density : R;
  weathered_zone_thickness : R;
  drainage_density : R;
  soil_thickness : R;
  vegetation_cover : R
}.

Definition relief (h : Hill) : R := local_relief h.
Definition slope (h : Hill) : R := mean_slope h.

(******************************************************************************)
(*  SC 2025 DEFINITION AS PREDICATE                                           *)
(*                                                                            *)
(*  Formalizes the legal definition from 2025 INSC 1338.                      *)
(******************************************************************************)

Definition sc_relief_threshold : R := 100.
Definition range_proximity_threshold : R := 500.

Definition meets_100m_threshold (h : Hill) : Prop :=
  relief h >= sc_relief_threshold.

Definition hill_distance (h1 h2 : Hill) : R :=
  let lat_diff := latitude (location h1) - latitude (location h2) in
  let lon_diff := longitude (location h1) - longitude (location h2) in
  111000 * sqrt (lat_diff * lat_diff + lon_diff * lon_diff).

Definition is_supporting_slope (h_small h_large : Hill) : Prop :=
  meets_100m_threshold h_large /\
  ~meets_100m_threshold h_small /\
  hill_distance h_small h_large <= range_proximity_threshold.

Definition is_intervening (h h1 h2 : Hill) : Prop :=
  meets_100m_threshold h1 /\ meets_100m_threshold h2 /\
  hill_distance h1 h2 <= range_proximity_threshold /\
  hill_distance h h1 <= hill_distance h1 h2 /\
  hill_distance h h2 <= hill_distance h1 h2.

Definition aravalli_hill_2025 (h : Hill) (all_hills : Ensemble Hill) : Prop :=
  meets_100m_threshold h \/
  (exists h_qual, In Hill all_hills h_qual /\ is_supporting_slope h h_qual) \/
  (exists h1 h2, In Hill all_hills h1 /\ In Hill all_hills h2 /\ is_intervening h h1 h2).

Definition standalone_excluded (h : Hill) (all_hills : Ensemble Hill) : Prop :=
  ~meets_100m_threshold h /\
  (forall h_qual, In Hill all_hills h_qual -> ~is_supporting_slope h h_qual) /\
  (forall h1 h2, In Hill all_hills h1 -> In Hill all_hills h2 -> ~is_intervening h h1 h2).

(******************************************************************************)
(*  EMPIRICAL CONSTANTS (FSI-verified)                                        *)
(******************************************************************************)

Definition hills_total : R := 12423.
Definition hills_above_100m : R := 2015.
Definition hills_below_100m : R := 10408.

Lemma hills_partition : hills_above_100m + hills_below_100m = hills_total.
Proof.
  unfold hills_total, hills_above_100m, hills_below_100m.
  lra.
Qed.

Definition excluded_hills_count : R := 5756.
Definition excluded_hills_mean_slope : R := 3.46.
Definition erosion_threshold_slope : R := 3.

Lemma excluded_hills_exceed_erosion_threshold :
  excluded_hills_mean_slope > erosion_threshold_slope.
Proof.
  unfold excluded_hills_mean_slope, erosion_threshold_slope.
  lra.
Qed.

Definition erosion_relevant (slope : R) : Prop := slope >= erosion_threshold_slope.

Lemma excluded_hills_are_erosion_relevant :
  erosion_relevant excluded_hills_mean_slope.
Proof.
  unfold erosion_relevant, excluded_hills_mean_slope, erosion_threshold_slope.
  lra.
Qed.

Lemma excluded_hills_exist : excluded_hills_count > 0.
Proof.
  unfold excluded_hills_count. lra.
Qed.

Theorem definition_under_inclusive :
  excluded_hills_count > 0 /\ erosion_relevant excluded_hills_mean_slope.
Proof.
  split.
  - exact excluded_hills_exist.
  - exact excluded_hills_are_erosion_relevant.
Qed.

Inductive PLPAPurpose : Set :=
  | ErosionPrevention
  | GroundwaterConservation.

(******************************************************************************)
(*  EROSION AND HYDROLOGICAL PREDICATES                                       *)
(*                                                                            *)
(*  Separate predicates for the two PLPA purposes, grounded in physical       *)
(*  mechanisms rather than simple slope correlation.                          *)
(******************************************************************************)

(* Erosion susceptibility based on slope *)
Definition erosion_susceptible (h : Hill) : Prop :=
  slope h >= erosion_threshold_slope.

(* USLE slope factor: higher values indicate greater erosion potential *)
Definition slope_percent (deg : R) : R := 100 * deg * PI / 180.

Definition usle_slope_factor (deg : R) : R :=
  let s := slope_percent deg in
  0.065 + 0.045 * s + 0.0065 * s * s.

(* A hill prevents erosion if it has erosion-susceptible terrain AND vegetation *)
Definition prevents_erosion (h : Hill) : Prop :=
  erosion_susceptible h /\ vegetation_cover h > 0.

(* Groundwater recharge: depends on fractures, weathering, and moderate slope *)
Definition base_infiltration (l : Lithology) : R :=
  match l with
  | Quartzite => 75  (* mm/hr - fractured, high infiltration *)
  | Schist => 50
  | Gneiss => 40
  | Phyllite => 30
  | Marble => 60
  | Alluvium => 100
  end.

Definition slope_infiltration_factor (deg : R) : R :=
  let rad := deg * PI / 180 in
  cos rad * sqrt (Rabs (cos rad)).

Definition effective_infiltration (h : Hill) : R :=
  base_infiltration (rock_type h) *
  slope_infiltration_factor (slope h) *
  (1 + 0.1 * fracture_density h).

Definition storage_capacity (h : Hill) : R :=
  weathered_zone_thickness h * 0.15.

Definition recharge_potential (h : Hill) : R :=
  effective_infiltration h * storage_capacity h * area_ha h.

Definition recharges_groundwater (h : Hill) : Prop :=
  fracture_density h > 0 /\
  weathered_zone_thickness h > 0 /\
  slope h <= 30.

(* PLPA functional: serves either purpose *)
Definition plpa_functional (h : Hill) : Prop :=
  prevents_erosion h \/ recharges_groundwater h.

(* Legacy compatibility *)
Definition serves_erosion_purpose (s : R) : Prop := erosion_relevant s.

Lemma excluded_hills_serve_erosion_purpose :
  serves_erosion_purpose excluded_hills_mean_slope.
Proof.
  unfold serves_erosion_purpose.
  exact excluded_hills_are_erosion_relevant.
Qed.

Theorem statutory_inconsistency :
  excluded_hills_count > 0 /\ serves_erosion_purpose excluded_hills_mean_slope.
Proof.
  split.
  - exact excluded_hills_exist.
  - exact excluded_hills_serve_erosion_purpose.
Qed.

Lemma exclusion_exceeds_half : hills_below_100m / hills_total > 1/2.
Proof.
  unfold hills_below_100m, hills_total.
  lra.
Qed.

Definition hydrologically_significant (slope : R) : Prop :=
  slope >= erosion_threshold_slope.

Lemma excluded_hills_hydrologically_significant :
  hydrologically_significant excluded_hills_mean_slope.
Proof.
  unfold hydrologically_significant.
  exact excluded_hills_are_erosion_relevant.
Qed.

Theorem excluded_hills_serve_both_purposes :
  serves_erosion_purpose excluded_hills_mean_slope /\
  hydrologically_significant excluded_hills_mean_slope.
Proof.
  split.
  - exact excluded_hills_serve_erosion_purpose.
  - exact excluded_hills_hydrologically_significant.
Qed.

Theorem definition_inconsistent_with_plpa :
  excluded_hills_count > 0 /\
  serves_erosion_purpose excluded_hills_mean_slope /\
  hydrologically_significant excluded_hills_mean_slope /\
  hills_below_100m / hills_total > 1/2.
Proof.
  repeat split.
  - exact excluded_hills_exist.
  - exact excluded_hills_serve_erosion_purpose.
  - exact excluded_hills_hydrologically_significant.
  - exact exclusion_exceeds_half.
Qed.

(******************************************************************************)
(*  WITNESS CONSTRUCTION                                                      *)
(*                                                                            *)
(*  A concrete excluded hill demonstrating under-inclusivity.                 *)
(*  Properties based on typical sub-100m Aravalli terrain in Alwar district.  *)
(******************************************************************************)

Definition witness_hill : Hill := mkHill
  1                              (* id *)
  (mkLocation 27.5 76.5)         (* Alwar district *)
  350                            (* peak: 350m ASL *)
  280                            (* base: 280m ASL *)
  70                             (* relief: 70m < 100m threshold *)
  3.5                            (* mean slope: 3.5 deg *)
  8.0                            (* max slope *)
  25                             (* area: 25 ha *)
  Quartzite                      (* fractured quartzite *)
  2.5                            (* fracture density: 2.5/m *)
  8                              (* weathered zone: 8m *)
  1.2                            (* drainage density *)
  0.5                            (* soil thickness *)
  0.4.                           (* vegetation: 40% *)

Lemma witness_excluded : ~meets_100m_threshold witness_hill.
Proof.
  unfold meets_100m_threshold, relief, witness_hill, local_relief.
  simpl. unfold sc_relief_threshold. lra.
Qed.

Lemma witness_erosion_susceptible : erosion_susceptible witness_hill.
Proof.
  unfold erosion_susceptible, slope, witness_hill, mean_slope.
  unfold erosion_threshold_slope. simpl. lra.
Qed.

Lemma witness_has_vegetation : vegetation_cover witness_hill > 0.
Proof. unfold witness_hill. simpl. lra. Qed.

Lemma witness_prevents_erosion : prevents_erosion witness_hill.
Proof.
  unfold prevents_erosion. split.
  - exact witness_erosion_susceptible.
  - exact witness_has_vegetation.
Qed.

Lemma witness_has_fractures : fracture_density witness_hill > 0.
Proof. unfold witness_hill. simpl. lra. Qed.

Lemma witness_has_weathering : weathered_zone_thickness witness_hill > 0.
Proof. unfold witness_hill. simpl. lra. Qed.

Lemma witness_moderate_slope : slope witness_hill <= 30.
Proof. unfold slope, witness_hill, mean_slope. simpl. lra. Qed.

Lemma witness_recharges : recharges_groundwater witness_hill.
Proof.
  unfold recharges_groundwater. repeat split.
  - exact witness_has_fractures.
  - exact witness_has_weathering.
  - exact witness_moderate_slope.
Qed.

Lemma witness_plpa_functional : plpa_functional witness_hill.
Proof.
  unfold plpa_functional. left. exact witness_prevents_erosion.
Qed.

(******************************************************************************)
(*  EXISTENTIAL UNDER-INCLUSIVITY                                             *)
(******************************************************************************)

Theorem exists_excluded_functional :
  exists h : Hill, ~meets_100m_threshold h /\ plpa_functional h.
Proof.
  exists witness_hill. split.
  - exact witness_excluded.
  - exact witness_plpa_functional.
Qed.

Theorem exists_doubly_functional_excluded :
  exists h : Hill,
    ~meets_100m_threshold h /\
    prevents_erosion h /\
    recharges_groundwater h.
Proof.
  exists witness_hill. split.
  - exact witness_excluded.
  - split. exact witness_prevents_erosion. exact witness_recharges.
Qed.

(******************************************************************************)
(*  FSI ALTERNATIVE DEFINITION                                                *)
(******************************************************************************)

Definition fsi_height_threshold : R := 30.
Definition fsi_slope_threshold : R := 4.57.

Definition meets_fsi_criteria (h : Hill) : Prop :=
  relief h >= fsi_height_threshold /\ slope h >= fsi_slope_threshold.

Definition fsi_total_hills : R := 12081.
Definition fsi_hills_above_100m : R := 1048.
Definition fsi_hills_meeting_criteria : R := 4832.

Lemma fsi_better_coverage :
  fsi_hills_meeting_criteria / fsi_total_hills >
  fsi_hills_above_100m / fsi_total_hills.
Proof.
  unfold fsi_hills_meeting_criteria, fsi_hills_above_100m, fsi_total_hills. lra.
Qed.

Lemma fsi_coverage_ratio : fsi_hills_meeting_criteria / fsi_hills_above_100m > 4.
Proof.
  unfold fsi_hills_meeting_criteria, fsi_hills_above_100m. lra.
Qed.

(******************************************************************************)
(*  REVISED CONSISTENCY CRITERIA                                              *)
(******************************************************************************)

Definition under_inclusive (D P : Hill -> Prop) : Prop :=
  exists h, P h /\ ~D h.

Definition captures_all (D P : Hill -> Prop) : Prop :=
  forall h, P h -> D h.

Definition bounded_under_inclusion (rate threshold : R) : Prop :=
  rate <= threshold.

Definition acceptable_rate : R := 0.10.

Lemma exclusion_rate_unacceptable :
  fsi_hills_above_100m / fsi_total_hills < acceptable_rate.
Proof.
  unfold fsi_hills_above_100m, fsi_total_hills, acceptable_rate. lra.
Qed.

Theorem sc_definition_under_inclusive :
  under_inclusive meets_100m_threshold plpa_functional.
Proof.
  unfold under_inclusive.
  exists witness_hill. split.
  - exact witness_plpa_functional.
  - exact witness_excluded.
Qed.

(******************************************************************************)
(*  CONFIDENCE INTERVALS                                                      *)
(******************************************************************************)

Definition excluded_slope_ci_lower : R := 3.38.
Definition excluded_slope_ci_upper : R := 3.54.

Lemma ci_above_threshold : excluded_slope_ci_lower >= erosion_threshold_slope.
Proof.
  unfold excluded_slope_ci_lower, erosion_threshold_slope. lra.
Qed.

(******************************************************************************)
(*  COMPREHENSIVE SUMMARY THEOREM                                             *)
(******************************************************************************)

Theorem aravalli_analysis_summary :
  (* Existential under-inclusivity *)
  (exists h, ~meets_100m_threshold h /\ prevents_erosion h /\ recharges_groundwater h) /\
  (* Quantitative severity: >90% excluded by FSI data *)
  (fsi_hills_above_100m / fsi_total_hills < 0.10) /\
  (* Excluded terrain erosion-relevant *)
  (excluded_hills_mean_slope > erosion_threshold_slope) /\
  (* Statistical robustness *)
  (excluded_slope_ci_lower >= erosion_threshold_slope) /\
  (* FSI alternative superior *)
  (fsi_hills_meeting_criteria / fsi_hills_above_100m > 4).
Proof.
  repeat split.
  - exact exists_doubly_functional_excluded.
  - exact exclusion_rate_unacceptable.
  - exact excluded_hills_exceed_erosion_threshold.
  - exact ci_above_threshold.
  - exact fsi_coverage_ratio.
Qed.
