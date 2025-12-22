(* ============================================================================ *)
(*  ARAVALLI ANALYSIS - Definitive Version                                     *)
(*  Formal verification of SC 2025 INSC 1338 definition consistency            *)
(*                                                                             *)
(*  Methodology: Marker-controlled watershed for local relief computation      *)
(*  Reference: Horn (1981), Weiss (2001), MacMillan et al. (2000)              *)
(*                                                                             *)
(*  Author: Charles C. Norton                                                  *)
(*  Date: December 2025                                                        *)
(* ============================================================================ *)

(* Suppress verbose messages *)
Off[General::stop];
Off[General::spell1];
Off[Import::nffil];

(* ============================================================================ *)
(*  SECTION 1: CONFIGURATION                                                   *)
(* ============================================================================ *)

(* Thresholds from SC Order 2025 INSC 1338 and FSI methodology *)
scReliefThreshold = 100.0;       (* SC definition: 100m above local relief *)
erosionThreshold = 3.0;          (* FSI: 3 degrees for erosion susceptibility *)
prominenceThreshold = 20.0;      (* Minimum prominence for peak detection (m) *)

(* All 24 Aravalli districts *)
allDistricts = {
  (* Rajasthan - 16 districts *)
  <|"name" -> "Udaipur", "latMin" -> 23.8, "latMax" -> 25.3, "lonMin" -> 73.0, "lonMax" -> 74.3|>,
  <|"name" -> "Sirohi", "latMin" -> 24.3, "latMax" -> 25.3, "lonMin" -> 72.1, "lonMax" -> 73.2|>,
  <|"name" -> "Ajmer", "latMin" -> 25.7, "latMax" -> 26.9, "lonMin" -> 73.8, "lonMax" -> 75.4|>,
  <|"name" -> "Jaipur", "latMin" -> 26.3, "latMax" -> 27.6, "lonMin" -> 75.0, "lonMax" -> 76.5|>,
  <|"name" -> "Alwar", "latMin" -> 27.2, "latMax" -> 28.0, "lonMin" -> 76.2, "lonMax" -> 77.0|>,
  <|"name" -> "Bhilwara", "latMin" -> 24.8, "latMax" -> 25.9, "lonMin" -> 74.2, "lonMax" -> 75.5|>,
  <|"name" -> "Chittorgarh", "latMin" -> 23.8, "latMax" -> 25.2, "lonMin" -> 74.3, "lonMax" -> 75.5|>,
  <|"name" -> "Rajsamand", "latMin" -> 24.8, "latMax" -> 25.8, "lonMin" -> 73.4, "lonMax" -> 74.3|>,
  <|"name" -> "Pali", "latMin" -> 24.8, "latMax" -> 26.2, "lonMin" -> 72.5, "lonMax" -> 74.0|>,
  <|"name" -> "Dungarpur", "latMin" -> 23.3, "latMax" -> 24.1, "lonMin" -> 73.3, "lonMax" -> 74.2|>,
  <|"name" -> "Banswara", "latMin" -> 23.1, "latMax" -> 23.8, "lonMin" -> 73.8, "lonMax" -> 74.6|>,
  <|"name" -> "Dausa", "latMin" -> 26.5, "latMax" -> 27.2, "lonMin" -> 76.2, "lonMax" -> 77.0|>,
  <|"name" -> "Sikar", "latMin" -> 27.2, "latMax" -> 28.0, "lonMin" -> 74.7, "lonMax" -> 75.7|>,
  <|"name" -> "Jhunjhunu", "latMin" -> 27.7, "latMax" -> 28.5, "lonMin" -> 75.0, "lonMax" -> 76.0|>,
  <|"name" -> "Nagaur", "latMin" -> 26.5, "latMax" -> 27.8, "lonMin" -> 73.0, "lonMax" -> 74.8|>,
  <|"name" -> "Tonk", "latMin" -> 25.6, "latMax" -> 26.6, "lonMin" -> 75.2, "lonMax" -> 76.3|>,
  (* Haryana - 5 districts *)
  <|"name" -> "Gurugram", "latMin" -> 28.1, "latMax" -> 28.6, "lonMin" -> 76.7, "lonMax" -> 77.2|>,
  <|"name" -> "Faridabad", "latMin" -> 28.2, "latMax" -> 28.6, "lonMin" -> 77.1, "lonMax" -> 77.5|>,
  <|"name" -> "Mahendragarh", "latMin" -> 27.8, "latMax" -> 28.3, "lonMin" -> 75.9, "lonMax" -> 76.5|>,
  <|"name" -> "Rewari", "latMin" -> 28.0, "latMax" -> 28.5, "lonMin" -> 76.3, "lonMax" -> 76.9|>,
  <|"name" -> "Nuh", "latMin" -> 27.8, "latMax" -> 28.2, "lonMin" -> 76.8, "lonMax" -> 77.2|>,
  (* Gujarat - 3 districts *)
  <|"name" -> "Sabarkantha", "latMin" -> 23.2, "latMax" -> 24.4, "lonMin" -> 72.6, "lonMax" -> 73.6|>,
  <|"name" -> "Aravalli", "latMin" -> 23.5, "latMax" -> 24.2, "lonMin" -> 73.0, "lonMax" -> 73.8|>,
  <|"name" -> "Mehsana", "latMin" -> 23.3, "latMax" -> 24.0, "lonMin" -> 72.0, "lonMax" -> 72.9|>
};

(* ============================================================================ *)
(*  SECTION 2: HELPER FUNCTIONS                                                *)
(* ============================================================================ *)

rusleS[slopeDeg_] := Module[{theta},
  theta = slopeDeg * Pi / 180;
  If[100 * Tan[theta] < 9, 10.8 * Sin[theta] + 0.03, 16.8 * Sin[theta] - 0.50]
];

infiltrationRate[slopeDeg_] := 50.0 * Cos[slopeDeg * Pi / 180]^1.5;

wilsonCI[p_, n_, z_: 1.96] := Module[{denom, center, margin},
  denom = 1 + z^2/n;
  center = (p + z^2/(2 n))/denom;
  margin = z * Sqrt[(p (1 - p) + z^2/(4 n))/n]/denom;
  {center - margin, center + margin}
];

(* ============================================================================ *)
(*  SECTION 3: MARKER-CONTROLLED WATERSHED RELIEF                              *)
(* ============================================================================ *)

computeWatershedRelief[dem_, prominenceMin_] := Module[
  {demNorm, demImg, demSmooth, peaks, peaksImg, watershedLabels, basinMinElevations, basinMinMap},
  (* Normalize DEM to 0-1 for image processing *)
  demNorm = Rescale[dem];
  demImg = Image[demNorm, "Real32"];
  demSmooth = GaussianFilter[demNorm, 3];
  (* Peaks with scaled prominence threshold *)
  peaks = MaxDetect[demSmooth, prominenceMin / Max[1, Max[dem] - Min[dem]]];
  peaksImg = Image[peaks, "Bit"];
  (* Watershed on inverted DEM (so basins flow to peaks) *)
  watershedLabels = WatershedComponents[Image[1 - demSmooth, "Real32"], peaksImg];
  (* Get min elevation per basin from original DEM *)
  basinMinElevations = ComponentMeasurements[{watershedLabels, dem}, "Min"];
  basinMinMap = N[watershedLabels /. Dispatch[basinMinElevations]];
  dem - basinMinMap
];

(* ============================================================================ *)
(*  SECTION 4: DISTRICT ANALYSIS FUNCTION                                      *)
(* ============================================================================ *)

analyzeDistrict[dist_] := Module[
  {demRaw, dem, dims, cellSize, latKm, lonKm,
   sobelX, sobelY, dzdx, dzdy, gradMag, slope, relief,
   slopeTrimmed, reliefTrimmed, commonRows, commonCols,
   pairedData, includedPixels, excludedPixels,
   includedSlopes, excludedSlopes, excludedReliefs,
   excludedErosionRelevant,
   hillMask, hillMaskSmooth, hillComponents, componentSizes, validComponents,
   hillStats, hillsAbove100m, hillsBelow100m,
   excludedHillSlopes, witnessHills, witness, witnessLoc},

  (* Fetch DEM quietly *)
  demRaw = Quiet[Check[
    GeoElevationData[
      GeoBounds[{{dist["latMin"], dist["lonMin"]}, {dist["latMax"], dist["lonMax"]}}],
      GeoResolution -> Quantity[1500, "Meters"]
    ],
    $Failed
  ]];

  (* Handle various return formats *)
  dem = Which[
    demRaw === $Failed, Return[<|"name" -> dist["name"], "success" -> False|>],
    Head[demRaw] === QuantityArray, QuantityMagnitude[demRaw],
    ArrayQ[demRaw, 2, NumericQ], demRaw,
    True, Return[<|"name" -> dist["name"], "success" -> False|>]
  ];

  If[!ArrayQ[dem, 2, NumericQ], Return[<|"name" -> dist["name"], "success" -> False|>]];

  dem = Clip[dem, {50, 2500}];
  dims = Dimensions[dem];

  If[Min[dims] < 20, Return[<|"name" -> dist["name"], "success" -> False|>]];
  If[Count[Flatten[dem], _?(# > 50 &)] < 0.5 * Times @@ dims,
    Return[<|"name" -> dist["name"], "success" -> False|>]];

  latKm = (dist["latMax"] - dist["latMin"]) * 111.0;
  lonKm = (dist["lonMax"] - dist["lonMin"]) * 99.0;
  cellSize = N[(latKm * 1000 / dims[[1]] + lonKm * 1000 / dims[[2]]) / 2];

  (* Slope computation *)
  sobelX = {{-1, 0, 1}, {-2, 0, 2}, {-1, 0, 1}} / (8.0 * cellSize);
  sobelY = {{1, 2, 1}, {0, 0, 0}, {-1, -2, -1}} / (8.0 * cellSize);
  dzdx = ListConvolve[sobelX, dem, {2, 2}, 0];
  dzdy = ListConvolve[sobelY, dem, {2, 2}, 0];
  slope = ArcTan[Sqrt[dzdx^2 + dzdy^2]] * 180.0 / Pi;

  (* Local relief via marker-controlled watershed *)
  relief = computeWatershedRelief[dem, prominenceThreshold];

  (* Align arrays *)
  commonRows = Min[Dimensions[slope][[1]], Dimensions[relief][[1]]];
  commonCols = Min[Dimensions[slope][[2]], Dimensions[relief][[2]]];
  slopeTrimmed = slope[[1 ;; commonRows, 1 ;; commonCols]];
  reliefTrimmed = relief[[1 ;; commonRows, 1 ;; commonCols]];

  (* Paired analysis *)
  pairedData = Transpose[{Flatten[reliefTrimmed], Flatten[slopeTrimmed]}];
  includedPixels = Select[pairedData, #[[1]] >= scReliefThreshold &];
  excludedPixels = Select[pairedData, #[[1]] < scReliefThreshold &];

  includedSlopes = If[Length[includedPixels] > 0, includedPixels[[All, 2]], {}];
  excludedSlopes = If[Length[excludedPixels] > 0, excludedPixels[[All, 2]], {}];
  excludedReliefs = If[Length[excludedPixels] > 0, excludedPixels[[All, 1]], {}];
  excludedErosionRelevant = Select[excludedPixels, #[[2]] >= erosionThreshold &];

  (* Hill identification *)
  hillMask = UnitStep[slope - erosionThreshold];
  hillMaskSmooth = Closing[Opening[hillMask, 1], 1];
  hillComponents = MorphologicalComponents[hillMaskSmooth, CornerNeighbors -> True];
  componentSizes = ComponentMeasurements[hillComponents, "Count"];
  validComponents = Select[componentSizes, #[[2]] >= 10 &][[All, 1]];

  hillStats = Table[
    Module[{positions, hSlopes, hReliefs, centroid},
      positions = Position[hillComponents, id];
      If[Length[positions] >= 10,
        hSlopes = Extract[slopeTrimmed, positions];
        hReliefs = Extract[reliefTrimmed, positions];
        centroid = Mean[positions];
        <|"id" -> id, "maxRelief" -> Max[hReliefs], "meanSlope" -> Mean[hSlopes],
          "area" -> Length[positions] * cellSize * cellSize / 10000.0,
          "centroidRow" -> centroid[[1]], "centroidCol" -> centroid[[2]]|>,
        Nothing
      ]
    ],
    {id, validComponents}
  ];

  hillsAbove100m = Select[hillStats, #["maxRelief"] >= scReliefThreshold &];
  hillsBelow100m = Select[hillStats, #["maxRelief"] < scReliefThreshold &];
  excludedHillSlopes = If[Length[hillsBelow100m] > 0, #["meanSlope"] & /@ hillsBelow100m, {}];

  witnessHills = Select[hillsBelow100m, #["meanSlope"] >= erosionThreshold &];
  witness = If[Length[witnessHills] > 0,
    Module[{w = First[SortBy[witnessHills, -#["meanSlope"] &]]},
      witnessLoc = <|
        "lat" -> dist["latMax"] - (w["centroidRow"] / dims[[1]]) * (dist["latMax"] - dist["latMin"]),
        "lon" -> dist["lonMin"] + (w["centroidCol"] / dims[[2]]) * (dist["lonMax"] - dist["lonMin"])
      |>;
      Append[w, "location" -> witnessLoc]
    ],
    <||>
  ];

  <|
    "name" -> dist["name"], "success" -> True, "cellSize" -> cellSize, "demDims" -> dims,
    "totalPixels" -> Length[pairedData],
    "includedPixels" -> Length[includedPixels],
    "excludedPixels" -> Length[excludedPixels],
    "includedMeanSlope" -> If[Length[includedSlopes] > 0, N[Mean[includedSlopes], 4], 0],
    "excludedMeanSlope" -> If[Length[excludedSlopes] > 0, N[Mean[excludedSlopes], 4], 0],
    "excludedMeanRelief" -> If[Length[excludedReliefs] > 0, N[Mean[excludedReliefs], 2], 0],
    "excludedErosionRelevantPixels" -> Length[excludedErosionRelevant],
    "excludedErosionFrac" -> If[Length[excludedPixels] > 0, N[Length[excludedErosionRelevant] / Length[excludedPixels], 4], 0],
    "totalHills" -> Length[hillStats],
    "hillsAbove100m" -> Length[hillsAbove100m],
    "hillsBelow100m" -> Length[hillsBelow100m],
    "excludedHillsMeanSlope" -> If[Length[excludedHillSlopes] > 0, N[Mean[excludedHillSlopes], 4], 0],
    "excludedHillsErosionRelevant" -> Length[witnessHills],
    "excludedHillsErosionFrac" -> If[Length[hillsBelow100m] > 0, N[Length[witnessHills] / Length[hillsBelow100m], 4], 0],
    "excludedMeanUSLE" -> If[Length[excludedSlopes] > 0, N[Mean[rusleS /@ excludedSlopes], 4], 0],
    "includedMeanUSLE" -> If[Length[includedSlopes] > 0, N[Mean[rusleS /@ includedSlopes], 4], 0],
    "excludedMeanInfiltration" -> If[Length[excludedSlopes] > 0, N[Mean[infiltrationRate /@ excludedSlopes], 2], 0],
    "includedMeanInfiltration" -> If[Length[includedSlopes] > 0, N[Mean[infiltrationRate /@ includedSlopes], 2], 0],
    "witness" -> witness
  |>
];

(* ============================================================================ *)
(*  SECTION 5: RUN ANALYSIS                                                    *)
(* ============================================================================ *)

WriteString["stdout", "ARAVALLI ANALYSIS - Marker-controlled watershed\n"];
WriteString["stdout", "Started: " <> DateString[] <> "\n"];
WriteString["stdout", "Processing 24 districts...\n\n"];

startTime = AbsoluteTime[];

(* Process with progress indicator *)
allResults = Table[
  WriteString["stdout", dist["name"] <> "... "];
  result = analyzeDistrict[dist];
  If[result["success"],
    WriteString["stdout", "OK\n"],
    WriteString["stdout", "FAILED\n"]
  ];
  result,
  {dist, allDistricts}
];

endTime = AbsoluteTime[];
runtime = Round[endTime - startTime];

successfulResults = Select[allResults, #["success"] &];
failedResults = Select[allResults, Not[#["success"]] &];

(* ============================================================================ *)
(*  SECTION 6: AGGREGATE AND OUTPUT                                            *)
(* ============================================================================ *)

totalPixels = Total[#["totalPixels"] & /@ successfulResults];
totalIncluded = Total[#["includedPixels"] & /@ successfulResults];
totalExcluded = Total[#["excludedPixels"] & /@ successfulResults];
totalExcludedErosionRelevant = Total[#["excludedErosionRelevantPixels"] & /@ successfulResults];

totalHills = Total[#["totalHills"] & /@ successfulResults];
totalHillsAbove = Total[#["hillsAbove100m"] & /@ successfulResults];
totalHillsBelow = Total[#["hillsBelow100m"] & /@ successfulResults];
totalExcludedHillsErosion = Total[#["excludedHillsErosionRelevant"] & /@ successfulResults];

excludedErosionProp = If[totalExcluded > 0, totalExcludedErosionRelevant / totalExcluded, 0];
ci = If[totalExcluded > 0, wilsonCI[excludedErosionProp, totalExcluded], {0, 0}];

WriteString["stdout", "\n=== RESULTS ===\n"];
WriteString["stdout", "Runtime: " <> ToString[runtime] <> " seconds\n"];
WriteString["stdout", "Successful: " <> ToString[Length[successfulResults]] <> "/24\n\n"];

WriteString["stdout", "PIXEL-LEVEL:\n"];
WriteString["stdout", "  Total: " <> ToString[totalPixels] <> "\n"];
WriteString["stdout", "  Included (>=100m): " <> ToString[totalIncluded] <> " (" <> ToString[N[100*totalIncluded/totalPixels,2]] <> "%)\n"];
WriteString["stdout", "  Excluded (<100m): " <> ToString[totalExcluded] <> " (" <> ToString[N[100*totalExcluded/totalPixels,2]] <> "%)\n"];
WriteString["stdout", "  Excluded erosion-relevant: " <> ToString[totalExcludedErosionRelevant] <> " (" <> ToString[N[100*excludedErosionProp,2]] <> "%)\n"];

WriteString["stdout", "\nHILL-LEVEL:\n"];
WriteString["stdout", "  Total: " <> ToString[totalHills] <> "\n"];
WriteString["stdout", "  >=100m: " <> ToString[totalHillsAbove] <> " (" <> ToString[N[100*totalHillsAbove/totalHills,2]] <> "%)\n"];
WriteString["stdout", "  <100m: " <> ToString[totalHillsBelow] <> " (" <> ToString[N[100*totalHillsBelow/totalHills,2]] <> "%)\n"];
WriteString["stdout", "  Excluded erosion-relevant: " <> ToString[totalExcludedHillsErosion] <> " (" <> ToString[N[100*totalExcludedHillsErosion/totalHillsBelow,2]] <> "%)\n"];

WriteString["stdout", "\n95% CI: [" <> ToString[N[100*ci[[1]],2]] <> "%, " <> ToString[N[100*ci[[2]],2]] <> "%]\n"];

(* ============================================================================ *)
(*  SECTION 7: EXPORT                                                          *)
(* ============================================================================ *)

witnessDistricts = Select[successfulResults, Length[#["witness"]] > 0 &];

exportData = <|
  "metadata" -> <|
    "version" -> "1.0",
    "methodology" -> "marker-controlled watershed",
    "prominenceThreshold" -> prominenceThreshold,
    "timestamp" -> DateString[],
    "mathematica" -> $VersionNumber,
    "runtime" -> runtime,
    "districtsAnalyzed" -> Length[successfulResults],
    "districtsFailed" -> Length[failedResults]
  |>,
  "thresholds" -> <|"scRelief" -> scReliefThreshold, "erosion" -> erosionThreshold, "prominence" -> prominenceThreshold|>,
  "aggregate" -> <|
    "totalPixels" -> totalPixels,
    "includedPixels" -> totalIncluded,
    "excludedPixels" -> totalExcluded,
    "includedPct" -> N[100 * totalIncluded / totalPixels, 4],
    "excludedPct" -> N[100 * totalExcluded / totalPixels, 4],
    "excludedErosionRelevantPixels" -> totalExcludedErosionRelevant,
    "excludedErosionRelevantPct" -> N[100 * totalExcludedErosionRelevant / totalExcluded, 4],
    "totalHills" -> totalHills,
    "hillsAbove100m" -> totalHillsAbove,
    "hillsBelow100m" -> totalHillsBelow,
    "hillsAbove100mPct" -> N[100 * totalHillsAbove / totalHills, 4],
    "hillsBelow100mPct" -> N[100 * totalHillsBelow / totalHills, 4],
    "excludedHillsErosionRelevant" -> totalExcludedHillsErosion,
    "excludedHillsErosionRelevantPct" -> N[100 * totalExcludedHillsErosion / totalHillsBelow, 4],
    "excludedErosionCI95Lower" -> N[ci[[1]], 6],
    "excludedErosionCI95Upper" -> N[ci[[2]], 6]
  |>,
  "perDistrict" -> successfulResults,
  "witnesses" -> (#["witness"] & /@ witnessDistricts)
|>;

Export["aravalli_results.json", exportData, "JSON"];
WriteString["stdout", "\nExported: aravalli_results.json\n"];

(* Coq constants *)
coqOutput = StringJoin[
  "(* ARAVALLI EMPIRICAL CONSTANTS - Generated " <> DateString[] <> " *)\n",
  "(* Methodology: marker-controlled watershed, prominence >= " <> ToString[prominenceThreshold] <> "m *)\n",
  "(* Districts: " <> ToString[Length[successfulResults]] <> "/24 *)\n\n",
  "Require Import Coq.Reals.Reals.\nRequire Import Coq.micromega.Lra.\nOpen Scope R_scope.\n\n",
  "Definition sc_relief_threshold : R := " <> ToString[scReliefThreshold] <> ".\n",
  "Definition erosion_threshold : R := " <> ToString[erosionThreshold] <> ".\n",
  "Definition total_pixels : R := " <> ToString[totalPixels] <> ".\n",
  "Definition included_pixels : R := " <> ToString[totalIncluded] <> ".\n",
  "Definition excluded_pixels : R := " <> ToString[totalExcluded] <> ".\n",
  "Definition excluded_erosion_relevant_pixels : R := " <> ToString[totalExcludedErosionRelevant] <> ".\n",
  "Definition total_hills : R := " <> ToString[totalHills] <> ".\n",
  "Definition hills_above_100m : R := " <> ToString[totalHillsAbove] <> ".\n",
  "Definition hills_below_100m : R := " <> ToString[totalHillsBelow] <> ".\n",
  "Definition excluded_hills_erosion_relevant : R := " <> ToString[totalExcludedHillsErosion] <> ".\n",
  "Definition exclusion_ratio : R := " <> ToString[N[totalExcluded/totalPixels, 8]] <> ".\n",
  "Definition hills_exclusion_ratio : R := " <> ToString[N[totalHillsBelow/totalHills, 8]] <> ".\n",
  "Definition excluded_erosion_frac : R := " <> ToString[N[excludedErosionProp, 8]] <> ".\n",
  "Definition excluded_erosion_ci_lower : R := " <> ToString[N[ci[[1]], 8]] <> ".\n",
  "Definition excluded_erosion_ci_upper : R := " <> ToString[N[ci[[2]], 8]] <> ".\n\n",
  "Lemma pixel_partition : included_pixels + excluded_pixels = total_pixels.\n",
  "Proof. unfold included_pixels, excluded_pixels, total_pixels. lra. Qed.\n\n",
  "Lemma hill_partition : hills_above_100m + hills_below_100m = total_hills.\n",
  "Proof. unfold hills_above_100m, hills_below_100m, total_hills. lra. Qed.\n"
];

Export["aravalli_empirical.v", coqOutput, "Text"];
WriteString["stdout", "Exported: aravalli_empirical.v\n"];
WriteString["stdout", "\n=== COMPLETE ===\n"];
