# The literature interface of the released proof

Read 2026-11-20 from `Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean` in Alpöge's archive (source text only; the build had not finished).

The file holds 186 theorems that take the three-field hypothesis `O : OpenLiteratureStatements` (Galois representations of polarized pairs, local-global compatibility, existence of a local Langlands correspondence). Nearly all return one named statement; a few bundle rows into a structure, and the last is the file's conclusion, `EveryCharacter`. `O` is itself supplied with proofs at the top of the tree, so none of these is an assumption of the final theorem.

- 155 of the statements are in the namespace `GlobalTheory.Published`.
- 151 are proved here from theorems elsewhere in the tree, using neither `O` nor another row.
- 4 read a field of `O` directly; 34 are assembled from other rows.

A name is a label, not a statement. Six definitions were read against their names on 2026-11-20 and each states the general theorem its name suggests: `ResolutionCharZero` (a sequence of blow-ups making any reduced separated scheme of finite type over a field of characteristic zero smooth, an isomorphism over the smooth locus, with simple normal crossings), `KawamataViehweg`, `ClozelPurity`, `SiegelKlingen`, `DeligneRibet`, `BhattScholzeIntegral`. The other rows are unaudited.

| Row | Statement | Built from other rows | Reads `O` |
|---|---|---:|---|
| `logDerivOne` | `GlobalTheory.Mem.An.LogDerOne` |  |  |
| `ellipticMainTheoremCM'` | `GlobalTheory.Published.EllipticMainTheoremCM` |  |  |
| `heckeTateFunctionalEquation'` | `GlobalTheory.Published.HeckeTateFunctionalEquation` |  |  |
| `hilbertClassFieldJ'` | `GlobalTheory.Published.HilbertClassFieldJ` |  |  |
| `partial_zeta_functional_equation_of_literature` | `GlobalTheory.Published.PartialZetaFunctionalEquation` |  |  |
| `deligne_ribet_of_literature` | `GlobalTheory.Published.DeligneRibet` |  |  |
| `siegel_klingen_deligne_ribet_of_literature` | `GlobalTheory.Published.SiegelKlingenDeligneRibet` | 1 |  |
| `join_out_of_literature` | `GlobalTheory.Mem.LiteralAutomorphy.JoinOut` | 2 |  |
| `ht_card_of_literature` | `GlobalTheory.HeightCounting.HtCard` |  |  |
| `ab_mul_n_st_of_literature` | `GlobalTheory.Published.AbMulNSt` |  |  |
| `abelian_de_rham_of_literature` | `GlobalTheory.Published.AbelianDeRham` |  |  |
| `de_rham_pot_semistable_of_literature` | `GlobalTheory.Published.DeRhamPotSemistable` |  |  |
| `global_artin_reciprocity_of_literature` | `GlobalTheory.Published.GlobalArtinReciprocity` |  |  |
| `hecke_l_adic_character_de_rham_of_literature` | `GlobalTheory.Published.HeckeLAdicCharacterDeRham` |  |  |
| `algebraic_character_wd_of_literature` | `GlobalTheory.Published.AlgebraicCharacterWD` | 3 |  |
| `ar_calc_of_literature` | `GlobalTheory.Published.ArCalc` |  |  |
| `ar_degree_of_literature` | `GlobalTheory.Published.ArDegree` |  |  |
| `principalisation_of_literature` | `GlobalTheory.Published.Principalisation` |  |  |
| `arith_hilbert_samuel_of_literature` | `GlobalTheory.Published.ArithHilbertSamuel` | 1 |  |
| `automorphic_forms_finite_gl_of_literature` | `GlobalTheory.Published.AutomorphicFormsFiniteGL` |  |  |
| `base_change_isobaric` | `GlobalTheory.Published.BaseChangeIsobaricTransfer` |  |  |
| `base_change_definite_unitary_group_of_literature` | `GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup` | 1 |  |
| `bernstein_unitary_product_irreducible_of_literature` | `GlobalTheory.Published.BernsteinUnitaryProductIrreducible` |  |  |
| `bernstein_zelevinsky_finiteness_of_literature` | `GlobalTheory.Published.BernsteinZelevinskyFiniteness` |  |  |
| `bhatt_scholze_integral_of_literature` | `GlobalTheory.Published.BhattScholzeIntegral` |  |  |
| `bhatt_scholze_crystalline_lattices_of_literature` | `GlobalTheory.Published.BhattScholzeCrystallineLattices` | 1 |  |
| `bloch_kato_local_of_literature` | `GlobalTheory.Published.BlochKatoLocal` |  |  |
| `borel_casselman_of_literature` | `GlobalTheory.Published.BorelCasselman` |  |  |
| `brauer_degree_zero_of_literature` | `GlobalTheory.Published.BrauerDegreeZero` |  |  |
| `cm_curve_good_outside_prime_st_of_literature` | `GlobalTheory.Published.CMCurveGoodOutsidePrimeSt` |  |  |
| `ess_square_integrable_segments_of_literature` | `GlobalTheory.Published.EssSquareIntegrableSegments` |  |  |
| `local_converse_gl_of_literature` | `GlobalTheory.Published.LocalConverseGL` |  |  |
| `local_langlands_recT_exists_of_literature` | `UpperTheory.Zero.LLC.RecTExists` |  | yes |
| `pair_u_of_literature` | `UpperTheory.GalS.PairUAlt` | 2 | yes |
| `cusp_forms_bounded_gl_of_literature` | `GlobalTheory.Published.CuspFormsBoundedGL` |  |  |
| `jacquet_shalika_rigidity_of_literature` | `GlobalTheory.Published.JacquetShalikaRigidity` |  |  |
| `gelfand_kazhdan_dual_of_literature` | `GlobalTheory.Published.GelfandKazhdanDual` | 2 |  |
| `generic_unlinked_gl_of_literature` | `GlobalTheory.Published.GenericUnlinkedGL` |  |  |
| `chevalley_units_of_literature` | `GlobalTheory.Published.ChevalleyUnits` |  |  |
| `geometric_restriction_of_literature` | `GlobalTheory.Published.GeometricLemma` |  |  |
| `grothendieck_ring_polynomial_of_literature` | `GlobalTheory.Published.GrothendieckRingPolynomial` |  |  |
| `segment_representation_of_literature` | `GlobalTheory.Published.SegmentRepresentation` |  |  |
| `zelevinsky_polynomial_ring_of_literature` | `GlobalTheory.Published.ZelevinskyPolynomialRing` | 2 |  |
| `depth_zero_induction_of_literature` | `GlobalTheory.Published.DepthZeroInduction` | 3 |  |
| `langlands_exhaustion_gl_of_literature` | `GlobalTheory.Published.LanglandsExhaustionGL` |  |  |
| `langlands_multisegments_of_literature` | `GlobalTheory.Published.LanglandsMultisegments` |  |  |
| `standard_cosocle_gl_of_literature` | `GlobalTheory.Published.StandardCosocleGL` |  |  |
| `local_langlands_gl_recT_exists_of_literature` | `UpperTheory.Zero.LLC.RecTExists` | 12 |  |
| `irreducible_admissible_gl_of_literature` | `GlobalTheory.Published.IrreducibleAdmissibleGL` |  |  |
| `standard_functors_finite_length_of_literature` | `GlobalTheory.Published.StandardFunctorsFiniteLength` |  |  |
| `tempered_product_of_square_integrable_of_literature` | `GlobalTheory.Published.TemperedProductOfSquareIntegrable` | 8 |  |
| `casselman_wallach_of_literature` | `GlobalTheory.Published.CasselmanWallach` |  |  |
| `chebotarev_degree_one_of_literature` | `GlobalTheory.Published.ChebotarevDegreeOne` |  |  |
| `chow_form_exists_of_literature` | `GlobalTheory.Published.ChowFormExists` |  |  |
| `clozel_cohomological_of_literature` | `GlobalTheory.Published.ClozelCohomological` |  |  |
| `clozel_purity_of_literature` | `GlobalTheory.Published.ClozelPurity` |  |  |
| `complex_multiplication_j_st_of_literature` | `GlobalTheory.Published.ComplexMultiplicationJSt` |  |  |
| `cusp_bounded_of_literature` | `GlobalTheory.Published.CuspBounded` |  |  |
| `cusp_decay_bound_of_literature` | `GlobalTheory.Published.CuspDecayBound` |  |  |
| `cusp_decay_sobolev_of_literature` | `GlobalTheory.Published.CuspDecaySobolev` |  |  |
| `cusp_rapid_decay_of_literature` | `GlobalTheory.Published.CuspRapidDecay` |  |  |
| `cusp_trace_class_of_literature` | `GlobalTheory.Published.CuspTraceClass` |  |  |
| `cuspidal_mirabolic_of_literature` | `GlobalTheory.Published.CuspidalMirabolic` |  |  |
| `cuspidal_spectrum_gl_of_literature` | `GlobalTheory.Published.CuspidalSpectrumGL` |  |  |
| `cycle_heights_of_literature` | `GlobalTheory.Published.CycleHeights` |  |  |
| `depth_zero_jacquet_injective_of_literature` | `GlobalTheory.Published.DepthZeroJacquetInjective` |  |  |
| `depth_zero_support_of_literature` | `GlobalTheory.Published.DepthZeroSupport` |  |  |
| `discrete_series_classification_of_literature` | `GlobalTheory.Published.DiscreteSeriesClassification` |  |  |
| `discrete_series_cover_of_literature` | `GlobalTheory.Published.DiscreteSeriesCover` |  |  |
| `discrete_series_cover_exists_of_literature` | `GlobalTheory.Published.DiscreteSeriesCoverExists` |  |  |
| `discrete_series_exists_of_literature` | `GlobalTheory.Published.DiscreteSeriesExists` |  |  |
| `discrete_series_hermitian_unique_of_literature` | `GlobalTheory.Published.DiscreteSeriesHermitianUnique` |  |  |
| `discrete_series_lowest_k_type_of_literature` | `GlobalTheory.Published.DiscreteSeriesLowestKType` |  |  |
| `discrete_series_upq_exists_of_literature` | `GlobalTheory.Published.DiscreteSeriesUpqExists` |  |  |
| `dixmier_malliavin_factorisation_of_literature` | `GlobalTheory.Published.DixmierMalliavinFactorisation` |  |  |
| `siegel_eisenstein_continuation_of_literature` | `GlobalTheory.Published.SiegelEisensteinContinuation` |  |  |
| `doubling_method` | `GlobalTheory.Published.DoublingMethodLocalZetaIntegrals` | 2 |  |
| `flath_tensor_product_of_literature` | `GlobalTheory.Published.FlathTensorProduct` |  |  |
| `unitary_irreducible_admissible_of_literature` | `GlobalTheory.Published.UnitaryIrreducibleAdmissible` |  |  |
| `flath_factorisation_of_literature` | `GlobalTheory.Published.FlathFactorisation` | 2 |  |
| `fontaine_bcris_of_literature` | `GlobalTheory.Published.FontaineBcris` |  |  |
| `formal_algebraisation_of_literature` | `GlobalTheory.Published.FormalAlgebraisation` |  |  |
| `formal_degree_compact_dual_of_literature` | `GlobalTheory.Published.FormalDegreeCompactDual` |  |  |
| `gk_globalisation_of_literature` | `GlobalTheory.Published.GKGlobalisation` |  |  |
| `gl_howe_duality_of_literature` | `GlobalTheory.Published.GLHoweDuality` |  |  |
| `cusp_u_of_literature` | `UpperTheory.GalS.CuspUAlt` | 2 |  |
| `generic_unitary_dual_gl_of_literature` | `GlobalTheory.Published.GenericUnitaryDualGL` |  |  |
| `geometric_restriction_filtration_of_literature` | `GlobalTheory.Published.GeometricLemmaFiltration` |  |  |
| `good_chern_weil_of_literature` | `GlobalTheory.Published.GoodChernWeil` |  |  |
| `green_cuspidal_of_literature` | `GlobalTheory.Published.GreenCuspidal` |  |  |
| `green_regular_characters_of_literature` | `GlobalTheory.Published.GreenRegularCharacters` |  |  |
| `green_series_st_of_literature` | `GlobalTheory.Published.GreenSeriesSt` |  |  |
| `abelian_lifting_of_literature` | `GlobalTheory.Published.AbelianLifting` |  |  |
| `grothendieck_deformation_of_literature` | `GlobalTheory.Published.GrothendieckDeformation` | 2 |  |
| `grothendieck_messing_of_literature` | `GlobalTheory.Published.GrothendieckMessing` | 1 |  |
| `principal_polarisation_one_section_of_literature` | `GlobalTheory.Published.principalPolarisationOneSection` |  |  |
| `harish_chandra_analyticity_of_literature` | `GlobalTheory.Published.HarishChandraAnalyticity` |  |  |
| `harish_chandra_finite_of_literature` | `GlobalTheory.Published.HarishChandraFinite` |  |  |
| `harish_chandra_modules_of_literature` | `GlobalTheory.Published.HarishChandraModules` |  |  |
| `hasse_norm_st_of_literature` | `GlobalTheory.Published.HasseNormSt` |  |  |
| `hecke_l_adic_character_of_literature` | `GlobalTheory.Published.HeckeLAdicCharacter` |  |  |
| `hecke_l_adic_character_crystalline_of_literature` | `GlobalTheory.Published.HeckeLAdicCharacterCrystalline` | 4 |  |
| `hecke_l_adic_character_above_of_literature` | `GlobalTheory.Published.HeckeLAdicCharacterAbove` | 3 |  |
| `hecke_l_adic_parameter_above_of_literature` | `GlobalTheory.Published.HeckeLAdicParameterAboveAlt` | 1 |  |
| `hecke_l_entire_and_nonzero_at_one_of_literature` | `GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne` |  |  |
| `hecke_l_partial_continuation_of_literature` | `GlobalTheory.Published.HeckeLPartialContinuation` |  |  |
| `hermitian_hasse_principle_of_literature` | `GlobalTheory.Published.HermitianHassePrinciple` |  |  |
| `hermitian_local_global_of_literature` | `GlobalTheory.Published.HermitianLocalGlobal` |  |  |
| `holomorphic_discrete_series_of_literature` | `GlobalTheory.Published.HolomorphicDiscreteSeries` |  |  |
| `howe_duality_real_of_literature` | `GlobalTheory.Published.HoweDualityReal` |  |  |
| `ideal_invariants_one_orbit_st_of_literature` | `GlobalTheory.Published.IdealInvariantsOneOrbitSt` |  |  |
| `induced_simple_lowest_alcove_of_literature` | `GlobalTheory.Published.InducedSimpleLowestAlcove` |  |  |
| `jacquet_shalika_of_literature` | `GlobalTheory.Published.JacquetShalika` |  |  |
| `k_finite_vectors_unitary_of_literature` | `GlobalTheory.Published.KFiniteVectorsUnitary` |  |  |
| `kawamata_viehweg_of_literature` | `GlobalTheory.Published.KawamataViehweg` |  |  |
| `kudla_splitting_split_unitary_of_literature` | `GlobalTheory.Published.KudlaSplittingSplitUnitary` |  |  |
| `l2_extension_log_canonical_of_literature` | `GlobalTheory.Published.L2ExtensionLogCanonical` |  |  |
| `landherr_st_of_literature` | `GlobalTheory.Published.LandherrSt` |  |  |
| `linnik_of_literature` | `GlobalTheory.Published.Linnik` |  |  |
| `cuspidal_multiplicity_one_of_literature` | `GlobalTheory.Published.CuspidalMultiplicityOne` |  |  |
| `carU_local_global_of_literature` | `UpperTheory.GalS.CarUAlt` | 2 | yes |
| `carU_above_l_of_literature` | `UpperTheory.GalS.CarUAlt` | 3 |  |
| `metaplectic_representation_of_literature` | `GlobalTheory.Published.MetaplecticRepresentation` |  |  |
| `moy_prasad_jacquet_iso_of_literature` | `GlobalTheory.Published.MoyPrasadJacquetIso` |  |  |
| `nadel_vanishing_and_non_klt_divisor_of_literature` | `GlobalTheory.Published.NadelVanishingAndNonKltDivisor` |  |  |
| `nef_numerics_of_literature` | `GlobalTheory.Published.NefNumerics` |  |  |
| `point_separation_pair_of_literature` | `GlobalTheory.Published.PointSeparationPair` |  |  |
| `poitou_tate_normalised_of_literature` | `GlobalTheory.Published.PoitouTateNormalised` |  |  |
| `prismatic_dieudonne_hodge_of_literature` | `GlobalTheory.Published.PrismaticDieudonneHodge` |  |  |
| `quadratic_class_field_theory_of_literature` | `GlobalTheory.Published.QuadraticClassFieldTheory` |  |  |
| `radford_shuffle_polynomial_of_literature` | `GlobalTheory.Published.RadfordShufflePolynomial` |  |  |
| `siegel_weil_unitary_convergent_of_literature` | `GlobalTheory.Published.SiegelWeilUnitaryConvergent` |  |  |
| `weil_theta_convergence_of_literature` | `GlobalTheory.Published.WeilThetaConvergence` |  |  |
| `rallis_inner_product_convergent_of_literature` | `GlobalTheory.Published.RallisInnerProductConvergent` | 3 |  |
| `ray_character_artin_of_literature` | `GlobalTheory.Published.RayCharacterArtin` | 1 |  |
| `ray_class_field_st_of_literature` | `GlobalTheory.Published.RayClassFieldSt` |  |  |
| `real_metaplectic_representation_of_literature` | `GlobalTheory.Published.RealMetaplecticRepresentation` |  |  |
| `regular_algebraic_purity_of_literature` | `GlobalTheory.Published.RegularAlgebraicPurity` | 2 |  |
| `schur_orthogonality_square_integrable_of_literature` | `GlobalTheory.Published.SchurOrthogonalitySquareIntegrable` |  |  |
| `semi_abelian_hom_extension_of_literature` | `GlobalTheory.Published.SemiAbelianHomExtension` |  |  |
| `semi_abelian_lie_seminegative_of_literature` | `GlobalTheory.Published.SemiAbelianLieSeminegative` |  |  |
| `semistable_reduction_st_of_literature` | `GlobalTheory.Published.SemistableReductionSt` |  |  |
| `serre_holomorphic_sections_of_literature` | `GlobalTheory.Published.SerreHolomorphicSections` |  |  |
| `siegel_eisenstein_simple_pole` | `GlobalTheory.Published.UnusedSlot72` |  |  |
| `siegel_set_unitary_of_literature` | `GlobalTheory.Published.SiegelSetUnitary` |  |  |
| `siegel_toroidal_integral_of_literature` | `GlobalTheory.Published.SiegelToroidalIntegral` |  |  |
| `siegel_weil_unitary_schrodinger_of_literature` | `GlobalTheory.Published.SiegelWeilUnitarySchrodinger` |  |  |
| `square_integrable_segment_of_literature` | `GlobalTheory.Published.SquareIntegrableSegment` | 1 |  |
| `stone_von_neumann_of_literature` | `GlobalTheory.Published.StoneVonNeumann` |  |  |
| `strong_approx_su_of_literature` | `GlobalTheory.Published.StrongApproxSU` |  |  |
| `theta_rational_invariance_of_literature` | `GlobalTheory.Published.ThetaRationalInvariance` |  |  |
| `toroidal_compactification_of_literature` | `GlobalTheory.Published.ToroidalCompactification` |  |  |
| `toroidal_for_fan_ks_of_literature` | `GlobalTheory.Published.ToroidalForFanKS` |  |  |
| `totally_disjoint_product_irreducible_of_literature` | `GlobalTheory.Published.TotallyDisjointProductIrreducible` |  |  |
| `unlinked_product_irreducible_of_literature` | `GlobalTheory.Published.UnlinkedProductIrreducible` | 1 |  |
| `unramified_doubling_gl_of_literature` | `GlobalTheory.Published.UnramifiedDoublingGL` |  |  |
| `vol_ge_of_literature` | `GlobalTheory.Published.VolGe` | 3 |  |
| `vol_nef_of_literature` | `GlobalTheory.Published.VolNef` | 1 |  |
| `weber_ray_field_st_of_literature` | `GlobalTheory.Published.WeberRayFieldSt` |  |  |
| `weil_representation_exists_of_literature` | `GlobalTheory.Published.WeilRepresentationExists` |  |  |
| `weil_representation_unitary_pair_of_literature` | `GlobalTheory.Published.WeilRepresentationUnitaryPair` |  |  |
| `weil_siegel_formula_unitary_of_literature` | `GlobalTheory.Published.WeilSiegelFormulaUnitary` |  |  |
| `weyl_branching_of_literature` | `GlobalTheory.Published.WeylBranching` |  |  |
| `dual_abelian_scheme_of_literature` | `GlobalTheory.Published.DualAbelianScheme` |  |  |
| `zarhin_statement` | `GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement` | 1 |  |
| `fargues_exact_of_literature` | `GlobalTheory.CompanionTheory.Ar.HT.FarguesExact` |  |  |
| `nef_rr_of_literature` | `GlobalTheory.CompanionTheory.Ar.Pub.NefRR` |  |  |
| `poincare_lelong_inv_of_literature` | `GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv` |  |  |
| `principalisation_char_zero_of_literature` | `GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero` |  |  |
| `resolution_char_zero_of_literature` | `GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero` |  |  |
| `cheb_of_literature` | `GlobalTheory.TwSys.Cheb` |  |  |
| `eis_bl_of_literature` | `GlobalTheory.ThK.Dbl.EisBL` |  |  |
| `siegel_weil_std_of_literature` | `GlobalTheory.ThK.Dbl.SiegelWeilStd` |  |  |
| `theta_integrals_agree_and_local_matching_of_literature` | `GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching` | 2 |  |
| `global_euler_char_of_literature` | `ReciprocityTheory.Gal.GlobalEulerChar` |  |  |
| `global_finiteness_of_literature` | `ReciprocityTheory.Gal.GlobalFiniteness` |  |  |
| `localEulerChar_alt_alt` | `ReciprocityTheory.Gal.LocalEulerChar` |  |  |
| `local_finiteness_of_literature` | `ReciprocityTheory.Gal.LocalFiniteness` |  |  |
| `local_tate_duality_of_literature` | `ReciprocityTheory.Gal.LocalTateDuality` |  |  |
| `greenberg_wiles_of_literature` | `ReciprocityTheory.Gal.GreenbergWiles` | 5 |  |
| `unramified_orthogonality_of_literature` | `ReciprocityTheory.Gal.UnramifiedOrthogonality` |  |  |
| `siegelWeilU_unitary_convergent_of_literature` | `HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent` |  |  |
| `local_euler_char_k_of_literature` | `Formalism.GaloisCohomology.LocalEulerCharK` |  |  |
| `local_finiteness_k_of_literature` | `Formalism.GaloisCohomology.LocalFinitenessK` |  |  |
| `local_tate_duality_k_of_literature` | `Formalism.GaloisCohomology.LocalTateDualityK` | 154 | yes |
| `every_character_of_literature_of_vWin` | `UpperTheory.EveryCharacter` | 17 |  |
