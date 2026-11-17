module

-- Opt-in endpoint audit. Do not import this module in the library or CI.
import SubtreeProofs

#print axioms SubtreeProofs.Complexity.Memo.Body.erase_run
#print axioms SubtreeProofs.Complexity.Memo.Body.run_spec
#print axioms SubtreeProofs.Complexity.Memo.Problem.requestHeight_decreases
#print axioms SubtreeProofs.Complexity.Memo.eval_correct
#print axioms SubtreeProofs.Complexity.Memo.eval_wp
#print axioms SubtreeProofs.Complexity.Memo.evalRoots_trace_spec
#print axioms SubtreeProofs.Complexity.Memo.TraceInvariant.domain_eq
#print axioms SubtreeProofs.Complexity.Memo.evalRoots_balance
#print axioms SubtreeProofs.Complexity.Memo.roots_request_identity
#print axioms SubtreeProofs.Complexity.Memo.roots_expansion_bound
#print axioms SubtreeProofs.Complexity.Memo.roots_envelope
#print axioms SubtreeProofs.Complexity.Memo.Event.totalWork_eq
#print axioms SubtreeProofs.Complexity.Memo.Event.totalWork_le
#print axioms SubtreeProofs.Complexity.Memo.ListCache.ops
#print axioms SubtreeProofs.Complexity.Memo.DirectCache.ops
#print axioms SubtreeProofs.Complexity.Paper2004.problem
#print axioms SubtreeProofs.Complexity.Paper2004.eval_refines_memoLcs
#print axioms SubtreeProofs.Complexity.Paper2004.roots_envelope_spec
#print axioms SubtreeProofs.Complexity.Paper2004.memoLcs_calls_from_generic
#print axioms SubtreeProofs.Complexity.Paper2004.memoLcs_warm_misses_from_generic
#print axioms SubtreeProofs.Complexity.EditDistance.distance_optimum
#print axioms SubtreeProofs.Complexity.EditDistance.body_correct
#print axioms SubtreeProofs.Complexity.EditDistance.requests_decrease
#print axioms SubtreeProofs.Complexity.EditDistance.roots_spec
#print axioms SubtreeProofs.Complexity.EditDistance.initial_value_optimum
#print axioms SubtreeProofs.Complexity.EditDistance.list_roots_spec
#print axioms SubtreeProofs.Complexity.EditDistance.dense_roots_spec
#print axioms SubtreeProofs.Complexity.EditDistance.dense_setup
#print axioms SubtreeProofs.Complexity.Memo.DirectCache.productOps
#print axioms SubtreeProofs.Complexity.Memo.DirectCache.product_initial_sound
#print axioms SubtreeProofs.Complexity.Memo.WorkInvariant.lookup
#print axioms SubtreeProofs.Complexity.Memo.WorkInvariant.complete
#print axioms SubtreeProofs.Complexity.Memo.roots_work_spec
#print axioms SubtreeProofs.Complexity.Memo.Event.localWork_eq
#print axioms SubtreeProofs.Complexity.Memo.roots_weighted_work_envelope
#print axioms SubtreeProofs.Complexity.Memo.roots_weighted_work_wp
#print axioms SubtreeProofs.Complexity.Memo.roots_work_envelope
#print axioms SubtreeProofs.Complexity.Memo.ListCache.workModel
#print axioms SubtreeProofs.Complexity.Memo.DirectCache.workModel
#print axioms SubtreeProofs.Complexity.Memo.DirectCache.productWorkModel
#print axioms SubtreeProofs.Complexity.EditDistance.interior_card
#print axioms SubtreeProofs.Complexity.EditDistance.list_weighted_work_spec
#print axioms SubtreeProofs.Complexity.EditDistance.dense_weighted_work_spec
#print axioms SubtreeProofs.Complexity.Paper2004.roots_list_work
#print axioms SubtreeProofs.Complexity.Paper2004.cold_list_work

#print axioms SubtreeProofs.Paper2004.OrderedTree.decodeDyck_encodeDyck
#print axioms SubtreeProofs.Paper2004.OrderedTree.encodeDyck_decodeDyck
#print axioms SubtreeProofs.Paper2004.OrderedTree.embeds_iff_dyckEmbeds
#print axioms SubtreeProofs.Paper2004.OrderedTree.printed_containment_not_complete
#print axioms SubtreeProofs.Paper2004.OrderedTree.mem_contractions_iff
#print axioms SubtreeProofs.Paper2004.OrderedTree.maximumCommonContraction_correct
#print axioms SubtreeProofs.Rust.contractionBudget_refines_tree
#print axioms SubtreeProofs.WeightedMatching.solveMatrix_correct
#print axioms SubtreeProofs.Paper2004.OrderedTree.longestCommonBalanced_decodes_maximum
#print axioms SubtreeProofs.Paper2004.OrderedTree.decomposition_card_bound
#print axioms SubtreeProofs.Paper2004.OrderedTree.paperCommon_tree_correct
#print axioms SubtreeProofs.Rust.OrderedSolver.largest_common_embedding_of_trees
#print axioms SubtreeProofs.Droschinsky2016.exists_maximum
#print axioms SubtreeProofs.Droschinsky2016.Valid.inducedIso
#print axioms SubtreeProofs.Droschinsky2018.exists_maximum
#print axioms SubtreeProofs.Droschinsky2018.maximum_score_antitone
#print axioms SubtreeProofs.Rust.MemoizedOrderedSolver.maximum_common_embedding_of_trees
#print axioms SubtreeProofs.Rust.MemoizedOrderedSolver.memoized_common_embedding_cache_bound

#print axioms SubtreeProofs.WeightedMatching.AssignmentReduction.minimum_assignment_decodes
#print axioms SubtreeProofs.Droschinsky2016.fixedRootValue_eq_unrootedValue
#print axioms SubtreeProofs.Droschinsky2016.rooted_matching_recurrence
#print axioms SubtreeProofs.Droschinsky2018.Valid.rooted_realizations
#print axioms SubtreeProofs.Droschinsky2018.pairedImage_valid
#print axioms SubtreeProofs.Droschinsky2018.score_pairedImage
#print axioms SubtreeProofs.Droschinsky2018.valid_iff_source_embeddings
#print axioms SubtreeProofs.Droschinsky2018.rootedValid_iff_source_embeddings
#print axioms SubtreeProofs.Droschinsky2018.rootToRootValid_iff_source_embeddings
#print axioms SubtreeProofs.Droschinsky2018.skipped_recurrence_two_state
#print axioms SubtreeProofs.Droschinsky2018.mapped_recurrence

#print axioms SubtreeProofs.Rust.AssignmentEntrypoint.min_cost_assignment_total_spec
#print axioms SubtreeProofs.Rust.AssignmentEntrypoint.min_cost_assignment_spec

#print axioms SubtreeProofs.Rust.MatchingEntrypoint.max_weight_partial_matching_total_spec
#print axioms SubtreeProofs.Rust.MatchingEntrypoint.max_weight_partial_matching_spec

#print axioms SubtreeProofs.Paper2004.OrderedTree.OrderedIsoDP.level_correct
#print axioms SubtreeProofs.Paper2004.OrderedTree.OrderedIsoDP.anywhere_correct
#print axioms SubtreeProofs.Paper2004.OrderedTree.OrderedIsoDP.anywhereSize_optimum

#print axioms SubtreeProofs.Rust.OrderedIsomorphism.rooted_common_isomorphism_of_trees
#print axioms SubtreeProofs.Rust.OrderedIsomorphism.largest_common_isomorphism_of_trees

#print axioms SubtreeProofs.Rust.MatchingDeletionEntrypoint.max_weight_matching_deletions_total_spec
#print axioms SubtreeProofs.Rust.MatchingDeletionEntrypoint.max_weight_matching_deletions_spec

#print axioms SubtreeProofs.WeightedMatching.CopiedAssignmentReduction.feasible_tight_decodes
#print axioms SubtreeProofs.WeightedMatching.CopiedAssignmentReduction.normalize_tight

#print axioms SubtreeProofs.Rust.IndexedOrderedSolver.maximum_common_embedding_indexed_of_trees
#print axioms SubtreeProofs.Rust.IndexedOrderedSolver.maximum_common_embedding_indexed_indices

#print axioms SubtreeProofs.Rust.TokenParser.parse_balanced_tokens_total_spec
#print axioms SubtreeProofs.Rust.TokenParser.parse_balanced_tokens_spec

#print axioms SubtreeProofs.Rust.TokenMatching.maximum_common_token_embedding_total_spec

#print axioms SubtreeProofs.Paper2004.OrderedTree.forestEmbeds_iff_parent
#print axioms SubtreeProofs.Rust.TokenMatching.maximum_common_token_embedding_of_forests

#print axioms SubtreeProofs.Rust.GuidedReconstruction.reconstruct_guided_spec
#print axioms SubtreeProofs.Rust.GuidedReconstruction.maximum_common_embedding_indexed_guided_of_trees

#print axioms SubtreeProofs.Rust.GuidedReconstruction.maximum_common_embedding_indexed_guided_with_cache_spec
#print axioms SubtreeProofs.Rust.GuidedReconstruction.CorrectGuided.cache_bound

#print axioms SubtreeProofs.Paper2004.OrderedTree.embeds_leafCount_le
#print axioms SubtreeProofs.Rust.GuidedReconstruction.maximum_common_embedding_indexed_guided_cache_of_trees

#print axioms SubtreeProofs.Rust.GuidedReconstruction.maximum_common_embedding_indexed_guided_payload_of_trees

#print axioms SubtreeProofs.Assignment.exists_single_cycle_repair
#print axioms SubtreeProofs.WeightedMatching.CopiedAssignmentReduction.matched_single_cycle_repair

#print axioms SubtreeProofs.Assignment.exists_cut_adjustment_on
#print axioms SubtreeProofs.Assignment.ideal_adjustment_increment_bound_on

#print axioms SubtreeProofs.Rust.SparseCut.minimum_sparse_cut_edges_spec
#print axioms SubtreeProofs.Rust.SparseCut.minimum_sparse_cut_adjustment_spec

#print axioms SubtreeProofs.Rust.SparseAssignmentAdjustment.adjust_potentials_sparse_safe_spec

#print axioms SubtreeProofs.WeightedMatching.CopiedAssignmentReduction.deleted_bi_state
#print axioms SubtreeProofs.Rust.SparseBiAdjustment.adjust_potentials_bi_safe_spec

#print axioms SubtreeProofs.WeightedMatching.CopiedAssignmentReduction.matched_single_cycle_decodes

#print axioms SubtreeProofs.Rust.SparseCut.adjust_sparse_cut_bi_safe_spec

#print axioms SubtreeProofs.Rust.SparseCut.advance_sparse_cut_spec

#print axioms SubtreeProofs.Assignment.exists_search_adjustment

#print axioms SubtreeProofs.Rust.SparseSearch.inverse_completed_spec

#print axioms SubtreeProofs.Rust.SparseSearch.body_step_spec

#print axioms SubtreeProofs.Rust.SparseSearch.body_preserves_spec

#print axioms SubtreeProofs.Rust.SparseSearch.find_sparse_augmenting_path_spec

#print axioms SubtreeProofs.Assignment.exists_ranked_augmentation

#print axioms SubtreeProofs.Rust.SparseSearch.flip_body_step_spec

#print axioms SubtreeProofs.Rust.SparseSearch.flip_sparse_path_spec
#print axioms SubtreeProofs.Rust.SparseSearch.augment_sparse_permutation_spec

#print axioms SubtreeProofs.AssignmentVertexDeletion.compact_deletion_state
#print axioms SubtreeProofs.Rust.SparseDeletion.compact_index_total_spec

#print axioms SubtreeProofs.Rust.LookupEvents.compare_erases
#print axioms SubtreeProofs.Rust.LookupEvents.copy_erases
#print axioms SubtreeProofs.Rust.LookupEvents.copyResult_erases
#print axioms SubtreeProofs.Rust.LookupEvents.lookup_erases
#print axioms SubtreeProofs.Rust.LookupEvents.lookup_bound
#print axioms SubtreeProofs.Rust.LookupEvents.sound_unit_bound
#print axioms SubtreeProofs.Rust.LookupEvents.extra_scan_changes_cost

#print axioms SubtreeProofs.Rust.LookupSource.run_bound
#print axioms SubtreeProofs.Rust.LookupSource.run_unique
#print axioms SubtreeProofs.Rust.LookupSource.copy_source
#print axioms SubtreeProofs.Rust.LookupSource.compare_source
#print axioms SubtreeProofs.Rust.LookupSource.lookup_source_spec
#print axioms SubtreeProofs.Rust.LookupSource.lookup_source_all_runs
#print axioms SubtreeProofs.Rust.LookupSource.lookup_aeneas_value_agreement
#print axioms SubtreeProofs.Rust.LookupSource.lookup_all_runs_bound
#print axioms SubtreeProofs.Rust.LookupSource.extra_compare_violates_old_bound

#print axioms SubtreeProofs.Rust.LookupSource.Control.dispatch_preserves
#print axioms SubtreeProofs.Rust.LookupSource.Control.exec_lower
#print axioms SubtreeProofs.Rust.LookupSource.Control.run_lower
#print axioms SubtreeProofs.Rust.LookupSource.Frontend.check_iff
#print axioms SubtreeProofs.Rust.LookupSource.Frontend.checked_run
#print axioms SubtreeProofs.Rust.LookupSource.Certificate.original_checked
#print axioms SubtreeProofs.Rust.LookupSource.Certificate.mutant_checked
#print axioms SubtreeProofs.Rust.LookupSource.Certificate.mutant_rejects_original
#print axioms SubtreeProofs.Rust.LookupSource.Certificate.original_run
#print axioms SubtreeProofs.Rust.LookupSource.Certificate.mutant_run
#print axioms SubtreeProofs.Rust.LookupSource.Certificate.original_run_bound
#print axioms SubtreeProofs.Rust.LookupSource.Certificate.mutant_violates_old_comparison_budget

#print axioms SubtreeProofs.Rust.LookupSource.Heap.alloc_fresh
#print axioms SubtreeProofs.Rust.LookupSource.Heap.alloc_rep
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Represents.mono
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Represents.typed
#print axioms SubtreeProofs.Rust.LookupSource.Heap.word_typed
#print axioms SubtreeProofs.Rust.LookupSource.Heap.table_typed
#print axioms SubtreeProofs.Rust.LookupSource.Heap.locate_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.borrow_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.operand_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.rvalue_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.scrutinee_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.action_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.exec_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.run_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.packWord_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.packTable_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.inputs_exist
#print axioms SubtreeProofs.Rust.LookupSource.Heap.certified_run_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.certified_mutant_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.copy_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.compare_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.lookup_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.lookup_all_runs

#print axioms SubtreeProofs.Rust.LookupSource.Heap.Footprint.unique
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Owns.footprint
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Owns.exclusive
#print axioms SubtreeProofs.Rust.LookupSource.Heap.alloc_owns
#print axioms SubtreeProofs.Rust.LookupSource.Heap.packWord_owns
#print axioms SubtreeProofs.Rust.LookupSource.Heap.packResult_owns
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Layout.copy_layout
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Layout.copyResult_layout
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Layout.lookup_layout
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Layout.outputLayout_owns
#print axioms SubtreeProofs.Rust.LookupSource.Heap.copy_return_owns
#print axioms SubtreeProofs.Rust.LookupSource.Heap.copyResult_return_owns
#print axioms SubtreeProofs.Rust.LookupSource.Heap.lookup_return_owns
#print axioms SubtreeProofs.Rust.LookupSource.Heap.lookup_return_footprint
#print axioms SubtreeProofs.Rust.LookupSource.Heap.lookup_no_old_owned_alias

#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.Plain.footprint
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.disposable_no_owned
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.return_frame_disposable
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.certified_run_safe
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.store_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.return_spec
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.operand_sound
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.operands_sound
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.rvalue_sound
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.profile_sound
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.action_sound
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.Guarded.erases
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.verify_sound
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.RunSafe.erases
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.run_sound
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.original_checked
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.mutant_checked
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.original_run_safe
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.mutant_run_safe
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Frame.lookup_guarded

#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.same_eq
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.sameList_eq
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.constructorFields_sound
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.constructorFields_complete
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.aggregate_shape
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.checkAction_sound
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.checkCode_sound
#print axioms SubtreeProofs.Rust.LookupSource.TypeReader.layoutCheck_sound
#print axioms SubtreeProofs.Rust.LookupSource.TypeReader.layouts_sound
#print axioms SubtreeProofs.Rust.LookupSource.TypeReader.check_sound
#print axioms SubtreeProofs.Rust.LookupSource.TypeReader.check_functions
#print axioms SubtreeProofs.Rust.LookupSource.TypeReader.Certificate.original_checked
#print axioms SubtreeProofs.Rust.LookupSource.TypeReader.Certificate.mutant_checked
#print axioms SubtreeProofs.Rust.LookupSource.TypeReader.Certificate.original_functions
#print axioms SubtreeProofs.Rust.LookupSource.TypeReader.Certificate.original_declarations

#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.typed_mono
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.fieldsTyped_mono
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.EnvTyped.get
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.EnvTyped.clear
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.EnvTyped.store
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.EnvTyped.mono
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.fieldsTyped_get
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.projection_fields
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.locate_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.operand_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.operands_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.borrow_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.rvalue_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.scrutinee_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.action_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.exec_typed
#print axioms SubtreeProofs.Rust.LookupSource.TypeReader.check_boundaries
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.fieldsTyped_slot
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.initial_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.alloc_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.run_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.original_bodies_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.mutant_bodies_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.original_run_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.mutant_run_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.certified_run_typed
#print axioms SubtreeProofs.Rust.LookupSource.SourceTypes.certified_mutant_typed

#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.footprint_mono
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.fieldsFootprint_mono
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.footprint_bounds
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.fieldsFootprint_bounds
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.fieldsFootprint_append
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.fieldsFootprint_split
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.fieldsFootprint_perm
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Separated.every_footprint
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Separated.perm
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Separated.mono
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Separated.plain_cons
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Separated.pack
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Separated.plain_fields
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Separated.alloc
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Transfers.refl
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Transfers.perm
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Transfers.trans
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Transfers.prefix
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.mem_values
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.values_covers
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Bounded.clear
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Bounded.store
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.tail_set_zero
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.tail_set_succ
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.clear_store
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.values_split
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.values_set_split
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.values_move
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.clear_transfer
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.store_transfer
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.plain_values
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.return_transfer
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.plain_transfer
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.operand_spatial
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.operands_spatial
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.rvalue_spatial
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.scrutinee_spatial
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.action_spatial
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.Trace.erases
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.selected_constraints
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.exec_spatial
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.plainFields_get
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.initial_plain
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.initial_bounded
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.boundary_bound
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.RunSpatial.erases
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.run_spatial
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.original_spatial
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.mutant_spatial
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.lookup_profile
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.lookup_spatial
#print axioms SubtreeProofs.Rust.LookupSource.Heap.Spatial.lookup_spatial_total

#print axioms SubtreeProofs.Rust.LookupSource.Stack.lower_erases
#print axioms SubtreeProofs.Rust.LookupSource.Stack.StateRep.empty
#print axioms SubtreeProofs.Rust.LookupSource.Stack.StateRep.full
#print axioms SubtreeProofs.Rust.LookupSource.Stack.status_set
#print axioms SubtreeProofs.Rust.LookupSource.Stack.StateRep.set
#print axioms SubtreeProofs.Rust.LookupSource.Stack.placeReady_sound
#print axioms SubtreeProofs.Rust.LookupSource.Stack.StateRep.initialized
#print axioms SubtreeProofs.Rust.LookupSource.Stack.operands_length
#print axioms SubtreeProofs.Rust.LookupSource.Stack.operand_sound
#print axioms SubtreeProofs.Rust.LookupSource.Stack.operands_sound
#print axioms SubtreeProofs.Rust.LookupSource.Stack.rvalue_sound
#print axioms SubtreeProofs.Rust.LookupSource.Stack.scrutinee_sound
#print axioms SubtreeProofs.Rust.LookupSource.Stack.store_spec
#print axioms SubtreeProofs.Rust.LookupSource.Stack.initial_rep
#print axioms SubtreeProofs.Rust.LookupSource.Stack.action_sound
#print axioms SubtreeProofs.Rust.LookupSource.Stack.closed_frame
#print axioms SubtreeProofs.Rust.LookupSource.Stack.selected_erase
#print axioms SubtreeProofs.Rust.LookupSource.Stack.Trace.erases
#print axioms SubtreeProofs.Rust.LookupSource.Stack.verify_sound
#print axioms SubtreeProofs.Rust.LookupSource.Stack.RunSafe.erases
#print axioms SubtreeProofs.Rust.LookupSource.Stack.run_sound
#print axioms SubtreeProofs.Rust.LookupSource.Stack.Certificate.original_lower
#print axioms SubtreeProofs.Rust.LookupSource.Stack.Certificate.mutant_lower
#print axioms SubtreeProofs.Rust.LookupSource.Stack.Certificate.original_erase
#print axioms SubtreeProofs.Rust.LookupSource.Stack.Certificate.mutant_erase
#print axioms SubtreeProofs.Rust.LookupSource.Stack.Certificate.original_checked
#print axioms SubtreeProofs.Rust.LookupSource.Stack.Certificate.mutant_checked
#print axioms SubtreeProofs.Rust.LookupSource.Stack.Certificate.countsCheck_sound
#print axioms SubtreeProofs.Rust.LookupSource.Stack.Certificate.original_counts
#print axioms SubtreeProofs.Rust.LookupSource.Stack.Certificate.mutant_counts
#print axioms SubtreeProofs.Rust.LookupSource.Stack.Certificate.original_run_safe
#print axioms SubtreeProofs.Rust.LookupSource.Stack.Certificate.mutant_run_safe
#print axioms SubtreeProofs.Rust.LookupSource.Stack.certified_run_stack
#print axioms SubtreeProofs.Rust.LookupSource.Stack.lookup_stack_total
