/*
 * Copyright 2010-2011 INRIA Saclay
 * Copyright 2014-2015 INRIA Rocquencourt
 *
 * Use of this software is governed by the MIT license
 *
 * Written by Sven Verdoolaege, INRIA Saclay - Ile-de-France,
 * Parc Club Orsay Universite, ZAC des vignes, 4 rue Jacques Monod,
 * 91893 Orsay, France
 * and Inria Paris - Rocquencourt, Domaine de Voluceau - Rocquencourt,
 * B.P. 105 - 78153 Le Chesnay, France
 */

#include <assert.h>
#include <ctype.h>
#include <stdio.h>
#include <string.h>

#include <isl/val.h>
#include <isl/aff.h>
#include <isl/set.h>
#include <isl/map.h>
#include <isl/union_set.h>
#include <isl/union_map.h>
#include <isl/constraint.h>
#include <isl/schedule_node.h>
#include <isl/schedule.h>

#include "grouping.h"
#include "schedule.h"
#include "util.h"

/* Add parameters with identifiers "ids" to "set".
 */
static __isl_give isl_set *add_params(__isl_take isl_set *set,
	__isl_keep isl_id_list *ids)
{
	int i, n;
	unsigned nparam;

	n = isl_id_list_n_id(ids);

	nparam = isl_set_dim(set, isl_dim_param);
	set = isl_set_add_dims(set, isl_dim_param, n);

	for (i = 0; i < n; ++i) {
		isl_id *id;

		id = isl_id_list_get_id(ids, i);
		set = isl_set_set_dim_id(set, isl_dim_param, nparam + i, id);
	}

	return set;
}

/* Equate the dimensions of "set" starting at "first" to
 * freshly created parameters with identifiers "ids".
 * The number of equated dimensions is equal to the number of elements in "ids".
 */
static __isl_give isl_set *parametrize(__isl_take isl_set *set,
	int first, __isl_keep isl_id_list *ids)
{
	int i, n;
	unsigned nparam;

	nparam = isl_set_dim(set, isl_dim_param);

	set = add_params(set, ids);

	n = isl_id_list_n_id(ids);
	for (i = 0; i < n; ++i)
		set = isl_set_equate(set, isl_dim_param, nparam + i,
					isl_dim_set, first + i);

	return set;
}

/* Given a parameter space "space", create a set of dimension "len"
 * of which the dimensions starting at "first" are equated to
 * freshly created parameters with identifiers "ids".
 */
__isl_give isl_set *parametrization(__isl_take isl_space *space,
	int len, int first, __isl_keep isl_id_list *ids)
{
	isl_set *set;

	space = isl_space_set_from_params(space);
	space = isl_space_add_dims(space, isl_dim_set, len);
	set = isl_set_universe(space);

	return parametrize(set, first, ids);
}

/* Load and return a schedule from a file called "filename".
 */
static __isl_give isl_schedule *load_schedule(isl_ctx *ctx,
	const char *filename)
{
	FILE *file;
	isl_schedule *schedule;

	file = fopen(filename, "r");
	if (!file) {
		fprintf(stderr, "Unable to open '%s' for reading\n", filename);
		return NULL;
	}
	schedule = isl_schedule_read_from_file(ctx, file);
	fclose(file);

	return schedule;
}

/* Save the schedule "schedule" to a file called "filename".
 * The schedule is printed in block style.
 */
static void save_schedule(__isl_keep isl_schedule *schedule,
	const char *filename)
{
	FILE *file;
	isl_ctx *ctx;
	isl_printer *p;

	if (!schedule)
		return;

	file = fopen(filename, "w");
	if (!file) {
		fprintf(stderr, "Unable to open '%s' for writing\n", filename);
		return;
	}
	ctx = isl_schedule_get_ctx(schedule);
	p = isl_printer_to_file(ctx, file);
	p = isl_printer_set_yaml_style(p, ISL_YAML_STYLE_BLOCK);
	p = isl_printer_print_schedule(p, schedule);
	isl_printer_free(p);
	fclose(file);
}

/* Compute a schedule on the domain of "sc" that respects the schedule
 * constraints in "sc", without trying to combine groups of statements.
 */
__isl_give isl_schedule *ppcg_compute_non_grouping_schedule(
	__isl_take isl_schedule_constraints *sc, struct ppcg_options *options)
{
	if (options->debug->dump_schedule_constraints)
		isl_schedule_constraints_dump(sc);
	return isl_schedule_constraints_compute_schedule(sc);
}

/* Compute a schedule on the domain of "sc" that respects the schedule
 * constraints in "sc".
 *
 * "schedule" is a known correct schedule that is used to combine
 * groups of statements if options->group_chains is set.
 */
__isl_give isl_schedule *ppcg_compute_schedule(
	__isl_take isl_schedule_constraints *sc,
	__isl_keep isl_schedule *schedule, struct ppcg_options *options)
{
	if (options->group_chains)
		return ppcg_compute_grouping_schedule(sc, schedule, options);
	return ppcg_compute_non_grouping_schedule(sc, options);
}

/* Obtain a schedule, either by reading it form a file
 * or by computing it using "compute".
 * Also take care of saving the computed schedule and/or
 * dumping the obtained schedule if requested by the user.
 */
__isl_give isl_schedule *ppcg_get_schedule(isl_ctx *ctx,
	struct ppcg_options *options,
	__isl_give isl_schedule *(*compute)(void *user), void *user)
{
	isl_schedule *schedule;

	if (options->load_schedule_file) {
		schedule = load_schedule(ctx, options->load_schedule_file);
	} else {
		schedule = compute(user);
		if (options->save_schedule_file)
			save_schedule(schedule, options->save_schedule_file);
	}
	if (options->debug->dump_schedule)
		isl_schedule_dump(schedule);

	return schedule;
}

/* Mark all dimensions in the band node "node" to be of "type".
 */
__isl_give isl_schedule_node *ppcg_set_schedule_node_type(
	__isl_take isl_schedule_node *node, enum isl_ast_loop_type type)
{
	int i, n;

	n = isl_schedule_node_band_n_member(node);
	for (i = 0; i < n; ++i)
		node = isl_schedule_node_band_member_set_ast_loop_type(node, i,
							type);

	return node;
}

/* Given a partial schedule "partial" at "node", expand it to operate
 * on domain instances at the leaves.
 */
static __isl_give isl_multi_union_pw_aff *expand_partial(
	__isl_keep isl_schedule_node *node,
	__isl_take isl_multi_union_pw_aff *partial)
{
	isl_union_pw_multi_aff *con;

	con = isl_schedule_node_get_subtree_contraction(node);
	return isl_multi_union_pw_aff_pullback_union_pw_multi_aff(partial, con);
}

/* Given a partial schedule in terms of untagged statement instances,
 * adjust it to apply to all tagged instances in domain and range of "tagged".
 */
static __isl_give isl_multi_union_pw_aff *tag_partial(
	__isl_keep isl_union_map *tagged,
	__isl_take isl_multi_union_pw_aff *partial)
{
	isl_union_pw_multi_aff *untag;

	untag = ppcg_extract_untag_from_tagged_relation(tagged);
	return isl_multi_union_pw_aff_pullback_union_pw_multi_aff(partial,
								untag);
}

/* Given a relation "umap" between pairs of domain instances
 * at the leaves of the schedule tree, select those
 * that are scheduled together by the ancestors of "node".
 * That is, select those that have the same value for the prefix schedule.
 * If "tagged" is set, then domain and range of "umap" refer
 * to tagged domain instances.
 */
static __isl_give isl_union_map *localize(__isl_keep isl_schedule_node *node,
	__isl_take isl_union_map *umap, int tagged)
{
	isl_multi_union_pw_aff *prefix;

	prefix = isl_schedule_node_get_prefix_schedule_multi_union_pw_aff(node);
	if (tagged)
		prefix = tag_partial(umap, prefix);
	prefix = expand_partial(node, prefix);
	return isl_union_map_eq_at_multi_union_pw_aff(umap, prefix);
}

/* Given a relation "untagged" between pairs of domain instances
 * at the leaves of the schedule tree, select those
 * that are scheduled together by the ancestors of "node".
 * That is, select those that have the same value for the prefix schedule.
 */
static __isl_give isl_union_map *localize_untagged(
	__isl_keep isl_schedule_node *node, __isl_take isl_union_map *untagged)
{
	return localize(node, untagged, 0);
}

/* Given a relation "tagged" between pairs of tagged domain instances
 * at the leaves of the schedule tree, select those
 * that are scheduled together by the ancestors of "node".
 * That is, select those that have the same value for the prefix schedule.
 */
static __isl_give isl_union_map *localize_tagged(
	__isl_keep isl_schedule_node *node, __isl_take isl_union_map *tagged)
{
	return localize(node, tagged, 1);
}

/* Return the validity constraints between pairs of instances
 * that are scheduled together by the ancestors of "node".
 * That is, select those validity constraints that relate
 * pairs of instances that have the same value for the prefix schedule.
 */
static __isl_give isl_union_map *get_local_validity(
	__isl_keep isl_schedule_node *node,
	__isl_keep isl_schedule_constraints *sc)
{
	isl_union_map *validity;

	validity = isl_schedule_constraints_get_validity(sc);
	validity = localize_untagged(node, validity);

	return validity;
}

/* Return the conditional validity constraints between pairs of tagged instances
 * that are scheduled together by the ancestors of "node".
 * That is, select those conditional validity constraints that relate
 * pairs of tagged instances that have the same value for the prefix schedule.
 */
static __isl_give isl_union_map *get_local_conditional_validity(
	__isl_keep isl_schedule_node *node,
	__isl_keep isl_schedule_constraints *sc)
{
	isl_union_map *validity;

	validity = isl_schedule_constraints_get_conditional_validity(sc);
	validity = localize_tagged(node, validity);

	return validity;
}

/* Return the conditional validity conditions between pairs of tagged instances
 * that are scheduled together by the ancestors of "node".
 * That is, select those conditional validity conditions that relate
 * pairs of tagged instances that have the same value for the prefix schedule.
 */
static __isl_give isl_union_map *get_local_conditional_validity_condition(
	__isl_keep isl_schedule_node *node,
	__isl_keep isl_schedule_constraints *sc)
{
	isl_union_map *condition;

	condition =
	    isl_schedule_constraints_get_conditional_validity_condition(sc);
	condition = localize_tagged(node, condition);

	return condition;
}

/* Given conditional validity constraints specified by "condition" and
 * "conditional", find those that need to be imposed because
 * the corresponding condition is set with respect to "partial".
 * The inputs are tagged relations.
 * That is, find the conditions where source and target are
 * not coscheduled by "partial" and return the adjacent
 * conditional validity constraints, with the tags removed.
 */
static __isl_give isl_union_map *active_conditional(
	__isl_keep isl_multi_union_pw_aff *partial,
	__isl_keep isl_union_map *condition,
	__isl_keep isl_union_map *conditional)
{
	isl_union_map *umap;
	isl_union_map *local;
	isl_multi_union_pw_aff *tagged;
	isl_union_set *source, *sink;

	condition = isl_union_map_copy(condition);
	conditional = isl_union_map_copy(conditional);

	tagged = tag_partial(condition, isl_multi_union_pw_aff_copy(partial));
	local = isl_union_map_copy(condition);
	local = isl_union_map_eq_at_multi_union_pw_aff(local, tagged);
	condition = isl_union_map_subtract(condition, local);

	source = isl_union_map_domain(isl_union_map_copy(condition));
	sink = isl_union_map_range(condition);

	umap = isl_union_map_copy(conditional);
	umap = isl_union_map_intersect_range(umap, source);
	conditional = isl_union_map_intersect_domain(conditional, sink);
	conditional = isl_union_map_union(conditional, umap);
	conditional = isl_union_map_factor_domain(conditional);

	return conditional;
}

/* Are all members of the partial schedule "partial" starting at "first"
 * valid for the given validity and conditional validity constraints?
 *
 * A validity constraint is violated by a member if any source is
 * scheduled after a corresponding target.
 * A conditional validity constraint is violated by a member if any source is
 * scheduled after a corresponding target and there is at least one
 * adjacent condition that is not coscheduled by the entire "partial".
 */
static isl_bool valid_members(__isl_keep isl_multi_union_pw_aff *partial,
	int first, __isl_keep isl_union_map *validity,
	__isl_keep isl_union_map *condition,
	__isl_keep isl_union_map *conditional)
{
	int i, n;
	isl_bool valid = isl_bool_true;

	if (!partial)
		return isl_bool_error;
	n = isl_multi_union_pw_aff_dim(partial, isl_dim_set);
	if (first >= n)
		return isl_bool_true;

	validity = isl_union_map_copy(validity);
	conditional = active_conditional(partial, condition, conditional);
	validity = isl_union_map_union(validity, conditional);

	for (i = first; i < n; ++i) {
		isl_union_map *validity_i;
		isl_union_pw_aff *upa;
		isl_multi_union_pw_aff *partial_i;

		upa = isl_multi_union_pw_aff_get_union_pw_aff(partial, i);
		partial_i = isl_multi_union_pw_aff_from_union_pw_aff(upa);
		validity_i = isl_union_map_copy(validity);
		validity_i = isl_union_map_lex_gt_at_multi_union_pw_aff(
						    validity_i, partial_i);
		valid = isl_union_map_is_empty(validity_i);
		isl_union_map_free(validity_i);

		if (valid < 0 || !valid)
			break;
	}

	isl_union_map_free(validity);

	return valid;
}

/* If the band node "node" has exactly one member then mark it permutable.
 * Otherwise, check whether all members (except the first) are valid
 * with respect to the (conditional) validity constraints in "sc"
 * that are active at the top of the node.
 * The first member is not checked because the schedule tree
 * is assumed to be valid (aside from the initial band properties).
 * The schedule constraints in "sc" are specified in terms
 * of the domain elements at the leaves of the schedule tree.
 *
 * Only the (conditional) validity constraints that are active
 * at "node" need to be checked.  The partial schedule of the band node
 * is reformulated in terms of the domain elements at the leaves
 * before checking the validity of the members.
 */
static __isl_give isl_schedule_node *band_set_permutable(
	__isl_take isl_schedule_node *node,
	__isl_keep isl_schedule_constraints *sc)
{
	isl_union_map *condition, *validity, *conditional;
	isl_multi_union_pw_aff *partial;
	isl_union_pw_multi_aff *contraction;
	isl_bool valid;

	if (isl_schedule_node_band_n_member(node) == 1)
		return isl_schedule_node_band_set_permutable(node, 1);

	validity = get_local_validity(node, sc);
	condition = get_local_conditional_validity_condition(node, sc);
	conditional = get_local_conditional_validity(node, sc);

	contraction = isl_schedule_node_get_subtree_contraction(node);
	partial = isl_schedule_node_band_get_partial_schedule(node);
	partial = isl_multi_union_pw_aff_pullback_union_pw_multi_aff(partial,
								contraction);

	valid = valid_members(partial, 1, validity, condition, conditional);

	isl_multi_union_pw_aff_free(partial);
	isl_union_map_free(validity);
	isl_union_map_free(condition);
	isl_union_map_free(conditional);

	if (valid < 0)
		return isl_schedule_node_free(node);

	node = isl_schedule_node_band_set_permutable(node, valid);

	return node;
}

/* Return the coincidence constraints between pairs of instances
 * that are scheduled together by the ancestors of "node".
 * That is, select those coincidence constraints that relate
 * pairs of instances that have the same value for the prefix schedule.
 */
static __isl_give isl_union_map *get_local_coincidence(
	__isl_keep isl_schedule_node *node,
	__isl_keep isl_schedule_constraints *sc)
{
	isl_union_map *coincidence;

	coincidence = isl_schedule_constraints_get_coincidence(sc);
	coincidence = localize_untagged(node, coincidence);

	return coincidence;
}

/* For each member in the band node "node", determine whether
 * it is coincident with respect to the outer nodes and mark
 * it accordingly.
 *
 * That is, for each coincidence constraint between pairs
 * of instances that are scheduled together by the outer nodes,
 * check that domain and range are assigned the same value
 * by the band member.  This test is performed by checking
 * that imposing the same value for the band member does not
 * remove any elements from the set of coincidence constraints.
 */
static __isl_give isl_schedule_node *band_set_coincident(
	__isl_take isl_schedule_node *node,
	__isl_keep isl_schedule_constraints *sc)
{
	isl_union_map *coincidence;
	isl_union_pw_multi_aff *contraction;
	isl_multi_union_pw_aff *partial;
	int i, n;

	coincidence = get_local_coincidence(node, sc);

	partial = isl_schedule_node_band_get_partial_schedule(node);
	contraction = isl_schedule_node_get_subtree_contraction(node);
	partial = isl_multi_union_pw_aff_pullback_union_pw_multi_aff(partial,
								contraction);
	n = isl_schedule_node_band_n_member(node);
	for (i = 0; i < n; ++i) {
		isl_union_map *coincidence_i;
		isl_union_pw_aff *upa;
		isl_multi_union_pw_aff *partial_i;
		int subset;

		upa = isl_multi_union_pw_aff_get_union_pw_aff(partial, i);
		partial_i = isl_multi_union_pw_aff_from_union_pw_aff(upa);
		coincidence_i = isl_union_map_copy(coincidence);
		coincidence_i = isl_union_map_eq_at_multi_union_pw_aff(
						    coincidence_i, partial_i);
		subset = isl_union_map_is_subset(coincidence, coincidence_i);
		isl_union_map_free(coincidence_i);

		if (subset < 0)
			break;
		node = isl_schedule_node_band_member_set_coincident(node, i,
								    subset);
	}
	if (i < n)
		node = isl_schedule_node_free(node);
	isl_multi_union_pw_aff_free(partial);
	isl_union_map_free(coincidence);

	return node;
}

/* Determine the properties of band node "node"
 * based on the schedule constraints "sc".
 * The schedule constraints are expected to be specified in terms
 * of the domain elements at the leaves of the schedule tree.
 *
 * In particular, if the band has exactly one member, then mark it permutable.
 * Mark the band members coincident based on the coincidence constraints
 * of "sc".
 */
__isl_give isl_schedule_node *ppcg_schedule_node_band_set_properties(
	__isl_take isl_schedule_node *node,
	__isl_keep isl_schedule_constraints *sc)
{
	if (isl_schedule_node_band_n_member(node) == 0)
		return node;

	node = band_set_permutable(node, sc);
	node = band_set_coincident(node, sc);

	return node;
}

/* Are all children of the sequence node "node" band nodes
 * living in "space"?
 * "space" has been obtained from the first child, so the first child
 * does not need to be checked.
 */
static isl_bool band_children_with_space(__isl_keep isl_schedule_node *node,
	__isl_keep isl_space *space)
{
	enum isl_schedule_node_type type;
	int i, n;
	isl_bool ok;

	n = isl_schedule_node_n_children(node);

	ok = isl_bool_true;
	for (i = 1; ok == isl_bool_true && i < n; ++i) {
		isl_schedule_node *child;

		child = isl_schedule_node_get_child(node, i);
		child = isl_schedule_node_child(child, 0);
		type = isl_schedule_node_get_type(child);
		if (type < 0)
			ok = isl_bool_error;
		else if (type != isl_schedule_node_band) {
			ok = isl_bool_false;
		} else {
			isl_space *space2;

			space2 = isl_schedule_node_band_get_space(child);
			ok = isl_space_has_equal_tuples(space, space2);
			isl_space_free(space2);
		}
		isl_schedule_node_free(child);
	}

	return ok;
}

/* Does "node" point to a tree of the form
 *
 *      S
 *  ____|____
 *  |   |   |
 *  B  ...  B
 *
 * with B band nodes and S a sequence node, and
 * with all B nodes living in the same space?
 */
static isl_bool sequence_with_equal_spaced_band_children(
	__isl_keep isl_schedule_node *node)
{
	enum isl_schedule_node_type type;
	isl_bool ok;

	type = isl_schedule_node_get_type(node);
	if (type < 0)
		return isl_bool_error;
	if (type != isl_schedule_node_sequence)
		return isl_bool_false;

	node = isl_schedule_node_copy(node);
	node = isl_schedule_node_child(node, 0);
	node = isl_schedule_node_child(node, 0);

	type = isl_schedule_node_get_type(node);
	if (type < 0)
		ok = isl_bool_error;
	else
		ok = type == isl_schedule_node_band;

	if (ok == isl_bool_true) {
		isl_space *space;

		space = isl_schedule_node_band_get_space(node);
		node = isl_schedule_node_ancestor(node, 2);
		ok = band_children_with_space(node, space);
		isl_space_free(space);
	}

	isl_schedule_node_free(node);
	return ok;
}

/* Does "node" have the right shape for applying
 * cross band tiling?
 * That is, does "node" point to a tree of the form
 *
 *      A
 *      |
 *      S
 *  ____|____
 *  |   |   |
 *  B  ...  B
 *
 * with A and B band nodes and S a sequence node, and
 * with all B nodes living in the same space?
 */
isl_bool ppcg_schedule_node_has_cross_tile_shape(
	__isl_keep isl_schedule_node *node)
{
	enum isl_schedule_node_type type;
	isl_bool ok;

	type = isl_schedule_node_get_type(node);
	if (type < 0)
		return isl_bool_error;
	if (type != isl_schedule_node_band)
		return isl_bool_false;

	node = isl_schedule_node_get_child(node, 0);
	ok = sequence_with_equal_spaced_band_children(node);
	isl_schedule_node_free(node);

	return ok;
}

/* Assuming that "node" points to a tree of the form
 *
 *      A
 *      |
 *      S
 *  ____|____
 *  |   |   |
 *  B  ...  B
 *
 * with A and B band nodes and S a sequence node, and
 * with all B nodes living in the same space,
 * return the product of the spaces of A and B.
 */
__isl_give isl_space *ppcg_schedule_node_get_cross_tile_space(
	__isl_keep isl_schedule_node *node)
{
	isl_space *space, *space2;

	space = isl_schedule_node_band_get_space(node);
	node = isl_schedule_node_get_child(node, 0);
	node = isl_schedule_node_child(node, 0);
	node = isl_schedule_node_child(node, 0);
	space2 = isl_schedule_node_band_get_space(node);
	isl_schedule_node_free(node);

	return isl_space_product(space, space2);
}

/* Are all members of the band node "node" marked coincident?
 */
static isl_bool all_coincident(__isl_keep isl_schedule_node *node)
{
	int i, n;

	if (!node)
		return isl_bool_error;

	n = isl_schedule_node_band_n_member(node);

	for (i = 0; i < n; ++i) {
		isl_bool ok;

		ok = isl_schedule_node_band_member_get_coincident(node, i);
		if (ok < 0 || !ok)
			return ok;
	}

	return isl_bool_true;
}

/* Is is obvious that cross band tiling can be applied at "node",
 * given that the schedule tree has the right shape?
 * That is, are all members of "node" marked coincident?
 * A fully coincident band can be trivially pushed down the tree.
 * This assumes that the coincidence marking is consistent with
 * the (other) schedule constraints.
 */
static isl_bool plain_can_cross_tile(__isl_keep isl_schedule_node *node)
{
	return all_coincident(node);
}

/* Is is obvious that cross band tiling can be applied at "node"?
 * That is, does the schedule tree have the right shape and
 * are all members of "node" marked coincident?
 */
isl_bool ppcg_schedule_node_plain_can_cross_tile(
	__isl_keep isl_schedule_node *node)
{
	isl_bool shape;

	shape = ppcg_schedule_node_has_cross_tile_shape(node);
	if (shape < 0 || !shape)
		return shape;

	return plain_can_cross_tile(node);
}

/* Intersect domain and range of "umap" with "uset".
 */
static __isl_give isl_union_map *intersect_untagged_domains(
	__isl_take isl_union_map *umap, __isl_keep isl_union_set *uset)
{
	umap = isl_union_map_intersect_domain(umap, isl_union_set_copy(uset));
	umap = isl_union_map_intersect_range(umap, isl_union_set_copy(uset));
	return umap;
}

/* Given a binary relation "umap" between tagged domain instances,
 * restrict the (untagged) domain instances to "uset".
 * That is, intersect the domain instances embedded
 * in domain and range of "umap" with "uset".
 */
static __isl_give isl_union_map *intersect_tagged_domains(
	__isl_take isl_union_map *umap, __isl_keep isl_union_set *uset)
{
	umap = isl_union_map_intersect_domain_wrapped_domain(umap,
						    isl_union_set_copy(uset));
	umap = isl_union_map_intersect_range_wrapped_domain(umap,
						    isl_union_set_copy(uset));
	return umap;
}

/* Given a pointer "node" to a filter child of a sequence node that
 * itself has a band node as child,
 * is the band node valid with respect to the given
 * (conditional) validity constraints?
 * The conditions are evaluated in terms of the band node schedule
 * combined with "outer".
 * Both the (conditional) validity constraints and "outer"
 * are formulated in terms of domain instances at the leaves.
 * "contraction" maps those instances to the instances active at "node".
 *
 * Only the constraints that apply to statement instances that
 * reach the band node are relevant, so the constraints
 * are intersected with the filter of "node".
 */
static isl_bool is_valid_at( __isl_keep isl_schedule_node *node,
	__isl_keep isl_union_map *validity,
	__isl_keep isl_union_map *condition,
	__isl_keep isl_union_map *conditional,
	__isl_keep isl_union_pw_multi_aff *contraction,
	__isl_keep isl_multi_union_pw_aff *outer)
{
	int n_outer;
	isl_bool valid;
	isl_union_set *filter;
	isl_multi_union_pw_aff *partial;

	n_outer = isl_multi_union_pw_aff_dim(outer, isl_dim_set);

	filter = isl_schedule_node_filter_get_filter(node);
	filter = isl_union_set_preimage_union_pw_multi_aff(filter,
				    isl_union_pw_multi_aff_copy(contraction));
	validity = isl_union_map_copy(validity);
	validity = intersect_untagged_domains(validity, filter);
	condition = isl_union_map_copy(condition);
	condition = intersect_tagged_domains(condition, filter);
	conditional = isl_union_map_copy(conditional);
	conditional = intersect_tagged_domains(conditional, filter);

	outer = isl_multi_union_pw_aff_copy(outer);
	outer = isl_multi_union_pw_aff_intersect_domain(outer, filter);

	node = isl_schedule_node_copy(node);
	node = isl_schedule_node_child(node, 0);
	partial = isl_schedule_node_band_get_partial_schedule(node);
	isl_schedule_node_free(node);
	partial = isl_multi_union_pw_aff_pullback_union_pw_multi_aff(partial,
				    isl_union_pw_multi_aff_copy(contraction));
	partial = isl_multi_union_pw_aff_range_product(outer, partial);

	valid = valid_members(partial, n_outer,
				validity, condition, conditional);

	isl_multi_union_pw_aff_free(partial);

	isl_union_map_free(conditional);
	isl_union_map_free(condition);
	isl_union_map_free(validity);

	return valid;
}

/* Can cross band tiling be applied at "node",
 * given that the schedule tree has the right shape?
 *
 * That is, given a tree of the form
 *
 *      A
 *      |
 *      S
 *  ____|____
 *  |   |   |
 *  B  ...  B
 *
 * can node A be pushed down?
 * In other words, are sequence node S and band nodes B valid
 * with respect to the schedule constraints at node A?
 * The schedule constraints "sc" are assumed to be formulated
 * in terms of the domain instances at the leaf nodes of the tree.
 *
 * Since the point bands of A and B will be combined into a single node,
 * the conditions of the conditional validity constraints need
 * to be evaluated with respect to their combined partial schedule.
 */
static isl_bool can_cross_tile(__isl_keep isl_schedule_node *node,
	__isl_keep isl_schedule_constraints *sc)
{
	isl_bool valid;
	isl_union_map *validity, *condition, *conditional;
	isl_union_pw_multi_aff *contraction;
	isl_multi_union_pw_aff *partial, *outer;
	isl_schedule_node *seq;
	int i, n;

	validity = get_local_validity(node, sc);
	condition = get_local_conditional_validity_condition(node, sc);
	conditional = get_local_conditional_validity(node, sc);

	contraction = isl_schedule_node_get_subtree_contraction(node);

	seq = isl_schedule_node_get_child(node, 0);
	partial =
	    isl_schedule_node_sequence_get_partial_schedule_multi_union_pw_aff(
		seq);

	partial = isl_multi_union_pw_aff_pullback_union_pw_multi_aff(partial,
				    isl_union_pw_multi_aff_copy(contraction));
	valid = valid_members(partial, 0, validity, condition, conditional);
	isl_multi_union_pw_aff_free(partial);

	outer = isl_schedule_node_band_get_partial_schedule(node);
	outer = isl_multi_union_pw_aff_pullback_union_pw_multi_aff(outer,
				    isl_union_pw_multi_aff_copy(contraction));

	n = isl_schedule_node_n_children(seq);
	for (i = 0; valid == isl_bool_true && i < n; ++i) {
		isl_schedule_node *child;

		child = isl_schedule_node_get_child(seq, i);
		valid = is_valid_at(child, validity, condition, conditional,
				    contraction, outer);
		isl_schedule_node_free(child);
	}

	isl_schedule_node_free(seq);

	isl_multi_union_pw_aff_free(outer);
	isl_union_pw_multi_aff_free(contraction);
	isl_union_map_free(validity);
	isl_union_map_free(condition);
	isl_union_map_free(conditional);

	return valid;
}

/* Can cross band tiling be applied at "node"?
 * That is, does the schedule tree have the right shape and
 * can the top level band be pushed down without affecting
 * the validity of the tree?
 * The schedule constraints "sc" are used to determine
 * the validity of pushing the node down.
 * They are assumed to be formulated
 * in terms of the domain instances at the leaf nodes of the tree.
 *
 * First check if the node can trivially be pushed down.
 * Otherwise, use the schedule constraints to check
 * if it can be pushed down.
 */
isl_bool ppcg_schedule_node_can_cross_tile(__isl_keep isl_schedule_node *node,
	__isl_keep isl_schedule_constraints *sc)
{
	isl_bool shape, plain;

	shape = ppcg_schedule_node_has_cross_tile_shape(node);
	if (shape < 0 || !shape)
		return shape;

	plain = plain_can_cross_tile(node);
	if (plain < 0 || plain)
		return plain;

	return can_cross_tile(node, sc);
}

/* Perform cross band tiling at "node" with tile sizes specified by "sizes".
 * "node" is expected to point to a subtree of the form
 *
 *      A
 *      |
 *      S
 *  ____|____
 *  |   |   |
 *  B  ...  B
 *
 * with A and B band nodes and S a sequence node.
 * Furthermore, all B nodes have the same space.
 * The space of "sizes" is the product of that of A and B,
 * i.e., the space returned by ppcg_schedule_node_get_cross_tile_space.
 *
 * The result is of the form
 *
 *      TA
 *      |
 *      S
 *  ____|____
 *  |   |   |
 *  TB ...  TB
 *  |       |
 *  PA      PA
 *  PB      PB
 *
 * with TX and PX the tile and point bands of X.
 * "sc" is used to determine the properties of PA;PB.
 *
 * The caller is responsible for ensuring that cross tiling is valid.
 * In particular, it needs to be possible to push down PA
 * without affecting the validity of the rest of the tree.
 *
 * First tile A and push PA through the sequence.
 * Then tile B in each branch, push PA through TB, combine
 * PA and PB into a single band and determine its properties.
 */
__isl_give isl_schedule_node *ppcg_schedule_node_cross_tile(
	__isl_take isl_schedule_node *node, __isl_take isl_multi_val *sizes,
	__isl_keep isl_schedule_constraints *sc)
{
	int i, n;
	isl_multi_val *outer_sizes;

	outer_sizes = isl_multi_val_copy(sizes);
	outer_sizes = isl_multi_val_factor_domain(outer_sizes);
	node = isl_schedule_node_band_tile(node, outer_sizes);
	sizes = isl_multi_val_factor_range(sizes);

	node = isl_schedule_node_child(node, 0);
	node = isl_schedule_node_band_lower(node);

	n = isl_schedule_node_n_children(node);
	for (i = 0; i < n; ++i) {
		node = isl_schedule_node_child(node, i);
		node = isl_schedule_node_child(node, 0);
		node = isl_schedule_node_child(node, 0);
		node = isl_schedule_node_band_tile(node,
						    isl_multi_val_copy(sizes));
		node = isl_schedule_node_parent(node);
		node = isl_schedule_node_band_lower(node);
		node = isl_schedule_node_child(node, 0);
		node = isl_schedule_node_band_join_child(node);
		node = ppcg_schedule_node_band_set_properties(node, sc);
		node = isl_schedule_node_ancestor(node, 3);
	}
	isl_multi_val_free(sizes);

	node = isl_schedule_node_parent(node);

	return node;
}
