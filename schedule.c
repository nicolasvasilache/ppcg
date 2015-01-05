/*
 * Copyright 2010-2011 INRIA Saclay
 * Copyright 2014      INRIA Rocquencourt
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

/* If the band node "node" has exactly one member then mark it permutable.
 */
static __isl_give isl_schedule_node *band_set_permutable(
	__isl_take isl_schedule_node *node,
	__isl_keep isl_schedule_constraints *sc)
{
	if (isl_schedule_node_band_n_member(node) == 1)
		node = isl_schedule_node_band_set_permutable(node, 1);

	return node;
}

/* Return the coincidence constraints between pairs of instances
 * that are scheduled together by the ancestors of "node".
 * That is, select those coincidence constraints that relate
 * pairs of instances that have the same value for the prefix schedule.
 * If the schedule depth is zero, then the prefix schedule does not
 * contain any information, so we intersect domain and range
 * of the schedule constraints with the reaching domain elements instead.
 */
static __isl_give isl_union_map *get_local_coincidence(
	__isl_keep isl_schedule_node *node,
	__isl_keep isl_schedule_constraints *sc)
{
	isl_union_map *coincidence;
	isl_multi_union_pw_aff *prefix;
	isl_union_pw_multi_aff *contraction;

	coincidence = isl_schedule_constraints_get_coincidence(sc);
	contraction = isl_schedule_node_get_subtree_contraction(node);
	if (isl_schedule_node_get_schedule_depth(node) == 0) {
		isl_union_set *domain;

		domain = isl_schedule_node_get_domain(node);
		domain = isl_union_set_preimage_union_pw_multi_aff(domain,
						    contraction);
		coincidence = isl_union_map_intersect_domain(coincidence,
						    isl_union_set_copy(domain));
		coincidence = isl_union_map_intersect_range(coincidence,
						    domain);
		return coincidence;
	}

	prefix = isl_schedule_node_get_prefix_schedule_multi_union_pw_aff(node);
	prefix = isl_multi_union_pw_aff_pullback_union_pw_multi_aff(prefix,
								contraction);
	return isl_union_map_eq_at_multi_union_pw_aff(coincidence, prefix);
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
