/*
 * Copyright 2012-2013 Ecole Normale Superieure
 * Copyright 2015      INRIA Rocquencourt
 *
 * Use of this software is governed by the MIT license
 *
 * Written by Sven Verdoolaege,
 * Ecole Normale Superieure, 45 rue d'Ulm, 75230 Paris, France
 * and Inria Paris - Rocquencourt, Domaine de Voluceau - Rocquencourt,
 * B.P. 105 - 78153 Le Chesnay, France
 */

#include <isl/space.h>
#include <isl/val.h>
#include <isl/aff.h>
#include <isl/set.h>
#include <isl/union_set.h>
#include <isl/union_map.h>

#include "util.h"

/* Construct an isl_multi_val living in "space" with all values equal to "val".
 */
__isl_give isl_multi_val *ppcg_multi_val_from_int(__isl_take isl_space *space,
	int val)
{
	int i, n;
	isl_ctx *ctx;
	isl_val *v;
	isl_multi_val *mv;

	if (!space)
		return NULL;

	ctx = isl_space_get_ctx(space);
	n = isl_space_dim(space, isl_dim_set);
	mv = isl_multi_val_zero(space);
	v = isl_val_int_from_si(ctx, val);
	for (i = 0; i < n; ++i)
		mv = isl_multi_val_set_val(mv, i, isl_val_copy(v));
	isl_val_free(v);

	return mv;
}

/* Construct an isl_multi_val living in "space" with values specified
 * by "list".  "list" is assumed to have at least as many entries
 * as the set dimension of "space".
 */
__isl_give isl_multi_val *ppcg_multi_val_from_int_list(
	__isl_take isl_space *space, int *list)
{
	int i, n;
	isl_ctx *ctx;
	isl_multi_val *mv;

	if (!space)
		return NULL;

	ctx = isl_space_get_ctx(space);
	n = isl_space_dim(space, isl_dim_set);
	mv = isl_multi_val_zero(space);
	for (i = 0; i < n; ++i) {
		isl_val *v;

		v = isl_val_int_from_si(ctx, list[i]);
		mv = isl_multi_val_set_val(mv, i, v);
	}

	return mv;
}

/* Compute the size of a bounding box around the origin and "set",
 * where "set" is assumed to contain only non-negative elements.
 * In particular, compute the maximal value of "set" in each direction
 * and add one.
 */
__isl_give isl_multi_pw_aff *ppcg_size_from_extent(__isl_take isl_set *set)
{
	int i, n;
	isl_multi_pw_aff *mpa;

	n = isl_set_dim(set, isl_dim_set);
	mpa = isl_multi_pw_aff_zero(isl_set_get_space(set));
	for (i = 0; i < n; ++i) {
		isl_space *space;
		isl_aff *one;
		isl_pw_aff *bound;

		if (!isl_set_dim_has_upper_bound(set, isl_dim_set, i)) {
			const char *name;
			name = isl_set_get_tuple_name(set);
			if (!name)
				name = "";
			fprintf(stderr, "unable to determine extent of '%s' "
				"in dimension %d\n", name, i);
			set = isl_set_free(set);
		}
		bound = isl_set_dim_max(isl_set_copy(set), i);

		space = isl_pw_aff_get_domain_space(bound);
		one = isl_aff_zero_on_domain(isl_local_space_from_space(space));
		one = isl_aff_add_constant_si(one, 1);
		bound = isl_pw_aff_add(bound, isl_pw_aff_from_aff(one));
		mpa = isl_multi_pw_aff_set_pw_aff(mpa, i, bound);
	}
	isl_set_free(set);

	return mpa;
}

/* Given a binary relation between tagged instances,
 * construct a function that drops the tags from
 * the domain and the range instances.
 */
__isl_give isl_union_pw_multi_aff *ppcg_extract_untag_from_tagged_relation(
	__isl_keep isl_union_map *tagged)
{
	isl_union_map *universe;
	isl_union_set *domain, *range;

	universe = isl_union_map_universe(isl_union_map_copy(tagged));
	domain = isl_union_map_domain(isl_union_map_copy(universe));
	range = isl_union_map_range(universe);
	domain = isl_union_set_union(domain, range);
	universe = isl_union_set_unwrap(domain);
	return isl_union_map_domain_map_union_pw_multi_aff(universe);
}
