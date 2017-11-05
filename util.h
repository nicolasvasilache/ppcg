#ifndef UTIL_H
#define UTIL_H

#include <string.h>

#include <isl/space.h>
#include <isl/val.h>
#include <isl/aff_type.h>
#include <isl/union_map_type.h>

/* Compare the prefix of "s" to "prefix" up to the length of "prefix".
 */
static inline int prefixcmp(const char *s, const char *prefix)
{
	return strncmp(s, prefix, strlen(prefix));
}

__isl_give isl_multi_val *ppcg_multi_val_from_int(__isl_take isl_space *space,
	int val);
__isl_give isl_multi_val *ppcg_multi_val_from_int_list(
	__isl_take isl_space *space, int *list);
__isl_give isl_multi_pw_aff *ppcg_size_from_extent(__isl_take isl_set *set);

__isl_give isl_union_pw_multi_aff *ppcg_extract_untag_from_tagged_relation(
	__isl_keep isl_union_map *tagged);

#endif
