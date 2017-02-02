
#include <ppcg.h>

isl_schedule *torchterra_transform(isl_ctx *ctx, isl_union_set *domain,
   isl_union_map *reads, isl_union_map *writes, isl_schedule *schedule,
   isl_set *context);