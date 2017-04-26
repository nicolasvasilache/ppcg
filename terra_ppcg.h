
#include <ppcg.h>

#if defined(__cplusplus)
extern "C" {
#endif

isl_schedule *torchterra_transform(isl_ctx *ctx, isl_union_set *domain,
   isl_union_map *reads, isl_union_map *writes, isl_schedule *schedule,
   isl_set *context);

#if defined(__cplusplus)
}
#endif
