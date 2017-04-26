#ifndef GPU_HYBRID_H
#define GPU_HYBRID_H

#include <isl/schedule_node.h>

#include "gpu.h"
#include "hybrid.h"

#if defined(__cplusplus)
extern "C" {
#endif

__isl_give isl_schedule_node *gpu_hybrid_tile(struct gpu_gen *gen,
	__isl_take isl_schedule_node *node, __isl_take ppcg_ht_bounds *bounds,
	int *tile_sizes);

#if defined(__cplusplus)
}
#endif

#endif
