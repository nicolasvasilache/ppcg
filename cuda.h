#ifndef _CUDA_H
#define _CUDA_H

#include "ppcg_options.h"
#include "ppcg.h"

#if defined(__cplusplus)
extern "C" {
#endif

// Finer granularity print where void* user is a struct cuda_info
struct gpu_prog;
struct gpu_types;
__isl_give isl_printer *print_cuda(__isl_take isl_printer *p,
	struct gpu_prog *prog, __isl_keep isl_ast_node *tree,
        struct gpu_types *types, void *user);

int generate_cuda(isl_ctx *ctx, struct ppcg_options *options,
	const char *input);

#if defined(__cplusplus)
}
#endif

#endif
