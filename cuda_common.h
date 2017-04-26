#ifndef _CUDA_COMMON_H_
#define _CUDA_COMMON_H_

#include <stdio.h>

struct cuda_info {
	FILE *host_c;
	FILE *kernel_c;
	FILE *kernel_h;
};

#if defined(__cplusplus)
extern "C" {
#endif

void cuda_open_files(struct cuda_info *info, const char *input);
void cuda_close_files(struct cuda_info *info);

#if defined(__cplusplus)
}
#endif

#endif
