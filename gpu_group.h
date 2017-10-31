#ifndef GPU_GROUP_H
#define GPU_GROUP_H

#include <isl/schedule_node.h>
#include "gpu.h"

/* A group of array references in a kernel that should be handled together.
 * If private_tile is not NULL, then it is mapped to registers.
 * Otherwise, if shared_tile is not NULL, it is mapped to shared memory.
 * Otherwise, it is accessed from global memory.
 * Note that if both private_tile and shared_tile are set, then shared_tile
 * is only used inside group_common_shared_memory_tile.
 */
struct gpu_array_ref_group {
	/* The references in this group access this local array. */
	struct gpu_local_array_info *local_array;
	/* This is the corresponding array. */
	struct gpu_array_info *array;
	/* Position of this group in the list of reference groups of array. */
	int nr;

	/* The following fields are use during the construction of the groups.
	 * access is the combined access relation relative to the private
	 * memory tiling.  In particular, the domain of the map corresponds
	 * to the first thread_depth dimensions of the kernel schedule.
	 * write is set if any access in the group is a write.
	 * exact_write is set if all writes are definite writes.
	 * slice is set if there is at least one access in the group
	 * that refers to more than one element
	 * "min_depth" is the minimum of the tile depths and thread_depth.
	 */
	isl_map *access;
	int write;
	int exact_write;
	int slice;
	int min_depth;

	/* The shared memory tile, NULL if none. */
	struct gpu_array_tile *shared_tile;

	/* The private memory tile, NULL if none. */
	struct gpu_array_tile *private_tile;

	/* References in this group; point to elements of a linked list. */
	int n_ref;
	struct gpu_stmt_access **refs;
};

int gpu_group_references(struct ppcg_kernel *kernel,
	__isl_keep isl_schedule_node *node);

__isl_give isl_printer *gpu_array_ref_group_print_name(
	struct gpu_array_ref_group *group, __isl_take isl_printer *p);
void gpu_array_ref_group_compute_tiling(struct gpu_array_ref_group *group);
__isl_give isl_union_map *gpu_array_ref_group_access_relation(
	struct gpu_array_ref_group *group, int read, int write);
int gpu_array_ref_group_requires_unroll(struct gpu_array_ref_group *group);
enum ppcg_group_access_type gpu_array_ref_group_type(
	struct gpu_array_ref_group *group);
struct gpu_array_tile *gpu_array_ref_group_tile(
	struct gpu_array_ref_group *group);
struct gpu_array_ref_group *gpu_array_ref_group_free(
	struct gpu_array_ref_group *group);

/* Internal data structure for gpu_group_references.
 *
 * scop represents the input scop.
 * kernel_depth is the schedule depth where the kernel launch will
 * be introduced, i.e., it is the depth of the band that is mapped
 * to blocks.
 * shared_depth is the schedule depth at which the copying to/from
 * shared memory is computed.  The copy operation may then
 * later be hoisted to a higher level.
 * thread_depth is the schedule depth where the thread mark is located,
 * i.e., it is the depth of the band that is mapped to threads and also
 * the schedule depth at which the copying to/from private memory
 * is computed.  The copy operation may then later be hoisted to
 * a higher level.
 * n_thread is the number of schedule dimensions in the band that
 * is mapped to threads.
 * privatization lives in the range of thread_sched (i.e., it is
 * of dimension thread_depth + n_thread) and encodes the mapping
 * to thread identifiers (as parameters).
 * host_sched contains the kernel_depth dimensions of the host schedule.
 * shared_sched contains the first shared_depth dimensions of the
 * kernel schedule.
 * copy_sched contains the first thread_depth dimensions of the
 * kernel schedule.
 * thread_sched contains the first (thread_depth + n_thread) dimensions
 * of the kernel schedule.
 * full_sched is a union_map representation of the entire kernel schedule.
 * The schedules are all formulated in terms of the original statement
 * instances, i.e., those that appear in the domains of the access
 * relations.
 */
struct gpu_group_data {
  struct ppcg_scop *scop;
  int kernel_depth;
  int shared_depth;
  int thread_depth;
  int n_thread;
  isl_set *privatization;
  isl_union_map *host_sched;
  isl_union_map *shared_sched;
  isl_union_map *copy_sched;
  isl_union_map *thread_sched;
  isl_union_map *full_sched;
};
#endif
