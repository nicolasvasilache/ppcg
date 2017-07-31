#pragma once


extern "C" {

#include "ppcg/cuda.h"
#include "ppcg/cuda_common.h"
#include "ppcg/gpu.h"
#include "ppcg/gpu_group.h"
#include "ppcg/gpu_print.h"
#include "ppcg/gpu_tree.h"
#include "ppcg/ppcg.h"
#include "ppcg/ppcg_options.h"
#include "ppcg/util.h"


////////////////////////////////////////////////////////////////////////////////
// cuda.h
////////////////////////////////////////////////////////////////////////////////

// Finer granularity print where void* user is a struct cuda_info
struct gpu_prog;
struct gpu_types;
__isl_give isl_printer *print_cuda(__isl_take isl_printer *p,
                                   struct gpu_prog *prog,
                                   __isl_keep isl_ast_node *tree,
                                   struct gpu_types *types,
                                   void *user);

////////////////////////////////////////////////////////////////////////////////
// gpu.c
////////////////////////////////////////////////////////////////////////////////

/* Return the set of outer array elements accessed by
 * by the statement instances in "domain" in "prog".
 * The instances in "domain" are those that appear
 * in the domains of the access relations in "prog".
 */
__isl_give isl_union_set *accessed_by_domain(__isl_take isl_union_set *domain,
                                             struct gpu_prog *prog);

/* Mark "node" atomic, if it is a band node.
 * Do the same for all ancestors.
 * Return a pointer to "node" (in the updated schedule tree).
 */
__isl_give isl_schedule_node *atomic_ancestors(__isl_take isl_schedule_node *node);

/* Compute a tiling for all the array reference groups in "kernel".
 */
  void compute_group_tilings(struct ppcg_kernel *kernel);

/* Collect all write references that require synchronization.
 * "node" is assumed to point to the kernel node.
 * Each reference is represented by a universe set in a space
 *
 *	[S[i,j] -> R[]]
 *
 * with S[i,j] the statement instance space and R[] the array reference.
 *
 * This function should be called before block and thread filters are added.
 *
 * Synchronization is needed after a write if there is a subsequent read
 * within the same block that may not be performed by the same thread.
 * There should not be any dependences between different blocks,
 * so we start with the flow dependences within the same kernel invocation
 * and we subtract from these those dependences that are mapped
 * to the same iteration of the bands where synchronization is inserted.
 * We do not remove pairs of instances that are known to map to
 * the same thread across different iterations of the intermediate
 * bands because the read may be performed by a different thread
 * than the one that needs the value if shared memory is involved.
 *
 * We also consider all pairs of possible writes that access the same
 * memory location and that may be mapped to the same block but not
 * to the same iteration of the intermediate bands.
 * In theory, it would be possible for one thread to still be in
 * a previous iteration of a loop in these bands.
 * A write to global memory in this delayed thread could then overwrite
 * a write from another thread that has already moved on to
 * the next iteration.
 *
 * After computing the above writes paired off with reads or writes
 * that depend on them, we project onto the domain writes.
 * Sychronization is needed after writes to global memory
 * through these references.
 */
__isl_give isl_union_set *compute_sync_writes(
  struct ppcg_kernel *kernel, __isl_keep isl_schedule_node *node);

int create_kernel_vars(struct ppcg_kernel *kernel);

/* Extract the set of parameter values and outer schedule dimensions
 * for which any statement instance
 * in the kernel inserted at "node" needs to be executed.
 * Intersect the set of parameter values derived from the host schedule
 * relation with the context of "prog".
 */
__isl_give isl_set *extract_context(__isl_keep isl_schedule_node *node,
                                    struct gpu_prog *prog);

/* Compute the effective grid size as a list of the sizes in each dimension.
 *
 * The grid size specified by the user or set by default
 * in read_grid_sizes() and applied by the block filter,
 * may be too large for the given code in the sense that
 * it may contain blocks that don't need to execute anything.
 * We therefore don't return this grid size, but instead the
 * smallest grid size that ensures that all blocks that actually
 * execute code are included in the grid.
 *
 * We first extract a description of the grid, i.e., the possible values
 * of the block ids, from the domain elements in "domain" and
 * kernel->block_filter.
 * The block ids are parameters in kernel->block_filter.
 * We simply need to change them into set dimensions.
 *
 * Then, for each block dimension, we compute the maximal value of the block id
 * and add one.
 */
__isl_give isl_multi_pw_aff *extract_grid_size(
  struct ppcg_kernel *kernel, __isl_take isl_union_set *domain);

/* Group the domain elements into a single space, named kernelX,
 * with X the kernel sequence number "kernel_id".
 */
__isl_give isl_schedule_node *group_statements(
  __isl_take isl_schedule_node *node, int kernel_id);

/* Insert a context node at "node" introducing the block and thread
 * identifiers along with their bounds, which are stored in kernel->grid_size
 * and kernel->block_dim.
 * Note that the bounds on the block identifiers may implicitly impose
 * constraints on the parameters.  A guard needs to be inserted
 * in the schedule tree to ensure that those bounds hold at "node".
 * This guard is inserted in insert_guard.
 */
__isl_give isl_schedule_node *insert_context(
  struct ppcg_kernel *kernel, __isl_take isl_schedule_node *node);

/* Insert a guard that eliminates kernel launches where the kernel
 * obviously does not have any work to do.
 *
 * In particular, eliminate kernel launches where there are obviously
 * zero blocks.
 * Use the same block size constraints that are used to create the context
 * to ensure that all constraints implicit in the constructed context
 * are imposed by the guard.
 *
 * Additionally, add other constraints that are valid
 * for each executed instance ("context"), as long as this does not result
 * in a disjunction.
 */
__isl_give isl_schedule_node *insert_guard(
  __isl_take isl_schedule_node *node,
  __isl_keep isl_set *context,
  __isl_keep isl_multi_pw_aff *size,
  struct ppcg_scop *scop);

/* The sizes of the arrays on the host that have been computed by
 * extract_array_info may depend on the parameters.  Use the extra
 * constraints on the parameters that are valid at "host_domain"
 * to simplify these expressions and store the results in kernel->array.
 *
 * We only need these localized bounds for arrays that are accessed
 * by the current kernel.  If we have found at least one reference group
 * then the array is accessed by the kernel.
 *
 * The resulting sizes may be functions that are nowhere defined
 * in case the access function cannot possibly access anything inside
 * the kernel for some reason.  If so, they are replaced by the zero
 * function.  Since the access function cannot actually access anything,
 * there is no harm in printing the array sizes as zero.
 */
void localize_bounds(
  struct ppcg_kernel *kernel, __isl_keep isl_set *host_domain);

/* Mark all arrays of "kernel" that have an array reference group
 * that is not mapped to private or shared memory as
 * accessing the corresponding global device memory.
 */
void mark_global_arrays(struct ppcg_kernel *kernel);

/* Return the number of outer band members of the band node "node"
 * that are marked coincident.
 */
int n_outer_coincidence(__isl_keep isl_schedule_node *node);

/* Create the array of gpu_local_array_info structures "array"
 * inside "kernel".  The number of elements in this array is
 * the same as the number of arrays in "prog".
 * Initialize the "array" field of each local array to point
 * to the corresponding array in "prog".
 */
struct ppcg_kernel *ppcg_kernel_create_local_arrays(
  struct ppcg_kernel *kernel, struct gpu_prog *prog);

/* Wrapper around ppcg_kernel_free for use as a isl_id_set_free_user callback.
 */
void ppcg_kernel_free_wrap(void *user);

/* Extract user specified grid and block sizes from the gen->sizes
 * command line option after filling in some potentially useful defaults.
 * Store the extracted sizes in "kernel".
 * Add the effectively used sizes to gen->used_sizes.
 */
void read_grid_and_block_sizes(struct ppcg_kernel *kernel, struct gpu_gen *gen);

/* Scale a band node that may have been split by split_band.
 * "sizes" are the scaling factors for the original node.
 * "node" either points to the original band node, or the outer
 * of the two pieces after splitting.
 *
 * If the number of elements in "node" is smaller than the number of
 * elements in "sizes", then some splitting has occurred and we split
 * "sizes" in the same way.
 */
__isl_give isl_schedule_node *scale_band(
  __isl_take isl_schedule_node *node, __isl_take isl_multi_val *sizes);

/* Return constraints on the domain elements that equate a sequence of
 * parameters called "names", to the partial schedule
 * of "node" modulo the integers in "size".
 * The number of elements in the array "size" should be equal
 * to the number of elements in "names".
 * The number of members of the band node "node" should be smaller
 * than or equal to this number.  If it is smaller, then the first
 * elements of "names" are equated to zero.
 */
__isl_give isl_union_set *set_schedule_modulo(
  __isl_keep isl_schedule_node *node, __isl_keep isl_id_list *names,
  int *size);

/* Replace the partial schedule S of the band node "node" by
 *
 *	floor(S/f)
 *
 * or
 *
 *	f * floor(S/f)
 *
 * if scale_tile_loops is set, with f the integers in "factor".
 * The list that "factor" points to is assumed to contain at least
 * as many elements as the number of members in the band.
 */
__isl_give isl_schedule_node *snap_band_to_sizes(
  __isl_take isl_schedule_node *node,
  int *factor,
  struct ppcg_options *options);

/* If the band node "node" has more than "n" members, then split off
 * the first "n" of them.
 */
__isl_give isl_schedule_node *split_band(__isl_take isl_schedule_node *node, int n);

/* Tile "band" with tile size specified by "sizes".
 *
 * Since the tile loops will be mapped to block ids, we forcibly
 * turn off tile loop scaling.  We may want to enable tile loop scaling
 * at some later point, but then we would have to support the detection
 * of strides during the mapping to block ids.
 * Similarly, since the point loops will be mapped to thread ids,
 * we forcibly shift the point loops so that they start at zero.
 */
isl_schedule_node *tile_band(
  __isl_take isl_schedule_node *node, __isl_take isl_multi_val *sizes);


////////////////////////////////////////////////////////////////////////////////
// gpu_group.c
////////////////////////////////////////////////////////////////////////////////
/* Group references of all arrays in "kernel".
 * "node" points to the kernel mark.
 * The mapping to shared memory in computed at the "shared" mark.
 *
 * We first extract all required schedule information into
 * a gpu_group_data structure and then consider each array
 * in turn.
 */
int gpu_group_references_with_traversal(
  struct ppcg_kernel *kernel,
  __isl_keep isl_schedule_node *node,
  isl_schedule_node* (*move_down_to_shared)(isl_schedule_node *, isl_union_set *),
  isl_schedule_node* (*move_down_to_thread)(isl_schedule_node *, isl_union_set *));

int compute_group_bounds(struct ppcg_kernel *kernel,
  struct gpu_array_ref_group *group, struct gpu_group_data *data);

int accesses_overlap(struct gpu_array_ref_group *group1,
  struct gpu_array_ref_group *group2);

int depth_accesses_overlap(struct gpu_array_ref_group *group1,
  struct gpu_array_ref_group *group2);

void check_can_be_private_live_ranges(struct ppcg_kernel *kernel,
  __isl_keep isl_schedule_node *node);

struct gpu_array_ref_group *join_groups_and_free(
  struct gpu_array_ref_group *group1,
  struct gpu_array_ref_group *group2);

struct gpu_array_ref_group *join_groups(
  struct gpu_array_ref_group *group1,
  struct gpu_array_ref_group *group2);

int join_all_groups(int n, struct gpu_array_ref_group **groups);

int smaller_tile(struct gpu_array_tile *tile,
  struct gpu_array_tile *tile1, struct gpu_array_tile *tile2);


}
