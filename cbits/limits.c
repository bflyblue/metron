/* The runtime's maximum heap, set while the program runs (design §8.1).
 * The collector reads RtsFlags.GcFlags.maxHeapSize at every collection, so
 * a new value takes effect at the next one; zero is no limit. */
#include "Rts.h"

void metron_set_max_heap(StgWord64 bytes)
{
    StgWord64 blocks = bytes / BLOCK_SIZE;
    RtsFlags.GcFlags.maxHeapSize = blocks > 0xffffffffu ? 0xffffffffu : (uint32_t)blocks;
}
